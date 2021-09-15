/* Malloc implementation for multiple threads without lock contention.
   Copyright (C) 2001,2002,2003,2004,2005,2006,2007
   Free Software Foundation, Inc.
   This file is part of the GNU C Library.
   Contributed by Wolfram Gloger <wg@malloc.de>, 2001.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public License as
   published by the Free Software Foundation; either version 2.1 of the
   License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; see the file COPYING.LIB.  If not,
   write to the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

#include <stdbool.h>

/* Compile-time constants.  */
// 定义了堆的最大值和最小值，宏定义时的括号别忘了
// 最小值固定，为32B
// 最大值不固定，默认为2倍的mmap分配阈值或者1M

#define HEAP_MIN_SIZE (32*1024)
#ifndef HEAP_MAX_SIZE
# ifdef DEFAULT_MMAP_THRESHOLD_MAX
#  define HEAP_MAX_SIZE (2 * DEFAULT_MMAP_THRESHOLD_MAX)
# else
#  define HEAP_MAX_SIZE (1024*1024) /* must be a power of two */
# endif
#endif

/* HEAP_MIN_SIZE and HEAP_MAX_SIZE limit the size of mmap()ed heaps
   that are dynamically created for multi-threaded programs.  The
   maximum size must be a power of two, for fast determination of
   which heap belongs to a chunk.  It should be much larger than the
   mmap threshold, so that requests with a size just below that
   threshold can be fulfilled without creating too many heaps.  */

// 多线程环境下，是否开启对锁的争用的数据的统计
// 不开对功能也无任何影响，因此线程统计数据不是重点
#ifndef THREAD_STATS
#define THREAD_STATS 0
#endif

/* If THREAD_STATS is non-zero, some statistics on mutex locking are
   computed.  */

/***************************************************************************/
// 宏定义时，参数也单独用括号括起来
// 获得arena对应的top chunk

#define top(ar_ptr) ((ar_ptr)->top)

/* A heap is a single contiguous memory region holding (coalesceable，可合并的)
   malloc_chunks.  It is allocated with mmap() and always starts at an
   address aligned to HEAP_MAX_SIZE.  Not used unless compiling with
   USE_ARENAS. */

// 上面注释里说heap是连续的，这没问题，heap一定是通过mmap()分配的，一定是连续的，heap之间不一定连续
// heap支持,必须开启USE_ARENAS

// main_thread使用的main_arena不含heap
// 某次分配，我们分配了HEAP_MAX_SIZE内存，然后只有x字节给用户使用，
// 剩余的HEAP_MAX_SIZE - x字节应该处于protect状态，不能被用户读写
// 这里写的其实不太规范，即然统一用了INTERNEL_SIZE_T，就不应该用size_t

// 注意到这里，堆总是开始于HEAP_MAX_SIZE，堆的大小不必是HEAP_MAX_SIZE, 但是一定要开始与HEAP_MAX_SIZE

typedef struct _heap_info {
    mstate ar_ptr; /* Arena for this heap. */
    struct _heap_info *prev; /* Previous heap. */

    // 注意：没有任何一个字段存储heap_info的总大小，因为这是固定的，就是HEAP_MAX_SIZE,那就不需要费劲存储了
    // size 小于等于 mprotect_size 小于 HEAP_MAX_SIZE
    size_t size;   /* Current size in bytes. 现在使用的 */
    size_t mprotect_size;    /* Size in bytes that has been mprotected
			   PROT_READ|PROT_WRITE.  即为可用的，*/
    /* Make sure the following data is properly aligned, particularly
       that sizeof (heap_info) + 2 * SIZE_SZ is a multiple of
       MALLOC_ALIGNMENT. */

    // ？？？？？？/
    char pad[-6 * SIZE_SZ & MALLOC_ALIGN_MASK];
} heap_info;

/* Get a compile-time error if the heap_info padding is not correct
   to make alignment work as expected in sYSMALLOc.  */

// 暂时不做了解
extern int sanity_check_heap_info_alignment[(sizeof(heap_info)
                                             + 2 * SIZE_SZ) % MALLOC_ALIGNMENT
                                            ? -1 : 1];

/* Thread specific data */
// list: arena1  ->   arena2   --> arena3
// list_lock锁住这个list，arena_key锁住每一个arena1/2/3

static tsd_key_t arena_key;
static mutex_t list_lock;

#if THREAD_STATS
static int stat_n_heaps;
#define THREAD_STAT(x) x
#else
#define THREAD_STAT(x) do ; while(0)
#endif

/* Mapped memory in non-main arenas (reliable only for NO_THREADS). */
static unsigned long arena_mem;

/* Already initialized? */
int __malloc_initialized = -1;

/**************************************************************************/

#if USE_ARENAS

/* arena_get() acquires an arena and locks the corresponding mutex.
   First, try the one last locked successfully by this thread.  (This
   is the common case and handled with a macro for speed.)  Then, loop
   once over the circularly linked list of arenas.  If no arena is
   readily available, create a new one.  In this latter case, `size'
   is just a hint as to how much memory will be required immediately
   in the new arena. */

// 函数功能：获得一个可用的arena
// 首先取出线程特定数据，其实就是线程关联的arena，其实就是上次被这个线程上锁成功的arena
// 当这个arena确实存在时，且尝试加锁成功，我们更新一下状态，使用当前的arena，然后返回即可
// 否则即为与这个线程关联的arena根本不存在，或者当前被占用呢，那么我们就去寻找一个新的arena，
// 于是我们去arena_get2寻求帮助

#define arena_get(ptr, size) do { \
  Void_t *vptr = NULL; \
  ptr = (mstate)tsd_getspecific(arena_key, vptr); \
  if(ptr && !mutex_trylock(&ptr->mutex)) { \
    THREAD_STAT(++(ptr->stat_lock_direct)); \
  } else \
    ptr = arena_get2(ptr, (size)); \
} while(0)

/* find the heap and corresponding arena for a given ptr */
// & ～（x - 1） 实际操作就是 找到最接近x整数倍的地址
// 对于给定的地址：ptr，我们执行如下操作 得到其对应的heap
// 别忘了heap总是按照HEAP_MAX_SIZE大小去分配,且总是开始于HEAP_MAX_SIZE
// e.g : 地址0x17(十进制的23) == 0001 0111
//      假设HEAP_MAX_SIZE = 0x8 == 0001 0000
// 下面结果为 0x0001 0000,为0x10(十进制的16)

#define heap_for_ptr(ptr) \
 ((heap_info *)((unsigned long)(ptr) & ~(HEAP_MAX_SIZE-1)))

 // 注意到chunk若处于主分配区，则直接返回主分配区，而不能进行heap_for_ptr操作，
 // 因为主分配区没有heap_info结构
#define arena_for_chunk(ptr) \
 (chunk_non_main_arena(ptr) ? heap_for_ptr(ptr)->ar_ptr : &main_arena)

#else /* !USE_ARENAS */

/* There is only one arena, main_arena. */
// 这里是假设多线程环境下仅一个arena
#if THREAD_STATS
#define arena_get(ar_ptr, sz) do { \
  ar_ptr = &main_arena; \
  if(!mutex_trylock(&ar_ptr->mutex)) \
    ++(ar_ptr->stat_lock_direct); \
  else { \
    (void)mutex_lock(&ar_ptr->mutex); \
    ++(ar_ptr->stat_lock_wait); \
  } \
} while(0)
#else
#define arena_get(ar_ptr, sz) do { \
  ar_ptr = &main_arena; \
  (void)mutex_lock(&ar_ptr->mutex); \
} while(0)
#endif
#define arena_for_chunk(ptr) (&main_arena)

#endif /* USE_ARENAS */

/**************************************************************************/

#ifndef NO_THREADS

/* atfork support.  */

static __malloc_ptr_t (*save_malloc_hook)(size_t __size,
                                          __const __malloc_ptr_t);

# if !defined _LIBC || (defined SHARED && !USE___THREAD)

static __malloc_ptr_t (*save_memalign_hook)(size_t __align, size_t __size,
                                            __const __malloc_ptr_t);

# endif

static void (*save_free_hook)(__malloc_ptr_t __ptr,
                              __const __malloc_ptr_t);
// fork时用来保存arena
static Void_t *save_arena;

// 小巧精悍的不知道干嘛的代码
#ifdef ATFORK_MEM
ATFORK_MEM;
#endif

/* Magic value for the thread-specific arena pointer when
   malloc_atfork() is in use.  */
// 当fork时，会把AtFORK_ARENA_PTR 放入arena，任何其他用户从tsd中得到的都会是这个宏
#define ATFORK_ARENA_PTR ((Void_t*)-1)

/* The following hooks are used while the `atfork' handling mechanism
   is active. */

// 一个进程含有多个线程，一个线程执行fork时，另一个线程可能恰巧在执行malloc，或者执行fork的线程也要分配内存
// 我们通过ATFORK_ARENA_PTR宏来区分

/*
 * 我们待定再看，现在分配的话，不检查内存，直接分配即可，即
 * 如果是执行fork的线程也执行malloc，那么不做检查，直接分配
 * 否则是普通线程分配，那等fork完后，直接malloc
 */

static Void_t *
malloc_atfork(size_t sz, const Void_t *caller) {
    Void_t *vptr = NULL;
    Void_t *victim;
    // 获得当前线程对应的分配区
    // 这一个arena_key 是哪一个arena的？？？？是不是main_arena？？？？
    tsd_getspecific(arena_key, vptr);

    // 获取分配区不一定成功，所以vptr有两种选择，一种是代表不成功的ATFORK_ARENA_PTR
    // 另一种则为成功
    /*
            当父进程中的某个线程使用 fork 的机制创建子线程时，如果进程中的线程需要分配内
        存，将使用 malloc_atfork()函数分配内存。malloc_atfork()函数首先查看自己的线程私有实例
        中的分配区指针，如果该指针为 ATFORK_ARENA_PTR，意味着本线程正在 fork 新线程，并锁
        住了全局锁 list_lock 和每个分配区，当前只有本线程可以分配内存，如果在 fork 线程前的分
        配函数不是处于 check 模式，直接调用内部分配函数_int_malloc()。否则在分配内存的同时
        做检查。如果线程私有实例中的指针不是 ATFORK_ARENA_PTR，意味着当前线程只是常规线
        程，有另外的线程在 fork 子线程，当前线程只能等待 fork 子线程的线程完成分配，于是等
        待获得全局锁 list_lock，如果获得全局锁成功，表示 fork 子线程的线程已经完成 fork 操作，
        当前线程可以分配内存了，于是是释放全局锁 list_lock，并调用 public_mALLOc()分配内存。

        fork时，所有的锁我们都会得到，也就是我们可在所有的分配区分配内存，随便选，
        我们选择的是在main_arena分配

     */

    // 为什么普通线程调用public_malloc而调用fork的线程是调用_int_malloc
    if (vptr == ATFORK_ARENA_PTR) {// 本线程正在fork，那么分配内存即可，分配内存调用_int_malloc
        /* We are the only thread that may allocate at all.  */
        if (save_malloc_hook != malloc_check) {// malloc_check 在hooks.c里
            return _int_malloc(&main_arena, sz);
        } else {// 以下其实就是分解版的malloc_check，我们去学malloc_check
            if (top_check() < 0) //
                return 0;
            victim = _int_malloc(&main_arena, sz + 1);
            return mem2mem_check(victim, sz);
        }
    } else {// 这是一个普通线程正在fork, 我们阻塞在锁 这里即可
        /* Suspend the thread until the `atfork' handlers have completed.
           By that time, the hooks will have been reset as well, so that
           mALLOc() can be used again. */

        // 这里必须是等待在list_lock，参考我们的文档
        (void) mutex_lock(&list_lock);
        (void) mutex_unlock(&list_lock);
        return public_mALLOc(sz);
    }
}

static void
free_atfork(Void_t *mem, const Void_t *caller) {
    Void_t *vptr = NULL;
    mstate ar_ptr;
    mchunkptr p;                          /* chunk corresponding to mem */

    if (mem == 0)                              /* free(0) has no effect */
        return;

        // 找到待释放内存对应的chunk
    p = mem2chunk(mem);         /* do not bother to replicate free_check here */

#if HAVE_MMAP
    if (chunk_is_mmapped(p))                       /* release mmapped memory. */
    {
      munmap_chunk(p);
      return;
    }
#endif
    // 获得chunk对应的arena
    // #define arena_for_chunk(ptr) \
    //   (chunk_non_main_arena(ptr) ? heap_for_ptr(ptr)->ar_ptr : &main_arena)
    ar_ptr = arena_for_chunk(p);
    tsd_getspecific(arena_key, vptr);

    // 如果是普通线程，那么我们等待在该线程对应的arena的锁这里，注意，这里不需要等待在list lock锁
    // 如果是正在执行fork的线程，那直接free即可
    if (vptr != ATFORK_ARENA_PTR)
        (void) mutex_lock(&ar_ptr->mutex);
    _int_free(ar_ptr, mem);
    if (vptr != ATFORK_ARENA_PTR)
        (void) mutex_unlock(&ar_ptr->mutex);
}


/* Counter for number of times the list is locked by the same thread.  */
static unsigned int atfork_recursive_cntr;

/* The following two functions are registered via thread_atfork() to
   make sure that the mutexes remain in a consistent state in the
   fork()ed version of a thread.  Also adapt the malloc and free hooks
   temporarily, because the `atfork' handler mechanism may use
   malloc/free internally (e.g. in LinuxThreads). */

static void
ptmalloc_lock_all(void) {
    mstate ar_ptr;

    // ptmalloc根本就没有初始化过，即根本就没有使用过，那就不用上锁了
    if (__malloc_initialized < 1)
        return;
    if (mutex_trylock(&list_lock)) {
        Void_t *my_arena;// 这里其实是上面的vptr，作用是完全相同的，这里命名不好
        tsd_getspecific(arena_key, my_arena);

        // 这里避免了自身的递归加锁，可以看出是用一个静态变量来标识的
        if (my_arena == ATFORK_ARENA_PTR)
            /* This is the same thread which already locks the global list.
               Just bump the counter.  */
            goto out;

        /* This thread has to wait its turn.  */
        (void) mutex_lock(&list_lock);
    }
    // 获取每一个arena的锁
    for (ar_ptr = &main_arena;;) {
        (void) mutex_lock(&ar_ptr->mutex);
        ar_ptr = ar_ptr->next;
        if (ar_ptr == &main_arena) break;
    }

    // 以上加锁完毕了，接下来我们更换hook函数即可
    // 必须加锁完毕后再更换hook函数，防止先更换hook，
    // 然后有线程不处于fork状态，正常分配内存时，会调用了malloc_atfork

    /*
     * fork时调用malloc，肯定不能调用普通的malloc了，而是我们上面自定义的malloc_atfork
     * 注意到，public_mALLOc每次都会首先判断__malloc_hook是否是nullptr
     * 这个取值可以是_malloc_hook_ini，然后调用_int_malloc_
     *      也可以取nullptr
     * 不管以上取是什么，我们都以save_malloc_hook保存上，从而不影响我们正常malloc的使用
     * 然后把这个hook替换为我们的malloc_atfork
     * 此时不管以前是否被初始化，随后的每次调用malloc，都会调用malloc_atfork
     */

    save_malloc_hook = __malloc_hook;
    save_free_hook = __free_hook;
    __malloc_hook = malloc_atfork;
    __free_hook = free_atfork;

    /* Only the current thread may perform malloc/free calls now. */
    // 一定是第一次加锁，因为第二次及以后的加锁都会从上面的goto里跳转出去了，第一次加锁，要设置arena一下
    tsd_getspecific(arena_key, save_arena);
    tsd_setspecific(arena_key, ATFORK_ARENA_PTR);
    out:
    ++atfork_recursive_cntr;
}

static void
ptmalloc_unlock_all(void) {
    mstate ar_ptr;
    // 还未初始化，直接return
    if (__malloc_initialized < 1)
        return;

    // 本线程，解锁一次
    if (--atfork_recursive_cntr != 0)
        return;
    // 此时是最低一层的了，把arena放回线程特定数据
    tsd_setspecific(arena_key, save_arena);
    // 还原hook函数
    __malloc_hook = save_malloc_hook;
    __free_hook = save_free_hook;
    // 逐个解锁分配区
    for (ar_ptr = &main_arena;;) {
        (void) mutex_unlock(&ar_ptr->mutex);
        ar_ptr = ar_ptr->next;
        if (ar_ptr == &main_arena) break;
    }
    // 结束链表
    (void) mutex_unlock(&list_lock);
}

#ifdef __linux__

/* In NPTL, unlocking a mutex in the child process after a
   fork() is currently unsafe, whereas re-initializing it is safe and
   does not leak resources.  Therefore, a special atfork handler is
   installed for the child. */

// 特定平台的，我们暂时不看了

static void
ptmalloc_unlock_all2 (void)
{
  mstate ar_ptr;

  if(__malloc_initialized < 1)
    return;
#if defined _LIBC || defined MALLOC_HOOKS
  tsd_setspecific(arena_key, save_arena);
  __malloc_hook = save_malloc_hook;
  __free_hook = save_free_hook;
#endif
  for(ar_ptr = &main_arena;;) {
    mutex_init(&ar_ptr->mutex);
    ar_ptr = ar_ptr->next;
    if(ar_ptr == &main_arena) break;
  }
  mutex_init(&list_lock);
  atfork_recursive_cntr = 0;
}

#else

#define ptmalloc_unlock_all2 ptmalloc_unlock_all

#endif

#endif /* !defined NO_THREADS */

/* Initialization routine. */
#ifdef _LIBC
#include <string.h>
extern char **_environ;

// 如下函数未见被使用过，暂时不看
static char *
internal_function
next_env_entry (char ***position)
{
  char **current = *position;
  char *result = NULL;

  while (*current != NULL)
    {
      if (__builtin_expect ((*current)[0] == 'M', 0)
      && (*current)[1] == 'A'
      && (*current)[2] == 'L'
      && (*current)[3] == 'L'
      && (*current)[4] == 'O'
      && (*current)[5] == 'C'
      && (*current)[6] == '_')
    {
      result = &(*current)[7];

      /* Save current position for next visit.  */
      *position = ++current;

      break;
    }

      ++current;
    }

  return result;
}
#endif /* _LIBC */

/* Set up basic state so that _int_malloc et al can work.  */
static void
ptmalloc_init_minimal(void) {
#if DEFAULT_TOP_PAD != 0
    mp_.top_pad        = DEFAULT_TOP_PAD;
#endif
    mp_.n_mmaps_max = DEFAULT_MMAP_MAX;
    mp_.mmap_threshold = DEFAULT_MMAP_THRESHOLD;
    mp_.trim_threshold = DEFAULT_TRIM_THRESHOLD;
    mp_.pagesize = malloc_getpagesize;
}


#ifdef _LIBC
# ifdef SHARED
static void *
__failing_morecore (ptrdiff_t d)
{
  return (void *) MORECORE_FAILURE;
}

extern struct dl_open_hook *_dl_open_hook;
libc_hidden_proto (_dl_open_hook);
# endif

# if defined SHARED && !USE___THREAD
/* This is called by __pthread_initialize_minimal when it needs to use
   malloc to set up the TLS state.  We cannot do the full work of
   ptmalloc_init (below) until __pthread_initialize_minimal has finished,
   so it has to switch to using the special startup-time hooks while doing
   those allocations.  */
void
__libc_malloc_pthread_startup (bool first_time)
{
  if (first_time)
    {
      ptmalloc_init_minimal ();
      save_malloc_hook = __malloc_hook;
      save_memalign_hook = __memalign_hook;
      save_free_hook = __free_hook;
      __malloc_hook = malloc_starter;
      __memalign_hook = memalign_starter;
      __free_hook = free_starter;
    }
  else
    {
      __malloc_hook = save_malloc_hook;
      __memalign_hook = save_memalign_hook;
      __free_hook = save_free_hook;
    }
}
# endif
#endif

static void
ptmalloc_init(void) {
#if __STD_C
    const char* s;
#else
    char *s;
#endif
    int secure = 0;

    if (__malloc_initialized >= 0) // 已经被初始化过了，则可直接返回
        return;
    __malloc_initialized = 0; // 设置初始化标志

    /*
     * 以下不太确定，根据代码意思猜测如此
     * __LIBC == 标准c库
     * SHARED == 动态链接？
     *
     */

#ifdef _LIBC
# if defined SHARED && !USE___THREAD
    /* ptmalloc_init_minimal may already have been called via
       __libc_malloc_pthread_startup, above.  */
    if (mp_.pagesize == 0)
# endif
#endif
    ptmalloc_init_minimal();

    /*
     * 为多线程版本的 ptmalloc 的 pthread 初始化做准备，
     * 保存当前的 hooks 函数，
     * 并把 ptmalloc 为初始化时所有使用的分配 / 释放函数赋给 hooks 函数，
     * 因为在线程初始化一些私有实例时，ptmalloc 还没有初始化，所以需要做特殊处理。
     * 从这些 hooks 函数可以看出，在 ptmalloc 未初始化时，不能使用 remalloc 函数。
     * 在相关的 hooks 函数赋值以后，执行 pthread_initilaize() 初始化 pthread 。
     *
     * 以上涉及到一些线程相关的东西，我们还没有阅读过glibc里关于线程的章节，
     * 所以现在知道有这种东西即可
     *
     */

#ifndef NO_THREADS
# if defined _LIBC
    /* We know __pthread_initialize_minimal has already been called,
       and that is enough.  */
#   define NO_STARTER
# endif
# ifndef NO_STARTER
    /* With some threads implementations, creating thread-specific data
       or initializing a mutex may call malloc() itself.  Provide a
       simple starter version (realloc() won't work). */
    save_malloc_hook = __malloc_hook;
    save_memalign_hook = __memalign_hook;
    save_free_hook = __free_hook;
    __malloc_hook = malloc_starter;
    __memalign_hook = memalign_starter;
    __free_hook = free_starter;
#  ifdef _LIBC
    /* Initialize the pthreads interface. */
    if (__pthread_initialize != NULL)
      __pthread_initialize();
#  endif /* !defined _LIBC */
# endif    /* !defined NO_STARTER */
#endif /* !defined NO_THREADS */
    mutex_init(&main_arena.mutex);
    main_arena.next = &main_arena;

    /*
     * Ptmalloc需要保证只有主分配区才能使用 sbrk() 分配连续虚拟内存空间，
     * 如果有多个分配区使用 sbrk() 就不能获得连续的虚拟地址空间。

     * 大多数情况下 Glibc 库都是以动态链接库的形式加载的，处于默认命名空间，多个进程共用 Glibc 库，
     * Glibc 库代码段在内存中只有一份拷贝，数据段在每个用户进程都有一份拷贝。

     * 但如果 Glibc 库不在默认名字空间，
     * 或是用户程序是静态编译的并调用了 dlopen 函数加载 Glibc 库中的 ptamalloc_init() ，

     * 这种情况下的 ptmalloc 不允许使用 sbrk() 分配内存，
     * 只需修改 __morecore 函数指针指向 __failing_morecore 就可以禁止使用 sbrk() 了，
     * __morecore 默认指向 sbrk() 。

     */

#if defined _LIBC && defined SHARED
    /* In case this libc copy is in a non-default namespace, never use brk.
       Likewise if dlopened from statically linked program.  */
    Dl_info di;
    struct link_map *l;

    if (_dl_open_hook != NULL
        || (_dl_addr (ptmalloc_init, &di, &l, NULL) != 0
        && l->l_ns != LM_ID_BASE))
      __morecore = __failing_morecore;
#endif

    /*
     * 初始化全局锁 list_lock ，
     * list_lock 主要用于同步分配区的单向循环链表。
     * 然后创建线程私有实例 arena_key ，
     * 该私有实例保存的是分配区（ arena ）的 malloc_state 实例指针。
     * arena_key 指向的可能是主分配区的指针，也可能是非主分配区的指针，
     * 这里将调用 ptmalloc_init() 的线程的 arena_key 绑定到主分配区上。
     * 意味着本线程首选从主分配区分配内存。
     * 然后调用 thread_atfork() 设置当前进程在 fork 子线程（ linux 下线程是轻量级进程，使用类似 fork 进程的机制创建）时处理 mutex 的回调函数，
     * 在本进程 fork 子线程时，调用 ptmalloc_lock_all() 获得所有分配区的锁，
     * 禁止所有分配区分配内存，
     * 当子线程创建完毕，
     * 父进程调用 ptmalloc_unlock_all() 重新 unlock 每个分配区的锁 mutex ，
     * 子线程调用 ptmalloc_unlock_all2()
     * 重新初始化每个分配区的锁 mutex 。
     */

    mutex_init(&list_lock);
    tsd_key_create(&arena_key, NULL);
    // 这里可以看出，第一个调用ptmalloc_init()的线程会获得main_arena
    tsd_setspecific(arena_key, (Void_t * ) & main_arena);
    thread_atfork(ptmalloc_lock_all, ptmalloc_unlock_all, ptmalloc_unlock_all2);
#ifndef NO_THREADS
# ifndef NO_STARTER
    __malloc_hook = save_malloc_hook;
    __memalign_hook = save_memalign_hook;
    __free_hook = save_free_hook;
# else
#  undef NO_STARTER
# endif
#endif
#ifdef _LIBC
    secure = __libc_enable_secure;
    s = NULL;
    if (__builtin_expect (_environ != NULL, 1))
      {
        char **runp = _environ;
        char *envline;

        while (__builtin_expect ((envline = next_env_entry (&runp)) != NULL,
                     0))
      {
        size_t len = strcspn (envline, "=");

        if (envline[len] != '=')
          /* This is a "MALLOC_" variable at the end of the string
             without a '=' character.  Ignore it since otherwise we
             will access invalid memory below.  */
          continue;

        switch (len)
          {
          case 6:
            if (memcmp (envline, "CHECK_", 6) == 0)
          s = &envline[7];
            break;
          case 8:
            if (! secure)
          {
            if (memcmp (envline, "TOP_PAD_", 8) == 0)
              mALLOPt(M_TOP_PAD, atoi(&envline[9]));
            else if (memcmp (envline, "PERTURB_", 8) == 0)
              mALLOPt(M_PERTURB, atoi(&envline[9]));
          }
            break;
          case 9:
            if (! secure && memcmp (envline, "MMAP_MAX_", 9) == 0)
          mALLOPt(M_MMAP_MAX, atoi(&envline[10]));
            break;
          case 15:
            if (! secure)
          {
            if (memcmp (envline, "TRIM_THRESHOLD_", 15) == 0)
              mALLOPt(M_TRIM_THRESHOLD, atoi(&envline[16]));
            else if (memcmp (envline, "MMAP_THRESHOLD_", 15) == 0)
              mALLOPt(M_MMAP_THRESHOLD, atoi(&envline[16]));
          }
            break;
          default:
            break;
          }
      }
      }
#else
    if (!secure) {
        if ((s = getenv("MALLOC_TRIM_THRESHOLD_")))
            mALLOPt(M_TRIM_THRESHOLD, atoi(s));
        if ((s = getenv("MALLOC_TOP_PAD_")))
            mALLOPt(M_TOP_PAD, atoi(s));
        if ((s = getenv("MALLOC_PERTURB_")))
            mALLOPt(M_PERTURB, atoi(s));
        if ((s = getenv("MALLOC_MMAP_THRESHOLD_")))
            mALLOPt(M_MMAP_THRESHOLD, atoi(s));
        if ((s = getenv("MALLOC_MMAP_MAX_")))
            mALLOPt(M_MMAP_MAX, atoi(s));
    }
    s = getenv("MALLOC_CHECK_");
#endif
    if (s && s[0]) {
        mALLOPt(M_CHECK_ACTION, (int) (s[0] - '0'));
        if (check_action != 0)
            __malloc_check_init();
    }
    if (__malloc_initialize_hook != NULL)
        (*__malloc_initialize_hook)();
    __malloc_initialized = 1;
}

/* There are platforms (e.g. Hurd) with a link-time hook mechanism. */
#ifdef thread_atfork_static
thread_atfork_static(ptmalloc_lock_all, ptmalloc_unlock_all, \
                     ptmalloc_unlock_all2)
#endif



/* Managing heaps and arenas (for concurrent threads) */

#if USE_ARENAS

#if MALLOC_DEBUG > 1

/* Print the complete contents of a single heap to stderr. */
// debug使用的，暂时不看
static void
#if __STD_C
dump_heap(heap_info *heap)
#else
dump_heap(heap) heap_info *heap;
#endif
{
  char *ptr;
  mchunkptr p;

  fprintf(stderr, "Heap %p, size %10lx:\n", heap, (long)heap->size);
  ptr = (heap->ar_ptr != (mstate)(heap+1)) ?
    (char*)(heap + 1) : (char*)(heap + 1) + sizeof(struct malloc_state);
  p = (mchunkptr)(((unsigned long)ptr + MALLOC_ALIGN_MASK) &
                  ~MALLOC_ALIGN_MASK);
  for(;;) {
    fprintf(stderr, "chunk %p size %10lx", p, (long)p->size);
    if(p == top(heap->ar_ptr)) {
      fprintf(stderr, " (top)\n");
      break;
    } else if(p->size == (0|PREV_INUSE)) {
      fprintf(stderr, " (fence)\n");
      break;
    }
    fprintf(stderr, "\n");
    p = next_chunk(p);
  }
}

#endif /* MALLOC_DEBUG > 1 */

/* If consecutive mmap (0, HEAP_MAX_SIZE << 1, ...) calls return decreasing
   addresses as opposed to increasing, new_heap would badly fragment the
   address space.  In that case remember the second HEAP_MAX_SIZE part
   aligned to HEAP_MAX_SIZE from last mmap (0, HEAP_MAX_SIZE << 1, ...)
   call (if it is already aligned) and try to reuse it next time.  We need
   no locking for it, as kernel ensures the atomicity for us - worst case
   we'll call mmap (addr, HEAP_MAX_SIZE, ...) for some value of addr in
   multiple threads, but only one will succeed.  */
static char *aligned_heap_area;

/* Create a new heap.  size is automatically rounded up to a multiple
   of the page size. */

static heap_info *
internal_function
#if __STD_C
new_heap(size_t size, size_t top_pad)
#else
new_heap(size, top_pad) size_t size, top_pad;
#endif
{
  size_t page_mask = malloc_getpagesize - 1;
  char *p1, *p2;
  unsigned long ul;
  heap_info *h;


  /*
   * 堆最少分配HEAP_MIN_SIZE, 最多分配HEAP_MAX_SIZE
   * 能pad尽量pad，若因pad导致超出了MAX_SIZE, 那就不pad了
   * 最后别忘了页对齐
   */

    // heap不是每次都分配HEAP_MAX_SIZE吗？
  if(size+top_pad < HEAP_MIN_SIZE)
    size = HEAP_MIN_SIZE;
  else if(size+top_pad <= HEAP_MAX_SIZE)
    size += top_pad;
  else if(size > HEAP_MAX_SIZE)
    return 0;
  else
    size = HEAP_MAX_SIZE;
  size = (size + page_mask) & ~page_mask;

  /* A memory region aligned to a multiple of HEAP_MAX_SIZE is needed.
     No swap space needs to be reserved for the following large
     mapping (on Linux, this is the case for all non-writable mappings
     anyway). */

  // 全局变量 aligned_heap_area 是上一次调用 mmap 分配内存的结束虚拟地址，并已经按照HEAP_MAX_SIZE 大小对齐。
  /*
        由于全局变量 aligned_heap_area 没有锁保护，可能存在多个线程
        同时 mmap()函数从 aligned_heap_area 开始映射新的虚拟内存块，操作系统
        会保证只会有一个线程会成功，其它在同一地址映射新虚拟内存块都会失败。无论映射是否
        成功，都将全局变量 aligned_heap_area 设置为 NULL。如果映射成功，但返回的虚拟地址不
        是按 HEAP_MAX_SIZE 大小对齐的，取消该区域的映射，映射失败。

MAP_NORESERVE
      Do not reserve swap space for this mapping.  When swap space is reserved, one has the guarantee that  it
      is  possible  to modify the mapping.  When swap space is not reserved one might get SIGSEGV upon a write
      if no physical memory is available.  See also the discussion of the file  /proc/sys/vm/overcommit_memory
      in proc(5).  In kernels before 2.6, this flag had effect only for private writable mappings.

   */

  p2 = MAP_FAILED;
  if(aligned_heap_area) {
    p2 = (char *)MMAP(aligned_heap_area, HEAP_MAX_SIZE, PROT_NONE,
              MAP_PRIVATE|MAP_NORESERVE);
    aligned_heap_area = NULL;

    // 前面说过，heap的起始地址必须位于HEAP_MAX_SIZE的倍数处，不允许不对齐
    // 虽然分配成功，但是未按照HEAP_MAX_SIZE对齐,那么我们munmap
    // 如果分配都没成功，是不需要unmap的
    if (p2 != MAP_FAILED && ((unsigned long)p2 & (HEAP_MAX_SIZE-1))) { // 未对齐
      munmap(p2, HEAP_MAX_SIZE);
      p2 = MAP_FAILED; // 即使分配得到的内存，但是如果是未对齐的内存，依旧按照分配失败来处理
    }
  }

  /*
        全局变量 aligned_heap_area 为 NULL，或者从 aligned_heap_area 开始映射失败了，尝试
        映射 2 倍 HEAP_MAX_SIZE 大小的虚拟内存，便于地址对齐，因为在最坏可能情况下，需要
        映射 2 倍 HEAP_MAX_SIZE 大小的虚拟内存才能实现地址按照 HEAP_MAX_SIZE 大小对齐。

        解释为什么最坏情况下，映射两倍的HEAP_MAX_SIZE可以便于实现地址对齐
        开始与HEAP_MAX_SIZE,然后还要预留HEAP_MAX_SIZE,当然是2 * HEAP_MAX_SIZE
   */

  /*
   * 首先尝试按照上次的end继续分配内存，期望得到尽可能连续的地址，如下示意图，假如分配失败，
     --------｜-------------------｜
            end  HEAP_MAX_SIZE

     有可能是从end开始，找不到连续的HEAP_MAX_SIZE的大小，但是从其他位置是可以找到的，我们尝试这种case，
     为了减少分配的次数，我们一次分配一个较大的值，然后从其中找到按照HEAP_MAX_SIZE的倍数的起始的地址

        -----｜----------｜------------------------｜
             end    some pos      2 * HEAP_MAX_SIZE

      记p1为mmap得来的起始地址，p2为对齐地址,
      我们要将p2左侧和p2 + HEAP_MAX_SIZE右侧的内存归还操作系统
      其中注意特殊case，p2 == p1，另外p2 不可能等于p1 + HEAP_MAX_SIZE
      因为若对齐地址是在p1 + HEAP_MAX_SIZE，因为按HEAP_MAX_SIZE对齐，所以p1一定也是对齐处
      所以只会选p1
      则p2+MAX_SIZE右侧必有内存需要归还给os

   */


  if(p2 == MAP_FAILED) {
    p1 = (char *)MMAP(0, HEAP_MAX_SIZE<<1, PROT_NONE,
              MAP_PRIVATE|MAP_NORESERVE);
    /*
        映射 2 倍 HEAP_MAX_SIZE 大小的虚拟内存成功，将大于等于 p1 并按 HEAP_MAX_SIZE
        大小对齐的第一个虚拟地址赋值给 p2，p2 作为 sub_heap 的起始虚拟地址，p2+
        HEAP_MAX_SIZE 作为 sub_heap 的结束地址，并将 sub_heap 的结束地址赋值给全局变量
        aligned_heap_area，最后还需要将多余的虚拟内存还回给操作系统。
     */

    if(p1 != MAP_FAILED) {
        // 起始与对齐地址
      p2 = (char *)(((unsigned long)p1 + (HEAP_MAX_SIZE-1))
            & ~(HEAP_MAX_SIZE-1));
      ul = p2 - p1;
      if (ul) // p2 == p1
        munmap(p1, ul);
      else
        aligned_heap_area = p2 + HEAP_MAX_SIZE;
      // 总共2 * MAX_SIZE, p2左侧ul,p2用了MAX_SIZE， 右侧剩余2 * MAX_SIZE - MAX_SIZE - ul == MAX - ul
      // 右侧必有内存归还给os，不需要任何的判断
      munmap(p2 + HEAP_MAX_SIZE, HEAP_MAX_SIZE - ul);
    } else {
      /* Try to take the chance that an allocation of only HEAP_MAX_SIZE
     is already aligned. */

      /*
            映射 2 倍 HEAP_MAX_SIZE 大小的虚拟内存失败了，
            赌一把，
            再尝试映射 HEAP_MAX_SIZE 大小的虚拟内存，
            如果失败，返回吧；
            如果成功，但该虚拟地址不是按照 HEAP_MAX_SIZE 大小对齐的，返回。
       */

      p2 = (char *)MMAP(0, HEAP_MAX_SIZE, PROT_NONE, MAP_PRIVATE|MAP_NORESERVE);
      if(p2 == MAP_FAILED)
        return 0;
      if((unsigned long)p2 & (HEAP_MAX_SIZE-1)) { // 未对齐
        munmap(p2, HEAP_MAX_SIZE);
        return 0;
      }
    }
  }

  // 执行到这里，已经分配了HEAP_MAX_SIZE大小且按HEAP_MAX_SIZE对齐的了，且end也已经设置好了
  /*
        调用 mprotect()函数将 size 大小的内存设置为可读可写，
        如果失败，解除整个 sub_heap的映射。
   */

  if(mprotect(p2, size, PROT_READ|PROT_WRITE) != 0) {
    munmap(p2, HEAP_MAX_SIZE);
    return 0;
  }

  // 最后更新 heap_info 实例中的相关字段。
  h = (heap_info *)p2;
  h->size = size;
  h->mprotect_size = size;
  THREAD_STAT(stat_n_heaps++);
  return h;
}

/* Grow a heap.  size is automatically rounded up to a
   multiple of the page size. */

static int
#if __STD_C
grow_heap(heap_info *h, long diff)
#else
grow_heap(h, diff) heap_info *h; long diff;
#endif
{
  size_t page_mask = malloc_getpagesize - 1;
  long new_size;

  /*
        本函数可不是将堆分配的HEAP_MAX_SIZE再继续分配，而是在HEAP_MAX_SIZE内，分配新的未使用的内存给用户
        首先将要增加的可读可写的内存大小按照页对齐，
        然后计算 sub_heap 总的可读可写的内存大小 new_size，
        判断 new_size 是否大于HEAP_MAX_SIZE，如果是，返回，
        否则判断 new_size 是否大于当前 sub_heap 的可读可写区域大小，
        如果否，调用 mprotect()设置新增的区域可读可写，
        并更新当前 sub_heap 的可读可写区域的大小为 new_size。
        最后将当前 sub_heap 的字段 size 更新为 new_size。
   */

  diff = (diff + page_mask) & ~page_mask;
  new_size = (long)h->size + diff;
  // 一个堆最大就这么大，不可能再分配了
  if((unsigned long) new_size > (unsigned long) HEAP_MAX_SIZE)
    return -1;
  // 将需要新分配的protect size，分配来
  if((unsigned long) new_size > h->mprotect_size) {
    if (mprotect((char *)h + h->mprotect_size,
         (unsigned long) new_size - h->mprotect_size,
         PROT_READ|PROT_WRITE) != 0)
      return -2;
    h->mprotect_size = new_size;
  }
  // 此时一定有足够的protect size了，直接更改该堆现在的size即可
  h->size = new_size;
  return 0;
}

/* Shrink a heap.  */

/*
    Shrink_heap()函数的参数 diff 已经页对齐，同时 sub_heap 的 size 也是按照页对齐的，所
    以计算 sub_heap 的 new_size 时不用再处理页对齐。
    如果该函数运行在非 Glibc 中，则从 sub_heap 中切割出 diff 大小的虚拟内存，
    创建一个新的不可读写的映射区域，注意 mmap()函数这里使用了 MAP_FIXED 标志，然后更
    新 sub_heap 的可读可写内存大小。如果该函数运行在 Glibc 库中，则调用 madvise()函数，
    实际上 madvise()函数什么也不做，只是返回错误，这里并没有处理 madvise()函数的返回值。
    MMAP_FIXED:
        Don't  interpret  addr  as  a  hint:  place  the mapping at exactly that address.
 */

static int
#if __STD_C
shrink_heap(heap_info *h, long diff)
#else
shrink_heap(h, diff) heap_info *h; long diff;
#endif
{
  long new_size; // shrink后的剩余内存

  new_size = (long)h->size - diff;
  if(new_size < (long)sizeof(*h)) // 如果剩余内存都装不下一个heap_info了，这是不允许的
    return -1;
  /* Try to re-map the extra heap space freshly to save memory, and
     make it inaccessible. */
#ifdef _LIBC
  if (__builtin_expect (__libc_enable_secure, 0))
#else
  if (1)
#endif
    {
      if((char *)MMAP((char *)h + new_size, diff, PROT_NONE,
              MAP_PRIVATE|MAP_FIXED) == (char *) MAP_FAILED)
            return -2;
      h->mprotect_size = new_size;
    }
#ifdef _LIBC
  else
    madvise ((char *)h + new_size, diff, MADV_DONTNEED);
#endif
  /*fprintf(stderr, "shrink %p %08lx\n", h, new_size);*/

  h->size = new_size;
  return 0;
}

/* Delete a heap. */
/*
    delete_heap()宏函数首先判断当前删除的 sub_heap 的结束地址是否与全局变量
    aligned_heap_area 指向的地址相同，如果相同，则将全局变量 aligned_heap_area 设置为 NULL，
    因为当前 sub_heap 删除以后，就可以从当前 sub_heap 的起始地址或是更低的地址开始映射
    新的 sub_heap，这样可以尽量从地地址映射内存。然后调用 munmap()函数将整个 sub_heap
    的虚拟内存区域释放掉。在调用 munmap()函数时，heap_trim()函数调用 shrink_heap()函数
    可能已将 sub_heap 切分成多个子区域，munmap()函数的第二个参数为 HEAP_MAX_SIZE，无
    论该 sub_heap（大小为 HEAP_MAX_SIZE）的内存区域被切分成多少个子区域，将整个
    sub_heap 都释放掉了。
 */

#define delete_heap(heap) \
  do {								\
    if ((char *)(heap) + HEAP_MAX_SIZE == aligned_heap_area)	\
      aligned_heap_area = NULL;					\
    munmap((char*)(heap), HEAP_MAX_SIZE);			\
  } while (0)

static int
internal_function
#if __STD_C
heap_trim(heap_info *heap, size_t pad)
#else
heap_trim(heap, pad) heap_info *heap; size_t pad;
#endif
{
  mstate ar_ptr = heap->ar_ptr;
  unsigned long pagesz = mp_.pagesize;
  // 注意这里的top_chunk，初始是ar_ptr->top_chunk
  mchunkptr top_chunk = top(ar_ptr), p, bck, fwd;
  heap_info *prev_heap;
  long new_size, top_size, extra;

  /* Can this heap go away completely? */
  /*

        当前heap能否被delete掉，要考虑删除掉当前heap后，prev_heap是否可以很好的完成后续分配任务，
        否则删除掉当前heap后，prev heap不能满足下一次分配，我们很快的又要mmap回来当前heap，
        这实际上是不好的。

        每个非主分配区至少有一个 sub_heap，每个非主分配区的第一个 sub_heap 中包含了一
        个 heap_info 的实例和 malloc_state 的实例，非主分配区中的其它 sub_heap 中只有一个
        heap_info 实例，紧跟 heap_info 实例后，为可以用于分配的内存块。当当前非主分配区的 top
        chunk 与当前 sub_heap 的 heap_info 实例的结束地址相同时，意味着当前 sub_heap 中只有
        一个空闲 chunk，没有已分配的 chunk。所以可以将当前整个 sub_heap 都释放掉。
   */
  while(top_chunk == chunk_at_offset(heap, sizeof(*heap))) {// 当前heap完全空闲
    // 先判断prev_heap
    prev_heap = heap->prev;

    /*
        每个 sub_heap 的可读可写区域的末尾都有两个 chunk 用于 fencepost，以 64 位系统为
        例，最后一个 chunk 占用的空间为 MINSIZE-2*SIZE_SZ，为 16B，最后一个 chuk 的 size 字段
        记录的前一个 chunk 为 inuse 状态，并标识当前 chunk 大小为 0，倒数第二个 chunk 为 inuse
        状态，这个 chunk 也是 fencepost 的一部分，这个 chunk 的大小为 2*SIZE_SZ，为 16B，所以
        用于 fencepost 的两个 chunk 的空间大小为 32B。fencepost 也有可能大于 32B，第二个 chunk
        仍然为16B，第一个chunk的大小大于16B，这种情况发生在top chunk的空间小于2*MINSIZE，
        大于MINSIZE，但对于一个完全空闲的sub_heap来说，top chunk的空间肯定大于2*MINSIZE，
        所以在这里不考虑这种情况。用于fencepost的chunk空间其实都是被分配给应用层使用的，
        new_size 表示当前 sub_heap 中可读可写区域的可用空间，如果倒数第二个 chunk 的前一个
        chunk 为空闲状态，当前 sub_heap 中可读可写区域的可用空间大小还需要加上这个空闲
        chunk 的大小。如果 new_size 与 sub_heap 中剩余的不可读写的区域大小之和小于 32+4K（64
        位系统），意味着前一个 sub_heap 的可用空间太少了，不能释放当前的 sub_heap。

        fencepost 是在用户分配的size里的，而不一定是整个HEAP_MAX_SIZE的最高位置
     */
    // 获得较高位置的fencepost的chunk
    p = chunk_at_offset(prev_heap, prev_heap->size - (MINSIZE-2*SIZE_SZ));
    assert(p->size == (0|PREV_INUSE)); /* must be fencepost */

    // 获得较低位置的fencepost的chunk，我们无法一步到位的获得这个chunk，因为不确定它的size
    p = prev_chunk(p);

    // 这是fencepost的size
    new_size = chunksize(p) + (MINSIZE-2*SIZE_SZ);
    assert(new_size>0 && new_size<(long)(2*MINSIZE));

    // 前面一个空闲的话，就把这个也用起来，
    if(!prev_inuse(p))
      new_size += p->prev_size;
    assert(new_size>0 && new_size<HEAP_MAX_SIZE); // 前面也空闲的不能大于HEAP_MAX_SIZE

    // 已经使用的空间里的空闲的 == new_size
    // HEAP_MAX_SIZE - prev_heap->size == 可读可写的空间里未使用的空间 + 不可读不可写的空间
    if(new_size + (HEAP_MAX_SIZE - prev_heap->size) < pad + MINSIZE + pagesz)
      break;// 那就别再处理了

      /*
            首先更新非主分配区的内存统计，然后调用 delete_heap()宏函数释放该 sub_heap，把
            当前 heap 设置为被释放 sub_heap 的前一个 sub_heap，p 指向的是被释放 sub_heap 的前一
            个 sub_heap 的倒数第二个 chunk，如果 p 的前一个 chunk 为空闲状态，由于不可能出现多
            个连续的空闲 chunk，所以将 p 设置为 p 的前一个 chunk，也就是 p 指向空闲 chunk，并将
            该空闲 chunk 从空闲 chunk 链表中移除，并将将该空闲 chunk 赋值给 sub_heap 的 top chunk，
            并设置 top chunk 的 size，标识 top chunk 的前一个 chunk 处于 inuse 状态。然后继续判断循
            环条件，如果循环条件不满足，退出循环，如果条件满足，继续对当前 sub_heap 进行收缩。
       */

    // 删除当前heap，更新当前heap未prev heap
    ar_ptr->system_mem -= heap->size;
    arena_mem -= heap->size;
    delete_heap(heap);
    heap = prev_heap;
    // 去设置新的top_chunk
    if(!prev_inuse(p)) { /* consolidate backward */
      p = prev_chunk(p);
      unlink(p, bck, fwd);
    }
    assert(((unsigned long)((char*)p + new_size) & (pagesz-1)) == 0);
    assert( ((char*)p + new_size) == ((char*)heap + heap->size) );
    top(ar_ptr) = top_chunk = p;
    set_head(top_chunk, new_size | PREV_INUSE);
    /*check_chunk(ar_ptr, top_chunk);*/
  }

  /*
    首先查看 top chunk 的大小，如果 top chunk 的大小减去 pad 和 MINSIZE 小于一页大小，
    返回退出，否则调用 shrink_heap()函数对当前 sub_heap 进行收缩，将空闲的整数个页收缩
    掉，仅剩下不足一页的空闲内存，如果 shrink_heap()失败，返回退出，否则，更新内存使用
    统计，更新 top chunk 的大小。
   */

  top_size = chunksize(top_chunk);
  extra = ((top_size - pad - MINSIZE + (pagesz-1))/pagesz - 1) * pagesz;
  if(extra < (long)pagesz)
    return 0;
  /* Try to shrink. */
  if(shrink_heap(heap, extra) != 0)
    return 0;
  ar_ptr->system_mem -= extra;
  arena_mem -= extra;

  /* Success. Adjust top accordingly. */
  set_head(top_chunk, (top_size - extra) | PREV_INUSE);
  /*check_chunk(ar_ptr, top_chunk);*/
  return 1;
}

/* Create a new arena with initial size "size".  */

static mstate
_int_new_arena(size_t size)
{
  mstate a;
  heap_info *h;
  char *ptr;
  unsigned long misalign;

  h = new_heap(size + (sizeof(*h) + sizeof(*a) + MALLOC_ALIGNMENT),
           mp_.top_pad);
  if(!h) {
    /* Maybe size is too large to fit in a single heap.  So, just try
       to create a minimally-sized arena and let _int_malloc() attempt
       to deal with the large request via mmap_chunk().  */
    h = new_heap(sizeof(*h) + sizeof(*a) + MALLOC_ALIGNMENT, mp_.top_pad);
    if(!h)
      return 0;
  }
  a = h->ar_ptr = (mstate)(h+1);
  malloc_init_state(a);
  /*a->next = NULL;*/
  a->system_mem = a->max_system_mem = h->size;

  arena_mem += h->size;
#ifdef NO_THREADS
  if((unsigned long)(mp_.mmapped_mem + arena_mem + main_arena.system_mem) >
     mp_.max_total_mem)
    mp_.max_total_mem = mp_.mmapped_mem + arena_mem + main_arena.system_mem;
#endif

  /* Set up the top chunk, with proper alignment. */
  ptr = (char *)(a + 1);
  misalign = (unsigned long)chunk2mem(ptr) & MALLOC_ALIGN_MASK;
  if (misalign > 0)
    ptr += MALLOC_ALIGNMENT - misalign;
  top(a) = (mchunkptr)ptr;
  set_head(top(a), (((char*)h + h->size) - ptr) | PREV_INUSE);

  return a;
}

static mstate
internal_function
#if __STD_C
arena_get2(mstate a_tsd, size_t size)
#else
arena_get2(a_tsd, size) mstate a_tsd; size_t size;
#endif
{
  mstate a;

  // 本函数在arena_get分配不到该线程对应的arena时调用（可能该线程根本没有arena，或者是被占用）
  // 参数里提供的a_tsd为null，则表示根本没有arena，不为null，则表示当前被占用
  // 当没有arena时，设置为main_arena
  if(!a_tsd)
    a = a_tsd = &main_arena;
  else {
    a = a_tsd->next;
    if(!a) {
      /* This can only happen while initializing the new arena. */
      (void)mutex_lock(&main_arena.mutex);
      THREAD_STAT(++(main_arena.stat_lock_wait));
      return &main_arena;
    }
  }

  /* Check the global, circularly linked list for available arenas. */
  bool retried = false;
 repeat:
  do {
    if(!mutex_trylock(&a->mutex)) { // 尝试加锁成功
      if (retried) // 此前已经尝试过一轮了，那么此时我们一定对 list lock  加锁一次了, 我们解锁list lock
        (void)mutex_unlock(&list_lock);
      THREAD_STAT(++(a->stat_lock_loop));
      tsd_setspecific(arena_key, (Void_t *)a); // 设置当前的tsd（arena）为a
      return a;
    }
    a = a->next;       // 尝试去下一个arena里寻找
  } while(a != a_tsd); // 这是循环链表，即为遍历所有的arena

  /* If not even the list_lock can be obtained, try again.  This can
     happen during `atfork', or for example on systems where thread
     creation makes it temporarily impossible to obtain _any_
     locks. */
  if(!retried && mutex_trylock(&list_lock)) {// 第一遍，且加锁不成功，此时可能是atfork的原因
    /* We will block to not run in a busy loop.  */
    (void)mutex_lock(&list_lock); // 阻塞到这里，获取进程的全局arena_key

    // 注意此时我们一定有了arena key 的锁,
    /* Since we blocked there might be an arena available now.  */
    // 在我们block的这段时间内，可能又有了arena被释放了，其实主要是应对atfork
    // atfork会获取list lock和每个arena的锁，也会同时释放每个arena的锁和list lock的锁
    // 在atfork 情况下，我们获得list lock的锁后，arena的锁可能也被释放了，我们依旧再去检查一遍arena
    retried = true;
    a = a_tsd;
    goto repeat;
  }// 此时找遍了arena，没有立马可用的，我们此时还加着list_lock的锁呢

  // 总结我们找arena的策略：
  // 当前线程找的到，则立马使用当前线程的，
  // 找不到的话，我们遍历所有的arena，看是否有空闲的，
  // 我们确保会遍历一次所有arena，也就是会等arena_key的锁，但是不会等arena的锁
  // 遍历一遍还是没有合适的arena，那么我们就创建一个新的arena

  /* Nothing immediately available, so generate a new arena.  */
  a = _int_new_arena(size);
  if(a)
    {
      tsd_setspecific(arena_key, (Void_t *)a);
      mutex_init(&a->mutex);
      mutex_lock(&a->mutex); /* remember result */

      /* Add the new arena to the global list.  */
      a->next = main_arena.next;
      atomic_write_barrier (); // ？？？？ 这是个啥
      main_arena.next = a;

      THREAD_STAT(++(a->stat_lock_loop));
    }
  (void)mutex_unlock(&list_lock);

  return a;
}

#endif /* USE_ARENAS */

/*
 * Local variables:
 * c-basic-offset: 2
 * End:
 */
