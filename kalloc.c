// Physical memory allocator, intended to allocate
// memory for user processes. Allocates in 4096-byte "pages".
// Free list is kept sorted and combines adjacent pages into
// long runs, to make it easier to allocate big segments.
// One reason the page size is 4k is that the x86 segment size
// granularity is 4k.

#include "param.h"
#include "types.h"
#include "defs.h"
#include "param.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"

#define NULL	0

struct spinlock kalloc_lock;

struct run {
  struct run *next;
  int len; // bytes
};
struct run *freelist;

// Initialize free list of physical pages.
// This code cheats by just considering one megabyte of
// pages after _end.  Real systems would determine the
// amount of memory available in the system and use it all.
void
kinit(void)
{
  extern int end;
  uint mem;
  char *start;

  initlock(&kalloc_lock, "kalloc");
  start = (char*) &end;
  start = (char*) (((uint)start + PAGE) & ~(PAGE-1));
  mem = 256; // assume computer has 256 pages of RAM
  cprintf("mem = %d\n", mem * PAGE);
  kfree(start, mem * PAGE);
}

// Free the len bytes of memory pointed at by cp,
// which normally should have been returned by a
// call to kalloc(cp).  (The exception is when
// initializing the allocator; see kinit above.)
void
kfree(char *cp, int len)
{
  struct run **rr;
  struct run *p = (struct run*) cp;
  struct run *pend = (struct run*) (cp + len);
  int i;

  if(len % PAGE)
    panic("kfree");

  // Fill with junk to catch dangling refs.
  for(i = 0; i < len; i++)
    cp[i] = 1;

  acquire(&kalloc_lock);

  rr = &freelist;
  while(*rr){
    struct run *rend = (struct run*) ((char*)(*rr) + (*rr)->len);
    if(p >= *rr && p < rend)
      panic("freeing free page");
    if(pend == *rr){
      p->len = len + (*rr)->len;
      p->next = (*rr)->next;
      *rr = p;
      goto out;
    }
    if(pend < *rr){
      p->len = len;
      p->next = *rr;
      *rr = p;
      goto out;
    }
    if(p == rend){
      (*rr)->len += len;
      if((*rr)->next && (*rr)->next == pend){
        (*rr)->len += (*rr)->next->len;
        (*rr)->next = (*rr)->next->next;
      }
      goto out;
    }
    rr = &((*rr)->next);
  }
  p->len = len;
  p->next = 0;
  *rr = p;

 out:
  release(&kalloc_lock);
}

// Allocate n bytes of physical memory.
// Returns a kernel-segment pointer.
// Returns 0 if the memory cannot be allocated.
char*
kalloc(int n)
{
  struct run **rr;

  if(n % PAGE)
    panic("kalloc");

  acquire(&kalloc_lock);

  rr = &freelist;
  while(*rr){
    struct run *r = *rr;
    if(r->len == n){
      *rr = r->next;
      release(&kalloc_lock);
      return (char*) r;
    }
    if(r->len > n){
      char *p = (char*)r + (r->len - n);
      r->len -= n;
      release(&kalloc_lock);
      return p;
    }
    rr = &(*rr)->next;
  }
  release(&kalloc_lock);
  cprintf("kalloc: out of memory\n");
  return 0;
}


#define getpage()	kalloc(PAGE)
#define freepage(p)	kfree(p)
#define OBJ_MIN		8
#define OBJ_MAX		4096
#define SLAB_MAGIC_UNINIT 0x12345678
#define SLAB_MAGIC_INIT 0xabbaabba

/* one cache - one slab - one page */

struct cache {
	struct cache *next;
	void *slist; /* full ... partial slab list head */
	void *spart; /* the least free partial slab */
	int objsize; /* object size */
	void (*ctor)(void *); /* creator */ 
	void (*dtor)(void *); /* destroctor */
	struct spinlock lock;
};

struct slab {
	struct cache *cache;
	void *obj; /* first free obj */
	struct spinlock lock;
	unsigned char objmap[64]; /* obj usage bitmap one bit for one obj*/
	unsigned int magic; /* magic number to indicate initilize state */
};

static inline void slab_setbit(struct slab *slabp, int i)
{
	int j,k;

	j = i/8;
	k = i%8;

	slabp->objmap[j] |= 1 << (8-k);
}

static inline void slab_clrbit(struct slab *slabp, int i)
{
	int j,k;

	j = i/8;
	k = i%8;

	/* ... */
}

static inline int slab_first_free_bit(struct slab *slabp)
{
	return 0;
}

static inline int slab_free_bit_count(struct slab *slabp)
{
	return 0;
}

struct cache *cache_head;
struct cache *cache_tail;

struct cache cache_cache;

/* cache_cahce init */
void kmem_cache_init(void)
{
	cache_cache.next = NULL;
	cache_cache.slist = NULL;
	cache_cache.spart = NULL;
	cache_cache.objsize = sizeof(struct cache);
	cache_cache.ctor = NULL;
	cache_cache.dtor = NULL;
  	initlock(&cache_cache.lock, "cache_cache");
	cache_head = &cache_cache;
	cache_tail = &cache_cache;
}

/* 
 * Grow (by 1) the number of slabs within a cache.  This is called by
 * kmem_cache_alloc() when there are no active objs left in a cache.
 * caller must acquire the cache lock.
 */
static int kmem_cache_grow(struct cache *cache)
{
	struct slab *slabp = cache->spart;
	void *mem;

	mem = getpage();		
	if(!mem)
		return -1;

	/* get a slab  */
	slabp = mem + PAGE - sizeof(struct slab);

	/* after free to page cache the slab will restore to init state */
	if (slabp->cache == cache && slabp->magic == SLAB_MAGIC_INIT)
		goto link;

	slabp->obj = mem;
	slabp->cache = cache;
	initlock(&slabp->lock, "slab");
	memset(slabp->objmap, 0, 64);

	if (cache->ctor)
		while (mem < slabp) {
			cache->ctor(mem);
			mem += cache->objsize;
		}

	slabp->magic = SLAB_MAGIC_INIT;

link:
	if(!cache->slist)
		cache->slist = slabp;
	cache->spart = slabp;

	return 0;
}

static inline void *getobj(struct slab *slabp)
{
	int size, max, i;
	void *obj = slabp->obj;

	size = slabp->cache->objsize;
	if ((PAGE - ((uint)obj & (PAGE - 1)) - sizeof(struct slab)) < size) {
		cprintf("No space in this slab\n");
		return NULL;
	}

	max = PAGE / size;
	i = ((uint)obj & (PAGE-1))/size;

	slab_setbit(slabp, i);
	slabp->obj += size;

	return obj;
}

void *kmem_cache_alloc(struct cache *cache)
{
	struct slab *slabp;
	void *mem = NULL;

	acquire(&cache->lock);

	if (!cache->spart) {
		kmem_cache_grow(cache);
		/* there's no free/partial slab, need create one */
	} 

	slabp = cache->spart;

	/* alloc one object from the slab */
	mem = getobj(slabp);

	release(&cache->lock);

	return mem;
}

struct cache *kmem_cache_create(int size, void (*ctor)(void*),
				void (*dtor)(void*))
{
	struct cache *cachep;

	if(size < OBJ_MIN || size > OBJ_MAX) {
		cprintf("%s: over size limit\n", __FUNCTION__);
		goto out;
	}

	/* TODO: add check for existed cache (by name? ) */

	if(dtor && !ctor){
		cprintf("dtor && !ctor, does not make sense\n");
		goto out;
	}

	cachep = kmem_cache_alloc(&cache_cache);
	if (!cachep)
		goto out;

	memset(cachep, 0, sizeof(struct cache));
	cachep->objsize = size;
	cachep->ctor = ctor;
	cachep->dtor = dtor;
	initlock(&cachep->lock, "anonymous");

	acquire(&kalloc_lock);
	cache_tail->next = cachep;
	cache_tail = cachep;
	release(&kalloc_lock);
out:
	return NULL;
}

static inline void putobj(struct slab *slabp, void *obj)
{
	/*
	 * 1. set bitmap
	 * 2. reinit (ctor)
	 * 3. if whole slab free, free the slab, update link lists
	 */
}

static int get_freecount(struct slab *slabp)
{
	/* calculate then return the bitmap free obj count */
	return 0;
}

static int slab_free(struct slab *slabp)
{
	/* free the slab to page cache */
	return 0;
}

int kmem_cache_free(void *obj)
{
	struct slab *slabp;
	
	slabp = (struct slab *)((uint)obj | (PAGE -1)) - sizeof(struct slab);
	/* set the bitmap to 0 */
	putobj(slabp, obj);
	
	/* if all 0 release the slab*/
	if(!get_freecount(slabp))
		slab_free(slabp);

	return 0;
}


struct cache_size {
	int size;
	struct cache *cache;
};

static struct cache_size cache_sizes[8] = {
	{  8,		NULL},
	{  16,		NULL},
	{  32,		NULL},
	{  64,		NULL},
	{ 128,		NULL},
	{ 256,		NULL},
	{ 512,		NULL},
	{1024,		NULL}
};

/* init slab/sizes chaches*/
int kmem_cache_sizes_init(void)
{
	int i;

	for(i=0; i<8; i++) {
		/* create size slab */
	}

	return 0;
}

void *kmalloc(int size)
{
	int i;

	for(i=0; i<8; i++) {
		if (size > cache_sizes[i].size)
			return kmem_cache_alloc(cache_sizes[i].cache);		
	}

	cprintf("size too large for kmalloc\n");
	return NULL;
}

int kmfree(void *obj)
{
	kmem_cache_free(obj);

	return 0;
}
