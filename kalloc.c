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
	cprintf("mem start is %p\n", start);
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
#define putpage(p)	kfree(p, PAGE)
#define OBJ_MIN		8
#define OBJ_MAX		3956 /* PAGE - sizeof(struct slab) */
#define SLAB_MAGIC_INIT 0xabbaabba
#define SLAB_FREE_MAX	8

struct cache *foo_cache;

/* cache - slabs (one slab - one page) */
/* move to defs.h
struct cache {
	struct cache *next;
	struct cache *prev;
	struct slab *sfull;
	struct slab *spart;
	struct slab *sfree;
	int objsize;
	void (*ctor)(void *);
	void (*dtor)(void *);
	struct spinlock lock;
};
*/
struct slab {
	struct cache *cache;
	struct slab *next;
	struct slab *prev;
	void *obj; /* first free obj */
	struct spinlock lock;
	unsigned char objmap[64]; /* obj usage bitmap one bit for one obj*/
	unsigned int which; /* belong to which list full/free/partial */
	unsigned int magic;  /* magic number to indicate initilize state */
};

static inline void slab_setbit(struct slab *slabp, int i)
{
	int j,k;

	j = i/8;
	k = i%8;

	slabp->objmap[j] |= 1 << k;
}

static inline void slab_clrbit(struct slab *slabp, int i)
{
	int j,k;

	j = i/8;
	k = i%8;

	slabp->objmap[j] &= ~(1 << k);
}

static inline int slab_getbit(struct slab *slabp, int i)
{
	int j,k;

	j = i/8;
	k = i%8;

	return slabp->objmap[j] & (1 << k);
}

static inline int slab_first_free_bit(struct slab *slabp)
{
	int i, k = -1;

	for (i = 0; i<(64 * 8) ;i++)
		if (!slab_getbit(slabp, i)) {
			k = i;
			break;
		}
	return k;
}

static inline int slab_free_bit_count(struct slab *slabp)
{
	int i, k = 0;

	for (i = 0; i<(64 * 8); i++)
		if (!slab_getbit(slabp, i))
			k++;
	return k;
}

static int slab_obj_all_free(struct slab *slabp)
{
	return slab_free_bit_count(slabp) == 64 * 8;
}


static struct cache *cache_head;
static struct cache *cache_tail;

static struct cache cache_cache;

/* cache_cahce init */
void kmem_cache_init(void)
{
	cache_cache.next = NULL;
	cache_cache.prev= NULL;
	cache_cache.sfull= NULL;
	cache_cache.spart = NULL;
	cache_cache.sfree = NULL;
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
	struct slab *slabp = NULL;
	void *mem;

	cprintf("grow\n");
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
		while ((mem + cache->objsize) < (void *)slabp) {
			cache->ctor(mem);
			mem += cache->objsize;
		}

	slabp->magic = SLAB_MAGIC_INIT;

link:
	slabp->prev = NULL;
	slabp->next = NULL;
	cache->sfree = slabp;

	return 0;
}

static inline int freelist_cnt(struct slab *s)
{
	int i = 0;

	while (s) {
		i++;
		s = s->next;
	}

	return i;
}

/* free the slab */
static int slab_free(struct slab *slabp)
{
	int f;

	f = freelist_cnt(slabp);

	slabp->prev->next = slabp->next;
	slabp->next->prev = slabp->prev;
	slabp->prev = NULL;
	slabp->next = NULL;

	if (f > SLAB_FREE_MAX) {
		/* return slab to page pool */
		putpage((void *)(slabp + sizeof(struct slab) - PAGE));
	} else { 
		slabp->next = slabp->cache->sfree;
		slabp->cache->sfree->prev = slabp;
	}

	return 0;
}

static void update_obj(struct slab *slabp)
{
	int i, size;

	i = slab_first_free_bit(slabp);
	size = slabp->cache->objsize;

	slabp->obj = (void *)((int)slabp + sizeof(struct slab) + i * size - PAGE);
}

static void part_to_full(struct slab *slabp)
{
	struct cache *c = slabp->cache;

	slabp->prev->next = slabp->next;
	slabp->next->prev = slabp->prev;

	slabp->prev = c->sfull->prev;
	slabp->next = c->sfull;
	c->sfull->prev = slabp;

	/* need to get the lock */
	
}

static void full_to_part(struct slab *slabp)
{
	struct cache *c = slabp->cache;

	slabp->prev->next = slabp->next;
	slabp->next->prev = slabp->prev;

	slabp->prev = c->spart->prev;
	slabp->next = c->spart;
	c->spart->prev = slabp;

	/* need to get the lock */
}

static inline void *getobj(struct slab *slabp)
{
	int i;
	void *obj = slabp->obj;

	if (!obj)
		cprintf("wrong address\n");
	if (!slab_free_bit_count(slabp)) {
		cprintf("No space in this slab\n");
		return NULL;
	}

	i = slab_first_free_bit(slabp);

	slab_setbit(slabp, i);
	if (slab_free_bit_count(slabp))
		update_obj(slabp);
	else {
		slabp->obj = NULL;
		part_to_full(slabp);
	}

	return obj;
}

/*
 * 1. set bitmap
 * 2. reinit (ctor)
 * 3. if whole slab free, free the slab, update link lists
 */
static inline void putobj(struct slab *slabp, void *obj)
{
	int size, i;

	size = slabp->cache->objsize;
	i = ((uint)obj & (PAGE - 1))/size;

	if (!slab_free_bit_count(slabp))
		full_to_part(slabp);
	slab_clrbit(slabp, i);
	slabp->cache->ctor(obj);
	update_obj(slabp);

	if (slab_obj_all_free(slabp))
		slab_free(slabp);
}

static struct slab *find_part(struct cache *cache)
{
	struct slab *p = NULL;

	for(p = cache->spart; p; p = p->next) {
		if (slab_free_bit_count(p))
			break;
	}

	return p;
}

static struct slab *free_to_part(struct cache *cache)
{
	struct slab *slabp;

	slabp = cache->sfree;

	cache->sfree = slabp->next;
	cache->sfree->prev = NULL;

	slabp->next = cache->spart;

	if(cache->spart)
		cache->spart->prev = slabp;

	cache->spart = slabp;

	return slabp;
}

void *kmem_cache_alloc(struct cache *cache)
{
	int ret;
	struct slab *slabp;

	acquire(&cache->lock);

	slabp = find_part(cache);

	if (slabp)
		goto ge;

	if (!cache->sfree) {
		ret = kmem_cache_grow(cache);
		if (ret < 0)
			return NULL;
		/* there's no free slab, need create one */
	} 

	slabp = free_to_part(cache);
ge:
	release(&cache->lock);
	/* alloc one object from the slab */
	return getobj(slabp);
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

	return cachep;
out:
	return NULL;
}

int kmem_cache_free(void *obj)
{
	struct slab *slabp;
	
	slabp = (struct slab *)(((uint)obj & ~(PAGE -1)) + PAGE - sizeof(struct slab));
	/* set the bitmap to 0 */
	putobj(slabp, obj);
	
	/* if all 0 release the slab*/
	if(!slab_free_bit_count(slabp))
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

void *kmalloc(int size);
void slab_test(void);

/* init slab/sizes chaches*/
int kmem_cache_sizes_init(void)
{
	int i;

	for(i=0; i<8; i++) {
		/* create size slab */
		cache_sizes[i].cache = kmem_cache_create(cache_sizes[i].size, NULL, NULL); 
		cprintf("cache_size - %d: %p\n", cache_sizes[i].size, cache_sizes[i].cache);
	}

	slab_test();
	return 0;
}

void *kmalloc(int size)
{
	int i;

	for(i=0; i<8; i++) {
		if (size >= cache_sizes[i].size) {

			if (i<7 && size < cache_sizes[i+1].size)
				return kmem_cache_alloc(cache_sizes[i].cache);		
			if (i==7 && size == cache_sizes[i].size)
				return kmem_cache_alloc(cache_sizes[i].cache);		
		}
	}

	cprintf("size too large for kmalloc, please use kalloc instead\n");
	return NULL;
}

int kmfree(void *obj)
{
	kmem_cache_free(obj);

	return 0;
}

struct foo {
	struct spinlock lock;
	int val;
	struct foo *next;
	char t[10];
};

void __foo_init(void * obj)
{
	int i;
	struct foo *f = (struct foo *)obj;

	initlock(&f->lock, "flock");
	f->val = 1;
	f->next = NULL;
	for (i=0; i<10; i++)
		f->t[i] = 'a';		
}

void __foo_exit(void * obj)
{
	;
}

void slab_test(void)
{
	int i;
	char *test;
	struct foo *ftest[8];

	test = kmalloc(100);

	if(test)
		cprintf("kmalloc 100 success : %p\n", test);
	else
		cprintf("kmalloc 100 fail\n");

	cprintf("foo_cache creat ..\n");
	foo_cache = kmem_cache_create(sizeof(struct foo), __foo_init, __foo_exit);
	if (!foo_cache) {
		cprintf("foo_cache creat failed\n");
		return;
	}

	cprintf("foo_cache created: %p\n", foo_cache);

	for (i=0; i<8; i++) {
		ftest[i] = kmem_cache_alloc(foo_cache);
		cprintf("struct foo alloced: %p\n", ftest[i]);
	}

	cprintf("struct foo free: %p\n", ftest[0]);
	kmem_cache_free(ftest[0]);
	ftest[0] = kmem_cache_alloc(foo_cache);
	cprintf("struct foo alloced again: %p\n", ftest[0]);

	cprintf("struct foo free: %p\n", ftest[1]);
	kmem_cache_free(ftest[1]);
	ftest[0] = kmem_cache_alloc(foo_cache);
	cprintf("struct foo alloced again: %p\n", ftest[1]);

	cprintf("struct foo free: %p\n", ftest[2]);
	kmem_cache_free(ftest[2]);
	ftest[0] = kmem_cache_alloc(foo_cache);
	cprintf("struct foo alloced again: %p\n", ftest[2]);

	cprintf("struct foo free: %p\n", ftest[3]);
	kmem_cache_free(ftest[3]);
	ftest[0] = kmem_cache_alloc(foo_cache);
	cprintf("struct foo alloced again: %p\n", ftest[3]);
}
