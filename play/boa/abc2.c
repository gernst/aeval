#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

  typedef ptrdiff_t sea_ptrdiff_t;
  /* need size to be signed */
  typedef ptrdiff_t sea_size_t;

  extern int8_t *nd_int8_ptr (void);
  extern int64_t nd_int64_t (void);
  extern sea_size_t nd_sea_size_t (void);

  static int8_t* sea_base;
  static int8_t* sea_ptr;
  static sea_ptrdiff_t sea_offset;
  static sea_size_t sea_size;
  static bool sea_active;

  extern void __VERIFIER_assume (int);
  __attribute__((__noreturn__)) extern void __VERIFIER_error (void);

#define assume __VERIFIER_assume
#define assert(X) if(!(X)){__VERIFIER_error ();}

  /* __attribute__((always_inline)) void assert  (int v)  { if (!v) __VERIFIER_error (); } */

  __attribute__((used)) void sea_abc_assert_valid_ptr (int8_t *base, sea_ptrdiff_t offset);
  __attribute__((used)) void sea_abc_assert_valid_offset (sea_ptrdiff_t offset, sea_size_t size);
  __attribute__((used)) void sea_abc_log_ptr (int8_t *base, sea_ptrdiff_t offset);
  __attribute__((used)) void sea_abc_alloc (int8_t *base, sea_size_t size);
  __attribute__((used)) void sea_abc_init(void);
  
#ifdef __cplusplus
}
#endif
 
/*
 * checks that base + offset is a valid pointer
 * insert after every load/store when size is unknown
 * base is a base pointer of some gep
 * offset is the computed offset _Should be adjusted for used size if needed_
 */

void sea_abc_assert_valid_ptr (int8_t *base, sea_ptrdiff_t offset)
{
  if (!sea_active) return;
  
  if (base == sea_base)
  {
   assert (offset >= 0 );
   assert (offset <= sea_size);
  }
#ifndef SEA_BASE_ONLY
  else if (base == sea_ptr)
  {
    assume (sea_ptr > sea_base);
    assert (sea_offset + offset >= 0);
    assert (sea_offset + offset <= sea_size);
  }
#endif
}

/**
 * insert after every load/store when offset and size are known
 * offset is the computed offset
 * size is a constant size
 */
void sea_abc_assert_valid_offset (sea_ptrdiff_t offset, sea_size_t size)
{
   assert (offset <= size);
  /* TODO: do not know how to check for underflow */
}

/**
 * insert after every p = gep(base, offset), if p is used indirectly
 * base - the base argument to gep
 * offset - the computed offset from gep + used_size
 */
void sea_abc_log_ptr (int8_t *base, sea_ptrdiff_t offset)
{
#ifndef SEA_BASE_ONLY
  if (nd_int64_t()) return;
  
  if (sea_active && sea_ptr == base)
  {
    /* update sea_ptr to base+offset, but trick alias analysis from
       noticing that sea_ptr and base might alias */
    sea_ptr = nd_int8_ptr();
    assume (sea_ptr == base + offset);
    sea_offset += offset;
  }
#endif
}

/**
 * insert after every allocation instruction
 * base - pointer to allocated buffer
 * size - the size of the allocated buffer
 */
void sea_abc_alloc (int8_t *base, sea_size_t size)
{
  if (!sea_active && sea_base == base)
  {
    assume (sea_size == size);
    sea_ptr = nd_int8_ptr();
    assume (sea_ptr == sea_base);
    sea_active = true;
  }
  else
    assume (sea_base + sea_size < base);
}

void sea_abc_init(void)
{
  sea_base = nd_int8_ptr ();
  assume (sea_base > 0);
  sea_size = nd_sea_size_t ();
  assume (sea_size >= 0); 
  sea_offset = 0;
  sea_ptr = 0;
  sea_active = false;
}
