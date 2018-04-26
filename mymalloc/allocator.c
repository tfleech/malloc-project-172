/**
 * Copyright (c) 2015 MIT License by 6.172 Staff
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 **/

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "./allocator_interface.h"
#include "./memlib.h"

// TUNING PARAMS

#ifndef SBRK_ON_REALLOC
  // when 1, will sbrk additional memory instead of consulting free list when
  // reallocing more memory into the last chunk on the heap.
  #define SBRK_ON_REALLOC 1
#endif

// we shouldn't need more than a terabyte of heap
#define MAX_BYTE_SIZE 40

#define FREE 1
#define OCCUPIED 2

// Don't call libc malloc!
#define malloc(...) (USE_MY_MALLOC)
#define free(...) (USE_MY_FREE)
#define realloc(...) (USE_MY_REALLOC)

// All blocks must have a specified minimum alignment.
// The alignment requirement (from config.h) is >= 8 bytes.
#ifndef ALIGNMENT
  #define ALIGNMENT 8
#endif

// Rounds up to the nearest multiple of ALIGNMENT.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

// The smallest aligned size that will hold a size_t value.
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define HEADER_SIZE (SIZE_T_SIZE)  // header and footer are both 8 byte
#define FOOTER_SIZE (SIZE_T_SIZE)  // header and footer are both 8 byte
#define OVERHEAD_SIZE (HEADER_SIZE + FOOTER_SIZE)  // header and footer are both 8 byte

// get the log base 2 of a size, which is the index of the bucket a chunk of
//    this size should be placed in
static int log_2(size_t x) {
  return 64 - __builtin_clzl(x);
}

// TYPE DEFINITIONS //

// use this type when the value represented is log(number of bytes) rather than
//  the actual number.
typedef uint32_t bytecount_t;

// placed at the beginning of each chunk allocated. log_size and free are preserved
//   across allocations, but next and prev are within the returnbed memory region,
//   and thus are only valid for free chunks.
typedef struct __attribute__((packed)) free_node_header {
  bytecount_t log_size;
  int32_t free;
  struct free_node_header* next;
  struct free_node_header* prev;
} free_node_t;

// placed at the end of each memory region, to allow for chunks to the right of
//   this to find the start of this
typedef struct __attribute__((packed)) free_node_footer {
  bytecount_t log_size;
  int32_t free;
} free_node_footer_t;

// STATIC FUNCTION DECLARATIONS //
static void coalese_search(free_node_t* ptr);

// GLOBAL VARIABLES //

// the i'th element of this array holds the first element in a linked list
//   of 2^i byte free blocks
free_node_t* bin_free_list[MAX_BYTE_SIZE];

// largest bin with a free node in it, or 0 if no such bin exists
bytecount_t max_bin;

void* rightmost_chunk;

free_node_footer_t* get_footer(free_node_t* chunk) {
  bytecount_t log_size = chunk->log_size;
  return ((free_node_footer_t*)((uint8_t*)chunk + (1 << log_size))) - 1;
}

int my_check() {
  // check for max_bin's invariant
  assert(max_bin == 0 || bin_free_list[max_bin] != NULL);
  for (size_t i = 0; i < MAX_BYTE_SIZE; i++) {
    // check for max_bin's invariant pt. 2
    assert(i <= max_bin || bin_free_list[i] == 0);

    free_node_t* cur = bin_free_list[i];
    assert(cur == NULL || cur->prev == NULL);
    assert(cur == NULL || (size_t)(cur->next) > 1000 || cur->next == NULL);

    if (cur != NULL) {
      assert(get_footer(cur)->free == cur->free);
      assert(get_footer(cur)->log_size == cur->log_size);
      assert( cur <= rightmost_chunk);
      cur = cur->next;
    }
    while (cur != NULL) {
      assert(cur <= rightmost_chunk);

      assert(get_footer(cur)->free == cur->free);
      assert(get_footer(cur)->log_size == cur->log_size);

      assert(cur->next == NULL || cur->next->prev == cur);
      assert(cur->prev->next == cur);

      assert((size_t)cur->prev > 1000);
      assert((size_t)cur->next > 1000 || cur->next == NULL);
      cur = cur->next;
    }

    // check for any funny business like a casted element in BFL being a `size` rather than a `next`
    assert(((size_t)bin_free_list[i]) == 0 || ((size_t)bin_free_list[i]) > 50);
    assert(((size_t)bin_free_list[i]) == 0 ||
           ((size_t)bin_free_list[i]->next) > 50 ||
           ((size_t)bin_free_list[i]->next) == 0);
  }

  return 0;
}

// init - Initialize the malloc package.  Called once before any other calls are made.
//  Simply set all globals to default vals.
int my_init() {
  max_bin = 0;
  for (size_t i = 0; i < MAX_BYTE_SIZE; i++) {
    bin_free_list[i] = NULL;
  }
  rightmost_chunk = NULL;
  return 0;
}

// accepts the direct address (no HEADER_SIZE offset) of memory block
//  and its size in bytes and adds that block to the head of the appropriate BFL.
// given a pointer to a node with correct size data, will complete prev, next, free, and footer
void add_free_node(free_node_t* new_node, bytecount_t log_size) {
  // maintain invariant that max_bin is the maximum non-null index into bin_free_list
  //  in the event we just freed a chunk bigger than our current largest
  if (log_size > max_bin) {
    max_bin = log_size;
  }

  new_node->next = bin_free_list[log_size];
  new_node->prev = NULL;
  new_node->free = FREE;
  new_node->log_size = log_size;
  assert(log_size == new_node->log_size);
  if (bin_free_list[log_size]) {
    bin_free_list[log_size]->prev = new_node;
  }
  bin_free_list[log_size] = new_node;

  free_node_footer_t* footer = get_footer(new_node);
  footer->free = FREE;
  footer->log_size = log_size;
}

//  malloc - Allocate a block by first checking for an exact match in BFL, then
//    checking for any bigger bin which can be split into bins of the appropriate
//    size, then finally if no other options left incrementing the heap pointer.
void* my_malloc(size_t size) {
  // We allocate a little bit of extra memory so that we can store the
  // size of the block we've allocated.
  size_t aligned_size = ALIGN(size + OVERHEAD_SIZE);

  bytecount_t log_size = log_2(aligned_size);
  void* p;

  if (bin_free_list[log_size] != NULL) {
    // simplist case: we can simply get a chunk from the BFL for the correct size
    p = bin_free_list[log_size];
    bin_free_list[log_size] = bin_free_list[log_size]->next;
    if (bin_free_list[log_size]) {
      bin_free_list[log_size]->prev = NULL;
    }

    // maintain invariant that max_bin is the maximum non-null index into
    // bin_free_list
    //  in the event we just gave away our last max_bin byte chunk.
    if (log_size == max_bin && bin_free_list[log_size] == NULL) {
      while (bin_free_list[max_bin] == NULL && max_bin > 0) {
        max_bin--;
      }
    }
  } else if (max_bin > log_size) {
    // split+cascade case: we find the next free chunk bigger than needed, and
    //  bisect it all the way down until we get two of the correct size chunks.
    //  We store all the intermediary chunks and one of the correctly sized ones
    //  in BFL, then return the other correctly sized one.


    // find smallest chunk in BFL bigger than needed
    bytecount_t next_biggest = log_size + 1;
    while (bin_free_list[next_biggest] == NULL) {
      next_biggest++;
    }
    // pop it from its list
    free_node_t* to_split = bin_free_list[next_biggest];
    bin_free_list[next_biggest] = to_split->next;
    if (bin_free_list[next_biggest]) {
      bin_free_list[next_biggest]->prev = NULL;
    }

    // maintain invariant that max_bin is the maximum non-null index into
    //  bin_free_list in the event we just split the previous single largest chunk.
    if (bin_free_list[max_bin] == NULL) {
      max_bin--;
    }

    // split chunk we just got up a bunch and store the daughter chunks in BFL.
    for (bytecount_t sub_block_log_size = next_biggest - 1;
         sub_block_log_size >= log_size;
         sub_block_log_size--) {
      add_free_node(to_split, sub_block_log_size);
      to_split = (free_node_t*)(((char*) to_split) + // cast to char* so addition works
                                (1 << sub_block_log_size));
    }
    p = to_split;
  } else {
    // worst case: alloc more memory from the OS or whatever
    p = mem_sbrk(1 << log_size);
    rightmost_chunk = p;
  }


  if (p == (void*) - 1) {
    // Whoops, an error of some sort occurred.  We return NULL to let
    // the client code know that we weren't able to allocate memory.
    return NULL;
  } else {
    // We store the size of the block we've allocated in the first
    // HEADER_SIZE bytes.

    ((free_node_t*)p)->log_size = log_size;
    ((free_node_t*)p)->free = OCCUPIED;

    free_node_footer_t* footer = get_footer(p);
    footer->log_size = log_size;
    footer->free = OCCUPIED;


    // Then, we return a pointer to the rest of the block of memory,
    // which is at least size bytes long.  We have to cast to uint8_t
    // before we try any pointer arithmetic because voids have no size
    // and so the compiler doesn't know how far to move the pointer.
    // Since a uint8_t is always one byte, adding HEADER_SIZE after
    // casting advances the pointer by HEADER_SIZE bytes.
    return (void*)((char*)p + HEADER_SIZE);
  }
}

// free - add this chunk back to the BFL, coalesing if possible
void my_free(void* ptr) {
  // free'ing null is nop
  if (ptr == NULL) {
    return;
  }

  // restore the header as the start of this memory region.
  free_node_t* direct_address = (free_node_t*)((char*)ptr - HEADER_SIZE);
  bytecount_t size = *((bytecount_t*) direct_address);
  add_free_node(direct_address, size);
  coalese_search(direct_address);
}

// remove a node from a doubly linked list
void remove_node(free_node_t* node) {
  if (bin_free_list[node->log_size] == node) {
    bin_free_list[node->log_size] = node->next;
    if (bin_free_list[node->log_size]) {
      bin_free_list[node->log_size]->prev = NULL;
    }
    return;
  }

  if (node->prev != NULL) {
    node->prev->next = node->next;
  }
  if (node->next != NULL) {
    node->next->prev = node->prev;
  }
}

// attemt to find free nodes of the same chunk size as ptr on the
//   left or right of ptr, then combine these chunks recursively.
// removes all combined chunks from their respective free lists.
static void coalese_search(free_node_t* ptr) {
  free_node_t* right = (free_node_t*)((uint8_t*)ptr + (1 << ptr->log_size));

  free_node_footer_t* left_footer = ((free_node_footer_t*)ptr) - 1;

  free_node_t* left = (free_node_t*)((uint8_t*)ptr - (1 << left_footer->log_size));
  if ((void*)left < my_heap_lo()) {
    left = NULL;
  }
  if ((void*)right > my_heap_hi()) {
    right = NULL;
  }

  if (right && right->free == FREE && right->log_size == ptr->log_size) {
    remove_node(ptr);
    remove_node(right);
    free_node_t* big = ptr;
    big->log_size = ptr->log_size + 1;
    add_free_node(big, big->log_size);
    return coalese_search(big);
  }

  if (left && left->free == FREE && left->log_size == ptr->log_size) {
    remove_node(left);
    remove_node(ptr);
    free_node_t* big = left;
    big->log_size = ptr->log_size + 1;
    add_free_node(big, big->log_size);
    return coalese_search(big);
  }
}


// realloc - Implemented simply in terms of malloc and free
void* my_realloc(void* ptr, size_t size) {
  void* newptr;

  // Get the size of the old block of memory.  Take a peek at my_malloc(),
  // where we stashed this in the HEADER_SIZE bytes directly before the
  // address we returned.  Now we can back up by that many bytes and read
  // the size.
  bytecount_t* direct_address = (bytecount_t*)((uint8_t*)ptr - HEADER_SIZE);
  size_t copy_size = 1 << *direct_address;
  bytecount_t log_copy_size = *direct_address;
  bytecount_t log_size = log_2(ALIGN(size + OVERHEAD_SIZE));

  if (size == 0) {
    my_free(ptr);
    return NULL;
  } else if (!ptr) {
    return my_malloc(size);
  } else if (log_size == log_copy_size) {
    return ptr;
  } else if (log_size < log_copy_size) {
    bytecount_t* free_ptr = (bytecount_t*)((uint8_t*)ptr - HEADER_SIZE + (1 << log_size));
    *direct_address = log_size;
    while ((uint8_t*)free_ptr < ((uint8_t*)ptr - HEADER_SIZE + (1 << log_copy_size))) {
      *free_ptr = log_size;
      my_free((uint8_t*)free_ptr + HEADER_SIZE);
      log_size++;
      free_ptr += 1 << log_size;
    }
    return ptr;
  } else {
    if (SBRK_ON_REALLOC && direct_address == rightmost_chunk) {
      mem_sbrk((1 << log_size) - copy_size);
      *direct_address = log_size;
      return ptr;
    } else {
      newptr = my_malloc(size);
      if (newptr) {
        memcpy(newptr, ptr, copy_size);
        my_free(ptr);
      }
      return newptr;
    }
  }
}

// call mem_reset_brk.
void my_reset_brk() {
  mem_reset_brk();
}

// call mem_heap_lo
void* my_heap_lo() {
  return mem_heap_lo();
}

// call mem_heap_hi
void* my_heap_hi() {
  return mem_heap_hi();
}
