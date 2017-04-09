#include <stdio.h>
#include <stdlib.h>
// #include "main.c"

int* copy_closure_recursively(int* reference_location, int* garter_val_addr, int* heap_top);
int* copy_tuple_recursively(int* reference_location, int* garter_val_addr, int* heap_top);
int print(int val);

const int DEBUG_GC = 0;

/*
  Prints the contents of the heap, in terms of the word number, the exact address,
  the hex value at that address and the decimal value at that address.  Does not
  attempt to interpret the words as Garter values

  Arguments:
    heap: the starting address of the heap
    size: the size in words
 */
void naive_print_heap(int* heap, int size) {
  for(int i = 0; i < size; i += 1) {
    printf("  %d/%p: %p (%d)\n", i, (heap + i), (int*)(*(heap + i)), *(heap + i));
  }
}

// Implement the functions below

/*
  Smarter algorithm to print the contents of the heap.  You should implement this function
  much like the naive approach above, but try to have it print out values as Garter values

  Arguments:
    from_start: the starting address (inclusive) of the from-space of the heap
    from_end: the ending address (exclusive) of the from-space of the heap
    to_start: the starting address (inclusive) of the to-space of the heap
    to_end: the ending address (exclusive) of the to-space of the heap
 */
void smarter_print_heap(int* from_start, int* from_end, int* to_start, int* to_end) {
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible

  // print from heap
  int from_size = from_end - from_start;
  printf("\n-----from heap-----\n");
  for(int i = 0; i < from_size; i += 1) {
    printf("  %d/%p: %p ", i, (from_start + i), (int*)(*(from_start + i)));
    printf("(");
    print(*(from_start + i));
    printf(")\n");
  }

  // print to heap
  int to_size = to_end - to_start;
  printf("-----to heap-----\n");
  for(int i = 0; i < to_size; i += 1) {
    printf("  %d/%p: %p (%d)\n", i, (to_start + i), (int*)(*(to_start + i)), *(to_start + i));
  }
}


int* copy_tuple_recursively(int* reference_location, int* garter_val_addr, int* heap_top) {
  int garter_val = *garter_val_addr;
  if (DEBUG_GC) {
    fprintf(stdout, "this is the garter_val for addr %x: %x\n", (uint)garter_val_addr, (uint)garter_val);
    fflush(stdout);
    fprintf(stdout, "(garter_val_addr[0] & ~0x1): %x\n", (uint)(garter_val_addr[0] & ~0x1));
    fflush(stdout);
  }
  // if garter_val is a (tagged) pointer to a heap-allocated garter value (tuple or closure)
  // call the pointed-to value heap_thing, then
  if ((garter_val_addr[0] & ~0x1) == 1) {
    if (DEBUG_GC) {
      fprintf(stdout, "forwarding pointer spotted!: %x\tchanging %x from %x to fwdptr\n", (uint)garter_val_addr[0], (uint)reference_location, (uint)*reference_location);
      fflush(stdout);
    }
    *reference_location = garter_val_addr[0];
    return heap_top;
  } else {
    if (DEBUG_GC) {
      fprintf(stdout, "changing %x from %x to %x\n", (uint)reference_location, (uint)reference_location[0], (uint)((void *)heap_top + 1));
      fflush(stdout);
    }
    reference_location[0] = (int)((void *)heap_top + 1);
  }
  int len = garter_val_addr[0] >> 1;
  // copy the full contents of heap_thing to heap_top
  int padding = 1;
  if ((((len + 1) * 4) % 8) == 0) {
    padding = 0;
  }
  if (DEBUG_GC) {
    fprintf(stdout, "do you recognize this value? heap_top[0]: %x\n", (uint)heap_top[0]);
    fflush(stdout);
  }
  for (int i = 0; i <= len + 1; i++) {
    if (DEBUG_GC) {
      fprintf(stdout, "garter_val_addr[i]: %x\n", (uint)garter_val_addr[i]);
      fflush(stdout);
    }
    heap_top[i] = garter_val_addr[i];
  }

  for (int i = len + 1; i <= (len + padding); i++) {
    heap_top[i] = 0xcafebabe;
  }
  // update the value at garter_val_addr with the value of heap_top
  // replace the value at garter_val (i.e. the address of heap_thing) with a forwarding
  // pointer to heap_top
  garter_val_addr[0] = (int)((void *)heap_top + 1);
  if (DEBUG_GC) {
    fprintf(stdout, "this should be 4: %x\tat this address: %x\n", (uint)heap_top[0], (uint)((void *)heap_top + 1));
    fflush(stdout);
  }
  // increment heap_top as needed to record the allocation
  // naive_print_heap(heap_top, 8);
  heap_top = &heap_top[len + padding + 1];
  // for each field within heap_thing at the new location,
  // recursively call copy_if_needed
  // (be careful about using the return value of those calls correctly!)
  int* new_heap_top_recursive = heap_top;
  if (DEBUG_GC) {
    fprintf(stdout, "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
    fflush(stdout);
  }
  for (int i = 1; i <= len; i++) {
    if (DEBUG_GC) {
      fprintf(stdout, "garter_val_addr[%d]\t%x\n", i, (uint)garter_val_addr[i]);
      fflush(stdout);
      fprintf(stdout, "(garter_val_addr[i] & 0x1): %x\n", (uint)(garter_val_addr[i] & 0x1));
      fflush(stdout);
      fprintf(stdout, "(garter_val_addr[i] & 0x7): %x\n", (uint)(garter_val_addr[i] & 0x7));
      fflush(stdout);
    }
    if ((garter_val_addr[i] & 0x7) == 5) {
      int* addr_to_follow = (int*)(garter_val_addr[i] - 5);
      if (DEBUG_GC) {
        fprintf(stdout, "I want to follow this closure address: %x\n", (uint)addr_to_follow);
        fflush(stdout);
      }
      new_heap_top_recursive = copy_closure_recursively(&garter_val_addr[i], addr_to_follow, new_heap_top_recursive);
    }
    if ((garter_val_addr[i] & 0x1) == 1) {
      int* addr_to_follow = (int*)(garter_val_addr[i] - 1);
      if (DEBUG_GC) {
        fprintf(stdout, "I want to follow this tuple address: %x\n", (uint)addr_to_follow);
        fflush(stdout);
      }
      new_heap_top_recursive = copy_tuple_recursively(&garter_val_addr[i], addr_to_follow, new_heap_top_recursive);
    }
  }
  return new_heap_top_recursive;
}

int* copy_closure_recursively(int* reference_location, int* garter_val_addr, int* heap_top) {
  int garter_val = *garter_val_addr;
  if (DEBUG_GC) {
    fprintf(stdout, "this is the garter_val for addr %x: %x\n", (uint)garter_val_addr, (uint)garter_val);
    fflush(stdout);
  }
  // if garter_val is a (tagged) pointer to a heap-allocated garter value (tuple or closure)
  // call the pointed-to value heap_thing, then
  if (DEBUG_GC) {
    fprintf(stdout, "(garter_val_addr[0] & ~0x1): %x\n", (uint)(garter_val_addr[0] & ~0x1));
    fflush(stdout);
  }
  if ((garter_val_addr[0] & ~0x1) == 1) {
    if (DEBUG_GC) {
      fprintf(stdout, "forwarding pointer spotted!: %x\tchanging %x from %x to fwdptr\n", (uint)garter_val_addr[0], (uint)reference_location, (uint)*reference_location);
      fflush(stdout);
    }
    *reference_location = garter_val_addr[0];
    return heap_top;
  } else {
    if (DEBUG_GC) {
      fprintf(stdout, "changing %x from %x to %x\n", (uint)reference_location, (uint)reference_location[0], (uint)((void *)heap_top + 1));
      fflush(stdout);
    }
    reference_location[0] = (int)((void *)heap_top + 1);
  }
  int len = garter_val_addr[0] >> 1;
  // copy the full contents of heap_thing to heap_top
  int padding = 1;
  if ((((len + 1) * 4) % 8) == 0) {
    padding = 0;
  }
  if (DEBUG_GC) {
    fprintf(stdout, "do you recognize this value? heap_top[0]: %x\n", (uint)heap_top[0]);
    fflush(stdout);
  }
  for (int i = 0; i <= len + 2; i++) {
    if (DEBUG_GC) {
      fprintf(stdout, "garter_val_addr[i]: %x\n", (uint)garter_val_addr[i]);
      fflush(stdout);
    }
    heap_top[i] = garter_val_addr[i];
  }

  for (int i = len + 2; i <= (len + padding + 1); i++) {
    heap_top[i] = 0xcafebabe;
  }
  // update the value at garter_val_addr with the value of heap_top
  // replace the value at garter_val (i.e. the address of heap_thing) with a forwarding
  // pointer to heap_top
  garter_val_addr[0] = (int)((void *)heap_top + 1);
  // increment heap_top as needed to record the allocation
  heap_top = &heap_top[len + padding + 2];
  // heap_top[len + 1] = 0xbeadcafe;
  // heap_top += (len + padding); // TODO is it x4?
  // for each field within heap_thing at the new location,
  // recursively call copy_if_needed
  // (be careful about using the return value of those calls correctly!)
  int* new_heap_top_recursive = heap_top;
  if (DEBUG_GC) {
    fprintf(stdout, "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
    fflush(stdout);
  }
  for (int i = 2; i <= len + 1; i++) {
    if (DEBUG_GC) {
      fprintf(stdout, "garter_val_addr[%d]\t%x\n", i, (uint)garter_val_addr[i]);
      fflush(stdout);
      fprintf(stdout, "(garter_val_addr[i] & ~0x1): %x\n", (uint)(garter_val_addr[i] & 0x1));
      fflush(stdout);
    }
    if ((garter_val_addr[i] & 0x7) == 5) {
      int* addr_to_follow = (int*)(garter_val_addr[i] - 5);
      if (DEBUG_GC) {
        fprintf(stdout, "I want to follow this closure address: %x\n", (uint)addr_to_follow);
        fflush(stdout);
      }
      new_heap_top_recursive = copy_closure_recursively(&garter_val_addr[i], addr_to_follow, new_heap_top_recursive);
    }
    if ((garter_val_addr[i] & 0x1) == 1) {
      int* addr_to_follow = (int*)(garter_val_addr[i] - 1);
      if (DEBUG_GC) {
        fprintf(stdout, "I want to follow this tuple address: %x\n", (uint)addr_to_follow);
        fflush(stdout);
      }
      new_heap_top_recursive = copy_tuple_recursively(&garter_val_addr[i], addr_to_follow, new_heap_top_recursive);
    }
  }
  return new_heap_top_recursive;
}


/*
  Copies a Garter value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location
    with a forwarding pointer to its new location

    heap_top -> is the next available ESI  on the new heap+/-
 */
int* copy_if_needed(int* garter_val_addr, int* heap_top) {
  int TUPLE_TAG_MASK = 0x00000007;
  int garter_val = *garter_val_addr;
  int* old_heap_top = heap_top;
  // TODO this check may not work when we add in lambdas?
  if ((garter_val & TUPLE_TAG_MASK) == 1) {
    // if garter_val is a (tagged) pointer to a heap-allocated garter value (tuple or closure)
    // call the pointed-to value heap_thing, then
    int* addr = (int*)(garter_val - 1);
    if ((addr[0] & ~0x1) == 1) {
      addr = (int*)(addr[0] - 1);
    }
    int len = addr[0] >> 1;
    // copy the full contents of heap_thing to heap_top
    // int padding = (len % 2) + 1;
    int padding = 1;
    if ((((len + 1) * 4) % 8) == 0) {
      padding = 0;
    }
    for (int i = 0; i <= len + 1; i++) {
      // heap_top[i] = addr[i];
      heap_top[i] = addr[i];
    }

    for (int i = len + 1; i <= (len + padding); i++) {
      heap_top[i] = 0xcafebabe;
    }
    // update the value at garter_val_addr with the value of heap_top
    if (DEBUG_GC) {
      fprintf(stdout, "this is garter_val_addr before: %x\t%x\theap_top: %x\n", (uint)garter_val_addr, (uint)*garter_val_addr, (uint)heap_top);
      fflush(stdout);
    }
    *garter_val_addr = (int)((void *)heap_top + 1); // change the value on stack to be ptr to heap_top
    if (DEBUG_GC) {
      fprintf(stdout, "this is garter_val_addr after: %x\t%x\theap_top: %x\n", (uint)garter_val_addr, (uint)*garter_val_addr, (uint)heap_top);
      fflush(stdout);
    }
    // replace the value at garter_val (i.e. the address of heap_thing) with a forwarding
    // pointer to heap_top
    addr[0] = (int)((void *)heap_top + 1);
    // increment heap_top as needed to record the allocation
    // naive_print_heap(heap_top, 8);
    heap_top = &heap_top[len + padding + 1];
    // for each field within heap_thing at the new location,
    // recursively call copy_if_needed
    // (be careful about using the return value of those calls correctly!)
    int* new_heap_top_recursive = heap_top;
    if (DEBUG_GC) {
      fprintf(stdout, "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
      fflush(stdout);
    }
    for (int i = 1; i <= len; i++) {
      if (DEBUG_GC) {
        fprintf(stdout, "addr[%d]\t%x\n", i, (uint)addr[i]);
        fflush(stdout);
        fprintf(stdout, "(addr[i] & 0x1): %x\n", (uint)(addr[i] & 0x1));
        fflush(stdout);
      }
      // if ((addr[i] & 0x7) == 5) {
      //   int* addr_to_follow = (int*)(addr[i] - 5);
      //   fprintf(stdout, "I want to follow this closure address: %x\n", addr_to_follow);
      //   fflush(stdout);
      //   new_heap_top_recursive = copy_closure_recursively(addr_to_follow, new_heap_top_recursive);
      // }
      if ((addr[i] & 0x7) == 5) {
        int* addr_to_follow = (int*)(addr[i] - 5);
        if (DEBUG_GC) {
          fprintf(stdout, "I want to follow this closure address: %x\n", (uint)addr_to_follow);
          fflush(stdout);
        }
        new_heap_top_recursive = copy_closure_recursively(&old_heap_top[i], addr_to_follow, new_heap_top_recursive);
      }
      if ((addr[i] & 0x1) == 1) {
        int* addr_to_follow = (int*)(addr[i] - 1);
        if (DEBUG_GC) {
          fprintf(stdout, "I want to follow this tuple address: %x\n", (uint)addr_to_follow);
          fflush(stdout);
          fprintf(stdout, "passing this as reference_location to change: %x\n", (uint)&old_heap_top[i]);
          fflush(stdout);
        }
        new_heap_top_recursive = copy_tuple_recursively(&old_heap_top[i],  addr_to_follow, new_heap_top_recursive);
      }
    }
    return new_heap_top_recursive;
  }
  // if garter_val is a tagged pointer to a closure...
  else if ((garter_val & TUPLE_TAG_MASK) == 5) {
    if (DEBUG_GC) {
      fprintf(stdout, "------------- COPY CLOSURE ---------------");
      fflush(stdout);
    }
    // if garter_val is a (tagged) pointer to a heap-allocated garter value (tuple or closure)
    // call the pointed-to value heap_thing, then
    int* addr = (int*)(garter_val - 5);
    if ((addr[0] & ~0x1) == 1) {
      addr = (int*)(addr[0] - 1);
    }
    int len = addr[0] >> 1;

    // copy the full contents of heap_thing to heap_top
    // int padding = (len % 2) + 1;
    int padding = 1;
    if ((((len + 2) * 4) % 8) == 0) {
      padding = 0;
    }
    // fprintf(stdout, "\n");
    // fflush(stdout);
    for (int i = 0; i <= len + 1; i++) {
      // heap_top[i] = addr[i];
      // fprintf(stdout, "len: %x, addr[%d]: %x\n", len, i, addr[i]);
      // fflush(stdout);
      heap_top[i] = addr[i];
    }

    for (int i = len + 2; i <= (len + 1 + padding); i++) {
      heap_top[i] = 0xcafebabe;
    }
    // update the value at garter_val_addr with the value of heap_top

    // fprintf(stdout, "\ngarter_val: %x\tgarter_val_addr: %x\theap_top + 5: %x\n", garter_val, garter_val_addr, (int)((void *)heap_top + 5));
    // fflush(stdout);
    *garter_val_addr = (int)((void *)heap_top + 5); // change the value on stack to be ptr to heap_top
    // *garter_val_addr = heap_top + 5; // change the value on stack to be ptr to heap_top
    // replace the value at garter_val (i.e. the address of heap_thing) with a forwarding
    // pointer to heap_top
    // fprintf(stdout, "------------------------------------- hi julie ----------------------------------------\n");
    // fflush(stdout);
    // fprintf(stdout, "heap_top + 1: %x\taddr[0]: %x\n", (int)((void *)heap_top + 1), addr[0]);
    // fflush(stdout);
    heap_top = &heap_top[len + padding + 2];
    return heap_top;

    // TODO sound the alarm!
    // we're not replacing the closure arity word with a forwarding pointer
    // to the new location on the heap! copying over unnecessary tuples. why?
    // because this is giving us a segfault even though the addresses look right.
    // addr[0] = (int)((void *)heap_top + 1);

    // increment heap_top as needed to record the allocation
    // heap_top = &heap_top[len + padding + 2];

    // return heap_top;
  }
  else {
    // garter_val is a primitive (number or boolean),
    // so just return the unchanged heap_top
    return heap_top;
  }
}

/*
  Prints the stack

  bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
  cur_base_ptr (EBP): the base pointer of the topmost Garter stack frame
  cur_stack_ptr (ESP): the current stack pointer of the topmost Garter stack frame
*/
void print_stack_gc(int* bottom_frame, int* cur_base_ptr, int* cur_stack_ptr) {
  fprintf(stdout, "start of print_stack_gc\n");
  for (int* cur_word = cur_stack_ptr /* maybe need a +1 here? */; cur_word < cur_base_ptr; cur_word++) {
    printf("address: %x\tvalue in hex: %x\tvalue from print: ", (uint)cur_word, (uint)*cur_word);
    print(*cur_word);
    printf("\n");
  }
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
int* gc(int* bottom_frame, int* top_frame, int* top_stack, int* from_start, int* from_end, int* to_start) {
  for (int* cur_word = top_stack /* maybe need a +1 here? */; cur_word < top_frame; cur_word++) {
    to_start = copy_if_needed(cur_word, to_start);
  }
  // printf("top_frame: %x\tbottom_frame: %x\n")
  if (top_frame < bottom_frame)
    to_start = gc(bottom_frame,
                  (int*)(*top_frame), // [top_frame] points to the saved EBP, which is the next stack frame
                  top_frame + 2,      // [top_frame+4] points to the return address
                                      // so [top_frame+8] is the next frame's stack-top
                  from_start,
                  from_end,
                  to_start); // to_start has been changed to include any newly copied data
  // after copying the remaining stack frames, return the new allocation starting point
  return to_start;
}
