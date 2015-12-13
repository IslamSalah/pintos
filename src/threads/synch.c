/* This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */

/* Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
*/

#include "threads/synch.h"
#include <stdio.h>
#include <string.h>
#include "threads/interrupt.h"
#include "threads/thread.h"
#include "lib/float.h"

/* Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
     decrement it.

   - up or "V": increment the value (and wake up one waiting
     thread, if any). */
void
sema_init (struct semaphore *sema, unsigned value) 
{
  ASSERT (sema != NULL);

  sema->value = value;
  list_init (&sema->waiters);
}

/* Down or "P" operation on a semaphore.  Waits for SEMA's value
   to become positive and then atomically decrements it.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but if it sleeps then the next scheduled
   thread will probably turn interrupts back on. */
void
sema_down (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  while (sema->value == 0) 
    {
      list_push_back (&sema->waiters, &thread_current ()->elem);
      thread_block ();
    }
  sema->value--;
  intr_set_level (old_level);
}

/* Down or "P" operation on a semaphore, but only if the
   semaphore is not already 0.  Returns true if the semaphore is
   decremented, false otherwise.

   This function may be called from an interrupt handler. */
bool
sema_try_down (struct semaphore *sema) 
{
  enum intr_level old_level;
  bool success;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (sema->value > 0) 
    {
      sema->value--;
      success = true; 
    }
  else
    success = false;
  intr_set_level (old_level);

  return success;
}

/* Up or "V" operation on a semaphore.  Increments SEMA's value
   and wakes up one thread of those waiting for SEMA, if any.

   This function may be called from an interrupt handler. */
void
sema_up (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (!list_empty (&sema->waiters)) {
		struct list_elem *e = list_max (&sema->waiters, &compare_func, 0);
		list_remove (e);
		sema->value++;				//this allows the the first semup to work correctly 
    thread_unblock (list_entry (e, struct thread, elem));
  }
  else
		sema->value++;
  
  intr_set_level (old_level);
}

static void sema_test_helper (void *sema_);

/* Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */
void
sema_self_test (void) 
{
  struct semaphore sema[2];
  int i;

  printf ("Testing semaphores...");
  sema_init (&sema[0], 0);
  sema_init (&sema[1], 0);
  thread_create ("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
  for (i = 0; i < 10; i++) 
    {
      sema_up (&sema[0]);
      sema_down (&sema[1]);
    }
  printf ("done.\n");
}

/* Thread function used by sema_self_test(). */
static void
sema_test_helper (void *sema_) 
{
  struct semaphore *sema = sema_;
  int i;

  for (i = 0; i < 10; i++) 
    {
      sema_down (&sema[0]);
      sema_up (&sema[1]);
    }
}

/* Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */
void
lock_init (struct lock *lock)
{
  ASSERT (lock != NULL);
	lock->mx_priority= -1;
  lock->holder = NULL;
  sema_init (&lock->semaphore, 1);
}

/* Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
lock_acquire (struct lock *lock)
{
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (!lock_held_by_current_thread (lock));
	
	struct thread *holder= lock->holder;
	
	/* If the current lock is already locked, then we update the mx_priority, by comparing it
	 * with the current_thread.
	 * We check if the thread holding the lock has less priority than the current priority so it
	 * donates it priority, then we add the current lock to the list of the thread of the donating_locks. */
	if(holder != NULL){
		if(lock->mx_priority < thread_current()->priority){
			lock->mx_priority= thread_current()->priority;
		}
		
		if(thread_current()->priority > holder->priority){
			if(!list_exist(&holder->donating_locks, &lock->elem)){
				list_push_back(&holder->donating_locks, &lock->elem);
			}
			holder->priority= thread_current()->priority;
		}
		
		thread_current()->blocked=lock;
		nest_donation(holder);
	}
	else{
		list_push_back(&thread_current()->donating_locks, &lock->elem);
	}
	
  sema_down (&lock->semaphore);
  lock->holder = thread_current();
}


/* For nested donations, as it carries the priority of H thread to the lock holder,
 * and checks if the lock holder is blocked on another lock so it will continue the
 * donation to the next lock and updating the priority. */
void
nest_donation(struct thread *cur){
	while(cur->blocked!=NULL &&	cur->blocked->holder->priority < cur->priority){
		struct thread *holder= cur->blocked->holder;
		holder->priority= cur->priority;
		cur->blocked->mx_priority=holder->priority;
		cur= holder;
	}
}

/* Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */
bool
lock_try_acquire (struct lock *lock)
{
  bool success;

  ASSERT (lock != NULL);
  ASSERT (!lock_held_by_current_thread (lock));

  success = sema_try_down (&lock->semaphore);
  if (success){
    lock->holder = thread_current ();
    list_push_back(&thread_current()->donating_locks, &lock->elem);
	}
  return success;
}

/* Comparator function, used to compare 2 locks, according to their mx_priority. */
bool
lock_comparator(const struct list_elem *a,
                          const struct list_elem *b,
                          void *aux){
	struct lock *A = list_entry (a, struct lock, elem);
	struct lock *B = list_entry (b, struct lock, elem);
	return A->mx_priority < B->mx_priority;
	
}

/* Releases LOCK, which must be owned by the current thread.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */

/* Removes the lock from donating locks, then it finds the next priority to be assigned
 * to the releasing thread. */ 
void
lock_release (struct lock *lock) 
{
  ASSERT (lock != NULL);
  ASSERT (lock_held_by_current_thread (lock));
	
	/* Removing the lock from the donating_lists. */
	list_remove(&lock->elem);
	
	
	/* Getting the next max. priority for the lock holder, either one of the locks, or the 
	 * initial priority. */
	struct list_elem *e;
	struct thread *holder= lock->holder;
	
	if(!list_empty(&holder->donating_locks)){
		e = list_max (&holder->donating_locks, &lock_comparator, 0);
		struct lock *mx_lock= list_entry(e, struct lock, elem);
		holder->priority= mx_lock->mx_priority;
	}
	
	if(list_empty(&holder->donating_locks) || holder->priority < holder->initial_priority){
		holder->priority= holder->initial_priority;
	}
  
  /* Setting the mx_priority of the lock, by getting the 2nd maximum as the maximum will
   * hold the lock, and the 2nd maximum will be waiting for the lock. */
  struct list_elem *e_2nd_mx;
  struct list *waiters= &lock->semaphore.waiters;
  
  /* If no waiters then the priority of the lock should be set to -1. */
  if(!list_empty(waiters)){
		/* Removing the maximum from the waiters list to get the 2nd maximum. */
		e= list_max(waiters, &compare_func, 0);
		list_remove(e);
		/* If the list only contains a single element (the maximum element), then
		 * mx_priority should be equal -1, as there is no waiters. */
		if(!list_empty(waiters)){
			e_2nd_mx= list_max(waiters, &compare_func, 0);
			lock->mx_priority= list_entry(e_2nd_mx, struct thread, elem)->priority;
		}
		else 
			lock->mx_priority= -1;
		/* Returning the max. thread, to be picked in the sema_up function to hold the lock. */
		list_push_back(waiters, e);
  }
  else 
		lock->mx_priority= -1;
  
  lock->holder = NULL;
  sema_up (&lock->semaphore);
}

/* Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */
bool
lock_held_by_current_thread (const struct lock *lock) 
{
  ASSERT (lock != NULL);

  return lock->holder == thread_current ();
}


/* One semaphore in a list. */
struct semaphore_elem 
  {
    struct list_elem elem;              /* List element. */
    struct semaphore semaphore;         /* This semaphore. */
  };

/* Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */
void
cond_init (struct condition *cond)
{
  ASSERT (cond != NULL);

  list_init (&cond->waiters);
}

/* Atomically releases LOCK and waits for COND to be signaled by
   some other piece of code.  After COND is signaled, LOCK is
   reacquired before returning.  LOCK must be held before calling
   this function.

   The monitor implemented by this function is "Mesa" style, not
   "Hoare" style, that is, sending and receiving a signal are not
   an atomic operation.  Thus, typically the caller must recheck
   the condition after the wait completes and, if necessary, wait
   again.

   A given condition variable is associated with only a single
   lock, but one lock may be associated with any number of
   condition variables.  That is, there is a one-to-many mapping
   from locks to condition variables.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
cond_wait (struct condition *cond, struct lock *lock) 
{
  struct semaphore_elem waiter;

  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));
  
  sema_init (&waiter.semaphore, 0);
  list_push_back (&cond->waiters, &waiter.elem);
  lock_release (lock);
  sema_down (&waiter.semaphore);
  lock_acquire (lock);
}

/*
 * used to do comparison on threads which is deep inside:
 * 1) cond->waiters is a list of semaphore_elem
 * 2)semaphore_elem contains semaphore
 * 3)semaphore contains waiters list
 * 4)waiters list contains only one thread (which is to be signaled by
 * condVar)
 * */
bool compare_func2(const struct list_elem *a,
                          const struct list_elem *b,
                          void *aux){
	struct semaphore_elem *A = list_entry (a, struct semaphore_elem, elem);
	struct semaphore_elem *B = list_entry (b, struct semaphore_elem, elem);
	
	struct thread *Aa = list_entry (list_front (&(&A->semaphore)->waiters), struct thread, elem);
	struct thread *Bb = list_entry (list_front (&(&B->semaphore)->waiters), struct thread, elem);
	return Aa->priority < Bb->priority;
}

/* If any threads are waiting on COND (protected by LOCK), then
   this function signals one of them to wake up from its wait.
   LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_signal (struct condition *cond, struct lock *lock UNUSED) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));
                          
  if (!list_empty (&cond->waiters)) {
		struct list_elem *e = list_max (&cond->waiters, &compare_func2, 0);
		list_remove (e);
    
    sema_up (&list_entry (e, struct semaphore_elem, elem)->semaphore);
  }          
  
}

/* Wakes up all threads, if any, waiting on COND (protected by
   LOCK).  LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_broadcast (struct condition *cond, struct lock *lock) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);

  while (!list_empty (&cond->waiters))
    cond_signal (cond, lock);
}
