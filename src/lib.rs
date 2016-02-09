//! This crate provides utilities for working with NULL-terminated linked lists provided
//! by C code. Suppose you call a foreign function which returns either NULL or a pointer
//! to a node of the following C type.
//!
//! ```c
//! struct LinkedListNode {
//!     int value;
//!     struct LinkedListNode *next;
//! };
//! ```
//!
//! You can use this library to wrap the C linked list in a rust type, allowing
//! operations such as iteration to be performed on it.
//!
//! ```ignore
//! let some_c_linked_list = foreign_function_which_returns_c_linked_list();
//! let rust_linked_list = unsafe { CLinkedListMut::from_ptr(some_c_linked_list, |n| n.next) };
//! for (i, node) in rust_linked_list.iter().enumerate() {
//!     println!("some_c_linked_list[{}] == {}", i, node.value);
//! }
//! ```

use std::fmt;

/// Wraps a C linked list comprised of mutable pointers between nodes.
pub struct CLinkedListMut<T, N: Fn(&T) -> *mut T> {
    head: *mut T,
    next: N,
}

/// Iterator over a `CLinkedListMut`. Returns references to the nodes of the list.
pub struct CLinkedListMutIter<'a, T: 'a, N: Fn(&T) -> *mut T + 'a> {
    cll: &'a CLinkedListMut<T, N>,
    prev: Option<&'a T>,
}

/// Iterator over a `CLinkedListMut`. Returns mutable references to the nodes of the list.
pub struct CLinkedListMutIterMut<'a, T: 'a, N: Fn(&T) -> *mut T + 'a> {
    cll: &'a mut CLinkedListMut<T, N>,
    prev: Option<&'a mut T>,
}

impl<'a, T: 'a, N: Fn(&T) -> *mut T + 'a> CLinkedListMut<T, N> {
    /// Construct a `CLinkedListMut` by wrapping a C linked list. `head` points to the head element
    /// of the list or is NULL for a list of length 0. `next` is a function that takes a node and
    /// returns a pointer to the next element.
    ///
    /// # Example
    ///
    /// To wrap this C type.
    ///
    /// ```c
    /// struct LinkedListNode {
    ///     int value;
    ///     struct LinkedListNode *next;
    /// };
    /// ```
    ///
    /// Call this function as `CLinkedListMut::from_ptr(ptr_to_head, |n| n.next)`.
    ///
    /// # Unsafety
    ///
    /// This function is unsafe because it is up to the caller to ensure that `head` is valid.
    pub unsafe fn from_ptr(head: *mut T, next: N) -> CLinkedListMut<T, N> {
        CLinkedListMut {
            head: head,
            next: next,
        }
    }

    /// Iterate over the linked list, returning references to the nodes of the list.
    pub fn iter(&'a self) -> CLinkedListMutIter<'a, T, N> {
        CLinkedListMutIter {
            cll: self,
            prev: None,
        }
    }

    /// Iterate over the linked list, returning mutable references to the nodes of the list.
    pub fn iter_mut(&'a mut self) -> CLinkedListMutIterMut<'a, T, N> {
        CLinkedListMutIterMut {
            cll: self,
            prev: None,
        }
    }

    /// Returns `true` if the list is empty.
    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    /// Calculates the length of the list. This is an `O(n)` operation.
    pub fn len(&self) -> usize {
        let mut node = self.head;
        let mut ret = 0;
        while !node.is_null() {
            node = unsafe { (self.next)(&mut *node) };
            ret += 1;
        }
        ret
    }

    /// Provides a reference to the front element in the list, or `None` if the list is empty.
    pub fn front(&self) -> Option<&T> {
        if self.head.is_null() {
            None
        }
        else {
            unsafe { Some(&*self.head) }
        }
    }

    /// Provides a mutable reference to the front element in the list, or `None` if the list is
    /// empty.
    pub fn front_mut(&self) -> Option<&mut T> {
        if self.head.is_null() {
            None
        }
        else {
            unsafe { Some(&mut *self.head) }
        }
    }
}

impl<'a, T: 'a, N: Fn(&T) -> *mut T + 'a> IntoIterator for &'a CLinkedListMut<T, N> {
    type Item = &'a T;
    type IntoIter = CLinkedListMutIter<'a, T, N>;

    fn into_iter(self) -> CLinkedListMutIter<'a, T, N> {
        self.iter()
    }
}

impl<'a, T: 'a, N: Fn(&T) -> *mut T + 'a> IntoIterator for &'a mut CLinkedListMut<T, N> {
    type Item = &'a mut T;
    type IntoIter = CLinkedListMutIterMut<'a, T, N>;

    fn into_iter(mut self) -> CLinkedListMutIterMut<'a, T, N> {
        self.iter_mut()
    }
}

impl<'a, T: 'a, N: Fn(&T) -> *mut T + 'a> Iterator for CLinkedListMutIter<'a, T, N> {
    type Item = &'a T;

    #[allow(unsafe_code)]
    fn next(&mut self) -> Option<&'a T> {
        // Note: implemented this way so that if the user changes the next pointer during iteration
        // it will iterate to the correct next element.
        let next = match self.prev {
            None => self.cll.head,
            Some(ref mut prev) => (self.cll.next)(*prev),
        };
        if next.is_null() {
            None
        }
        else {
            self.prev = Some(unsafe { &*next });
            Some(unsafe { &*next })
        }
    }
}

impl<'a, T: 'a, N: Fn(&T) -> *mut T + 'a> Iterator for CLinkedListMutIterMut<'a, T, N> {
    type Item = &'a mut T;

    #[allow(unsafe_code)]
    fn next(&mut self) -> Option<&'a mut T> {
        // Note: implemented this way so that if the user changes the next pointer during iteration
        // it will iterate to the correct next element.
        let next = match self.prev {
            None => self.cll.head,
            Some(ref mut prev) => (self.cll.next)(*prev),
        };
        if next.is_null() {
            None
        }
        else {
            self.prev = Some(unsafe { &mut *next });
            Some(unsafe { &mut *next })
        }
    }
}

impl<'a, T: fmt::Debug + 'a, N: Fn(&T) -> *mut T + 'a> fmt::Debug for CLinkedListMut<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Wraps a C linked list comprised of const pointers between nodes.
pub struct CLinkedListConst<T, N: Fn(&T) -> *const T> {
    head: *const T,
    next: N,
}

/// Iterator over a `CLinkedListConst`. Returns immutable references to the nodes of the list.
pub struct CLinkedListConstIter<'a, T: 'a, N: Fn(&T) -> *const T + 'a> {
    cll: &'a CLinkedListConst<T, N>,
    prev: Option<&'a T>,
}

impl<'a, T: 'a, N: Fn(&T) -> *const T + 'a> CLinkedListConst<T, N> {
    /// Construct a `CLinkedListConst` by wrapping a C linked list. `head` points to the head
    /// element of the list or is NULL for a list of length 0. `next` is a function that takes a
    /// node and returns a pointer to the next element.
    ///
    /// # Example
    ///
    /// To wrap this C type.
    ///
    /// ```c
    /// struct LinkedListNode {
    ///     int value;
    ///     const struct LinkedListNode *next;
    /// };
    /// ```
    ///
    /// Call this function as `CLinkedListConst::from_ptr(ptr_to_head, |n| n.next)`.
    ///
    /// # Unsafety
    ///
    /// This function is unsafe because it is up to the caller to ensure that `head` is valid.
    pub unsafe fn from_ptr(head: *const T, next: N) -> CLinkedListConst<T, N> {
        CLinkedListConst {
            head: head,
            next: next,
        }
    }

    /// Iterate over the linked list, returning immutable references to the nodes of the list.
    pub fn iter(&'a self) -> CLinkedListConstIter<'a, T, N> {
        CLinkedListConstIter {
            cll: self,
            prev: None,
        }
    }

    /// Returns `true` if the list is empty.
    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    /// Calculates the length of the list. This is an `O(n)` operation.
    pub fn len(&self) -> usize {
        let mut node = self.head;
        let mut ret = 0;
        while !node.is_null() {
            node = unsafe { (self.next)(&*node) };
            ret += 1;
        }
        ret
    }

    /// Provides a reference to the front element in the list, or `None` if the list is empty.
    pub fn front(&self) -> Option<&T> {
        if self.head.is_null() {
            None
        }
        else {
            unsafe { Some(&*self.head) }
        }
    }
}

impl<'a, T: 'a, N: Fn(&T) -> *const T + 'a> IntoIterator for &'a CLinkedListConst<T, N> {
    type Item = &'a T;
    type IntoIter = CLinkedListConstIter<'a, T, N>;

    fn into_iter(self) -> CLinkedListConstIter<'a, T, N> {
        self.iter()
    }
}

impl<'a, T: 'a, N: Fn(&T) -> *const T + 'a> Iterator for CLinkedListConstIter<'a, T, N> {
    type Item = &'a T;

    #[allow(unsafe_code)]
    fn next(&mut self) -> Option<&'a T> {
        // Note: implemented this way so that if the user changes the next pointer during iteration
        // it will iterate to the correct next element.
        let next = match self.prev {
            None => self.cll.head,
            Some(prev) => (self.cll.next)(prev),
        };
        if next.is_null() {
            None
        }
        else {
            self.prev = Some(unsafe { &*next });
            self.prev
        }
    }
}

impl<'a, T: fmt::Debug + 'a, N: Fn(&T) -> *const T + 'a> fmt::Debug for CLinkedListConst<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests{
    use super::*;

    use std;

    struct TestNodeConst {
        val: u32,
        next: *const TestNodeConst,
    }

    fn make_list_const() -> *const TestNodeConst {
        fn malloc<T>(t: T) -> *const T {
            Box::into_raw(Box::new(t)) as *const T
        }

        malloc(TestNodeConst {
            val: 0,
            next: malloc(TestNodeConst {
                val: 1,
                next: malloc(TestNodeConst {
                    val: 2,
                    next: std::ptr::null(),
                }),
            }),
        })
    }

    #[test]
    fn test_const() {
        let ptr: *const TestNodeConst = std::ptr::null();
        let list = unsafe { CLinkedListConst::from_ptr(ptr, |n| n.next) };
        let vec: Vec<u32> = list.iter().map(|n| n.val).collect();
        assert_eq!(vec, &[]);
        assert_eq!(list.len(), 0);
        assert!(list.is_empty());
        assert!(list.front().is_none());

        let ptr = make_list_const();
        let list = unsafe { CLinkedListConst::from_ptr(ptr, |n| n.next) };
        let vec: Vec<u32> = list.iter().map(|n| n.val).collect();
        assert_eq!(vec, &[0, 1, 2]);
        assert_eq!(list.len(), 3);
        assert!(! list.is_empty());
        let front = list.front().unwrap();
        assert_eq!(front.val, 0);
    }

    struct TestNodeMut {
        val: u32,
        next: *mut TestNodeMut,
    }

    fn make_list_mut() -> *mut TestNodeMut {
        fn malloc<T>(t: T) -> *mut T {
            Box::into_raw(Box::new(t))
        }

        malloc(TestNodeMut {
            val: 0,
            next: malloc(TestNodeMut {
                val: 1,
                next: malloc(TestNodeMut {
                    val: 2,
                    next: std::ptr::null_mut(),
                }),
            }),
        })
    }

    #[test]
    fn test_mut() {
        let ptr: *mut TestNodeMut = std::ptr::null_mut();
        let list = unsafe { CLinkedListMut::from_ptr(ptr, |n| n.next) };
        let vec: Vec<u32> = list.iter().map(|n| n.val).collect();
        assert_eq!(vec, &[]);
        assert_eq!(list.len(), 0);
        assert!(list.is_empty());
        assert!(list.front().is_none());

        let ptr = make_list_mut();
        let mut list = unsafe { CLinkedListMut::from_ptr(ptr, |n| n.next) };
        let vec: Vec<u32> = list.iter().map(|n| n.val).collect();
        assert_eq!(vec, &[0, 1, 2]);
        assert_eq!(list.len(), 3);
        assert!(! list.is_empty());
        {
            let front = list.front().unwrap();
            assert_eq!(front.val, 0);
        }

        for node in list.iter_mut() {
            node.val += 1;
        }

        let vec: Vec<u32> = list.iter().map(|n| n.val).collect();
        assert_eq!(vec, &[1, 2, 3]);
        assert_eq!(list.len(), 3);
        assert!(! list.is_empty());
        let front = list.front().unwrap();
        assert_eq!(front.val, 1);
    }
}


