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
//! let rust_linked_list = CLinkedListMut::from_ptr(some_c_linked_list, |n| n.next);
//! for (i, node) in rust_linked_list.iter().enumerate() {
//!     println!("some_c_linked_list[{}] == {}", i, node.value);
//! }
//! ```

/// Wraps a C linked list comprised of mutable pointers between nodes.
pub struct CLinkedListMut<T, N: FnMut(&mut T) -> *mut T> {
    head: *mut T,
    next: N,
}

/// Iterator over a `CLinkedListMut`. Returns mutable references to the nodes of the list.
pub struct CLinkedListMutIter<'a, T: 'a, N: FnMut(&mut T) -> *mut T + 'a> {
    cll: &'a mut CLinkedListMut<T, N>,
    prev: Option<&'a mut T>,
}

impl<'a, T: 'a, N: FnMut(&mut T) -> *mut T + 'a> CLinkedListMut<T, N> {
    /// Construct a `CLinkedListMut` by wrapping a C linked list. `head` points to the head element
    /// of the list and can be NULL for a list of length 0. `next` is a function that takes a node
    /// and returns a pointer to the next element.
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
    pub fn from_ptr(head: *mut T, next: N) -> CLinkedListMut<T, N> {
        CLinkedListMut {
            head: head,
            next: next,
        }
    }

    /// Iterate over the linked list, returning mutable references to the nodes of the list.
    pub fn iter(&'a mut self) -> CLinkedListMutIter<'a, T, N> {
        CLinkedListMutIter {
            cll: self,
            prev: None,
        }
    }
}

impl<'a, T: 'a, N: FnMut(&mut T) -> *mut T + 'a> Iterator for CLinkedListMutIter<'a, T, N> {
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

/// Wraps a C linked list comprised of const pointers between nodes.
pub struct CLinkedListConst<T, N: FnMut(&T) -> *const T> {
    head: *const T,
    next: N,
}

/// Iterator over a `CLinkedListConst`. Returns immutable references to the nodes of the list.
pub struct CLinkedListConstIter<'a, T: 'a, N: FnMut(&T) -> *const T + 'a> {
    cll: &'a mut CLinkedListConst<T, N>,
    prev: Option<&'a T>,
}

impl<'a, T: 'a, N: FnMut(&T) -> *const T + 'a> CLinkedListConst<T, N> {
    /// Construct a `CLinkedListConst` by wrapping a C linked list. `head` points to the head element
    /// of the list and can be NULL for a list of length 0. `next` is a function that takes a node
    /// and returns a pointer to the next element.
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
    pub fn from_ptr(head: *const T, next: N) -> CLinkedListConst<T, N> {
        CLinkedListConst {
            head: head,
            next: next,
        }
    }

    /// Iterate over the linked list, returning immutable references to the nodes of the list.
    pub fn iter(&'a mut self) -> CLinkedListConstIter<'a, T, N> {
        CLinkedListConstIter {
            cll: self,
            prev: None,
        }
    }
}

impl<'a, T: 'a, N: FnMut(&T) -> *const T + 'a> Iterator for CLinkedListConstIter<'a, T, N> {
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

