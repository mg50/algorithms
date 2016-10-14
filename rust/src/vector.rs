// use std::mem;

// struct Vector<T> {
//     len: usize,
//     cap: usize,
//     ary: [T]
// }


// impl <T> Vector<T> {
//     fn get(&self, idx: usize) -> Option<&T> {
//         if idx < 0 || idx >= self.len { None }
//         else {
//             let ary = &self.ary;
//             Some(&self.ary[idx])
//         }
//     }

//     pub fn set(&mut self, idx: usize, elem: T) {
//         self.ary[idx] = elem
//     }

//     fn length(&self) -> usize {
//         self.len
//     }

//     fn push(&mut self, elem: T) {
//         if self.len < self.cap {
//             self.ary[self.len] = elem;
//             self.len += 1;
//         } else {
//             let new_cap: usize = 2*self.cap;
// //            let blah: [u32; new_cap];
//             unsafe {
// //                let new_ary: [T; new_cap] = mem::uninitialized();
//             }
// //            let new_ary: [u32; 1] = [1];
//         }
//     }

// }


// // #[cfg(test)]
// // mod tests {
// //     #[test]
// //     fn it_works() {
// //         println!("hello");
// //     }
// // }
