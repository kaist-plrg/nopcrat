use super::*;

#[test]
fn test_param() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) -> i32 {
            *p = if b { 0 } else { 1 };
            *p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_local_write() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x: i32 = 0;
            let p: *mut i32 = &mut x;
            *p = if b { 0 } else { 1 };
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_local_read() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x: i32 = 0;
            let p: *mut i32 = &mut x;
            x = if b { 0 } else { 1 };
            *p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_double_indirection_write() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x: i32 = 0;
            let mut p: *mut i32 = &mut x;
            let q: *mut *mut i32 = &mut p;
            **q = if b { 0 } else { 1 };
            *p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_double_indirection_read() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x: i32 = 0;
            let mut p: *mut i32 = &mut x;
            let q: *mut *mut i32 = &mut p;
            *p = if b { 0 } else { 1 };
            **q
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_strong_update() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x: i32 = 0;
            let mut y: i32 = 0;
            let p: *mut i32 = &mut x;
            let q: *mut i32 = &mut y;
            let r = p;
            *r = 1;
            let r = q;
            *r = 1;
            x + y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![2]);
}

#[test]
fn test_weak_update() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x: i32 = 0;
            let mut y: i32 = 0;
            let p: *mut i32 = &mut x;
            let q: *mut i32 = &mut y;
            let r = if b { p } else { q };
            *r = 1;
            x + y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2]);
}

#[test]
fn test_param_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            (*p).x = if b { 0 } else { 1 };
            (*p).y = if b { 0 } else { 2 };
            (*p).x + (*p).y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_param_struct_ref() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            let q: *mut i32 = &mut (*p).x;
            let r: *mut i32 = &mut (*p).y;
            *q = if b { 0 } else { 1 };
            *r = if b { 0 } else { 2 };
            (*p).x + (*p).y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_param_struct2() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            (*p).x.x = if b { 0 } else { 1 };
            (*p).x.y = if b { 0 } else { 2 };
            (*p).y.x = if b { 0 } else { 3 };
            (*p).y.y = if b { 0 } else { 4 };
            (*p).x.x + (*p).x.y + (*p).y.x + (*p).y.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_struct2_ref() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            let q1: *mut T = &mut (*p).x;
            let q2: *mut T = &mut (*p).y;
            (*q1).x = if b { 0 } else { 1 };
            (*q1).y = if b { 0 } else { 2 };
            (*q2).x = if b { 0 } else { 3 };
            (*q2).y = if b { 0 } else { 4 };
            (*p).x.x + (*p).x.y + (*p).y.x + (*p).y.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_struct2_ref2() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            let q1: *mut T = &mut (*p).x;
            let q2: *mut T = &mut (*p).y;
            let r1: *mut i32 = &mut (*q1).x;
            let r2: *mut i32 = &mut (*q1).y;
            let r3: *mut i32 = &mut (*q2).x;
            let r4: *mut i32 = &mut (*q2).y;
            *r1 = if b { 0 } else { 1 };
            *r2 = if b { 0 } else { 2 };
            *r3 = if b { 0 } else { 3 };
            *r4 = if b { 0 } else { 4 };
            (*p).x.x + (*p).x.y + (*p).y.x + (*p).y.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_struct_weak_update() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool) -> i32 {
            let mut x: S = S { x: 0, y: 0 };
            let p: *mut i32 = &mut x.x;
            let q: *mut i32 = &mut x.y;
            let r = if b { p } else { q };
            *r = 1;
            x.x + x.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2]);
}

#[test]
fn test_param_array() {
    let code = "
        unsafe fn f(b: bool, p: *mut [i32; 2]) -> i32 {
            (*p)[0] = if b { 0 } else { 1 };
            (*p)[1] = if b { 0 } else { 2 };
            (*p)[0] + (*p)[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_param_array_ref() {
    let code = "
        unsafe fn f(b: bool, p: *mut [i32; 2]) -> i32 {
            let q: *mut i32 = &mut (*p)[0];
            let r: *mut i32 = &mut (*p)[1];
            *q = if b { 0 } else { 1 };
            *r = if b { 0 } else { 2 };
            (*p)[0] + (*p)[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_param_array2() {
    let code = "
        unsafe fn f(b: bool, p: *mut [[i32; 2]; 2]) -> i32 {
            (*p)[0][0] = if b { 0 } else { 1 };
            (*p)[0][1] = if b { 0 } else { 2 };
            (*p)[1][0] = if b { 0 } else { 3 };
            (*p)[1][1] = if b { 0 } else { 4 };
            (*p)[0][0] + (*p)[0][1] + (*p)[1][0] + (*p)[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_array2_ref() {
    let code = "
        unsafe fn f(b: bool, p: *mut [[i32; 2]; 2]) -> i32 {
            let q1: *mut [i32; 2] = &mut (*p)[0];
            let q2: *mut [i32; 2] = &mut (*p)[1];
            (*q1)[0] = if b { 0 } else { 1 };
            (*q1)[1] = if b { 0 } else { 2 };
            (*q2)[0] = if b { 0 } else { 3 };
            (*q2)[1] = if b { 0 } else { 4 };
            (*p)[0][0] + (*p)[0][1] + (*p)[1][0] + (*p)[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_array2_ref2() {
    let code = "
        unsafe fn f(b: bool, p: *mut [[i32; 2]; 2]) -> i32 {
            let q1: *mut [i32; 2] = &mut (*p)[0];
            let q2: *mut [i32; 2] = &mut (*p)[1];
            let r1: *mut i32 = &mut (*q1)[0];
            let r2: *mut i32 = &mut (*q1)[1];
            let r3: *mut i32 = &mut (*q2)[0];
            let r4: *mut i32 = &mut (*q2)[1];
            *r1 = if b { 0 } else { 1 };
            *r2 = if b { 0 } else { 2 };
            *r3 = if b { 0 } else { 3 };
            *r4 = if b { 0 } else { 4 };
            (*p)[0][0] + (*p)[0][1] + (*p)[1][0] + (*p)[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_struct_array() {
    let code = "
        struct S { x: [i32; 2], y: [i32; 2] }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            (*p).x[0] = if b { 0 } else { 1 };
            (*p).x[1] = if b { 0 } else { 2 };
            (*p).y[0] = if b { 0 } else { 3 };
            (*p).y[1] = if b { 0 } else { 4 };
            (*p).x[0] + (*p).x[1] + (*p).y[0] + (*p).y[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_struct_array_ref() {
    let code = "
        struct S { x: [i32; 2], y: [i32; 2] }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            let q1: *mut [i32; 2] = &mut (*p).x;
            let q2: *mut [i32; 2] = &mut (*p).y;
            (*q1)[0] = if b { 0 } else { 1 };
            (*q1)[1] = if b { 0 } else { 2 };
            (*q2)[0] = if b { 0 } else { 3 };
            (*q2)[1] = if b { 0 } else { 4 };
            (*p).x[0] + (*p).x[1] + (*p).y[0] + (*p).y[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_struct_array_ref2() {
    let code = "
        struct S { x: [i32; 2], y: [i32; 2] }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            let q1: *mut [i32; 2] = &mut (*p).x;
            let q2: *mut [i32; 2] = &mut (*p).y;
            let r1: *mut i32 = &mut (*q1)[0];
            let r2: *mut i32 = &mut (*q1)[1];
            let r3: *mut i32 = &mut (*q2)[0];
            let r4: *mut i32 = &mut (*q2)[1];
            *r1 = if b { 0 } else { 1 };
            *r2 = if b { 0 } else { 2 };
            *r3 = if b { 0 } else { 3 };
            *r4 = if b { 0 } else { 4 };
            (*p).x[0] + (*p).x[1] + (*p).y[0] + (*p).y[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_array_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut [S; 2]) -> i32 {
            (*p)[0].x = if b { 0 } else { 1 };
            (*p)[1].x = if b { 0 } else { 2 };
            (*p)[0].y = if b { 0 } else { 3 };
            (*p)[1].y = if b { 0 } else { 4 };
            (*p)[0].x + (*p)[0].y + (*p)[1].x + (*p)[1].y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_array_struct_ref() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut [S; 2]) -> i32 {
            let q1: *mut S = &mut (*p)[0];
            let q2: *mut S = &mut (*p)[1];
            (*q1).x = if b { 0 } else { 1 };
            (*q1).y = if b { 0 } else { 2 };
            (*q2).x = if b { 0 } else { 3 };
            (*q2).y = if b { 0 } else { 4 };
            (*p)[0].x + (*p)[0].y + (*p)[1].x + (*p)[1].y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_param_array_struct_ref2() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut [S; 2]) -> i32 {
            let q1: *mut S = &mut (*p)[0];
            let q2: *mut S = &mut (*p)[1];
            let r1: *mut i32 = &mut (*q1).x;
            let r2: *mut i32 = &mut (*q1).y;
            let r3: *mut i32 = &mut (*q2).x;
            let r4: *mut i32 = &mut (*q2).y;
            *r1 = if b { 0 } else { 1 };
            *r2 = if b { 0 } else { 2 };
            *r3 = if b { 0 } else { 3 };
            *r4 = if b { 0 } else { 4 };
            (*p)[0].x + (*p)[0].y + (*p)[1].x + (*p)[1].y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_null() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x = 0;
            let p: *mut i32 = if b { &mut x } else { 0 as *mut i32 };
            *p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0]);
}

#[test]
fn test_is_null_null() {
    let code = "
        unsafe fn f(mut p: *mut i32) -> i32 {
            p = 0 as *mut i32;
            let mut x = 0;
            if !p.is_null() {
                x = 1;
            }
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0]);
}

#[test]
fn test_is_null_param() {
    let code = "
        unsafe fn f(p: *mut i32) -> i32 {
            let mut x = 0;
            if !p.is_null() {
                x = 1;
            }
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_malloc() {
    let code = "
        extern crate libc;
        extern \"C\" {
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
        }
        unsafe fn f(b: bool) -> i32 {
            let p = malloc(4) as *mut i32;
            *p = if b { 0 } else { 1 };
            *p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert!(ret(&result[0]).is_top());
}

#[test]
fn test_literal() {
    let code = "
        unsafe fn f(b: bool) -> u8 {
            let str = b\".\\0\" as *const u8;
            *str
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert!(ret(&result[0]).uintv.is_top());
}

#[test]
fn test_volatile_write() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x: i32 = 0;
            let p: *mut i32 = &mut x;
            std::ptr::write_volatile(p, if b { 0 } else { 1 });
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_eq() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32) -> i32 {
            if p == q {
                0
            } else {
                1
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_lt() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32) -> i32 {
            if p < q {
                0
            } else {
                1
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_le() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32) -> i32 {
            if p <= q {
                0
            } else {
                1
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_ne() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32) -> i32 {
            if p != q {
                0
            } else {
                1
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_gt() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32) -> i32 {
            if p > q {
                0
            } else {
                1
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_ge() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32) -> i32 {
            if p >= q {
                0
            } else {
                1
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}
