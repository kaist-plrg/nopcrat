use super::*;

#[test]
fn test_add() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 0 } else { 1 };
            let y: u32 = if b { 0 } else { 2 };
            x + y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_sub() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 1 } else { 3 };
            let y: u32 = if b { 0 } else { 1 };
            x - y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_mul() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 1 } else { 2 };
            let y: u32 = if b { 1 } else { 3 };
            x * y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![1, 2, 3, 6]);
}

#[test]
fn test_div() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 3 } else { 6 };
            let y: u32 = if b { 1 } else { 3 };
            x / y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![1, 2, 3, 6]);
}

#[test]
fn test_rem() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 7 } else { 8 };
            let y: u32 = if b { 2 } else { 5 };
            x % y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_xor() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 1 } else { 3 };
            let y: u32 = if b { 2 } else { 4 };
            x ^ y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![1, 3, 5, 7]);
}

#[test]
fn test_and() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 5 } else { 4 };
            let y: u32 = if b { 3 } else { 7 };
            x & y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 1, 4, 5]);
}

#[test]
fn test_or() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 1 } else { 6 };
            let y: u32 = if b { 7 } else { 2 };
            x & y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 1, 2, 6]);
}

#[test]
fn test_shl() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 1 } else { 3 };
            let y: u32 = if b { 0 } else { 1 };
            x << y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![1, 2, 3, 6]);
}

#[test]
fn test_shr() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: u32 = if b { 2 } else { 6 };
            let y: u32 = if b { 0 } else { 1 };
            x >> y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![1, 2, 3, 6]);
}

#[test]
fn test_eq() {
    let code = "
        fn f(b: bool) -> bool {
            let x: u32 = if b { 0 } else { 1 };
            let y: u32 = if b { 0 } else { 1 };
            x == y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true, false]);
}

#[test]
fn test_lt() {
    let code = "
        fn f(b: bool) -> bool {
            let x: u32 = if b { 0 } else { 1 };
            let y: u32 = if b { 0 } else { 1 };
            x < y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true, false]);
}

#[test]
fn test_le() {
    let code = "
        fn f(b: bool) -> bool {
            let x: u32 = if b { 0 } else { 1 };
            let y: u32 = if b { 0 } else { 1 };
            x <= y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true, false]);
}

#[test]
fn test_ne() {
    let code = "
        fn f(b: bool) -> bool {
            let x: u32 = if b { 0 } else { 1 };
            let y: u32 = if b { 0 } else { 1 };
            x != y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true, false]);
}

#[test]
fn test_gt() {
    let code = "
        fn f(b: bool) -> bool {
            let x: u32 = if b { 0 } else { 1 };
            let y: u32 = if b { 0 } else { 1 };
            x > y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true, false]);
}

#[test]
fn test_ge() {
    let code = "
        fn f(b: bool) -> bool {
            let x: u32 = if b { 0 } else { 1 };
            let y: u32 = if b { 0 } else { 1 };
            x >= y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true, false]);
}

#[test]
fn test_not() {
    let code = "
        fn f(b: bool) -> u128 {
            let x: u128 = if b { 0 } else { 1 };
            !x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![u128::MAX - 1, u128::MAX]);
}

#[test]
fn test_const() {
    let code = "
        const X: u32 = 0;
        fn f() -> u32 {
            X
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0]);
}

#[test]
fn test_static() {
    let code = "
        static mut X: u32 = 0;
        static mut Y: u32 = 0;
        fn f() -> u32 {
            X = 1;
            Y = 2;
            X + Y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![3]);
}
