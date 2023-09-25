use super::*;

#[test]
fn test_xor_true() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            let b2 = x > 3;
            b1 ^ b2
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true]);
}

#[test]
fn test_xor_false() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            b1 ^ b1
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![false]);
}

#[test]
fn test_and_true() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            b1 & b1
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true]);
}

#[test]
fn test_and_false() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            let b2 = x > 3;
            b1 & b2
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![false]);
}

#[test]
fn test_or_true() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            let b2 = x > 3;
            b1 | b2
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true]);
}

#[test]
fn test_or_false() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x > 3;
            b1 | b1
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![false]);
}

#[test]
fn test_eq_true() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            b1 == b1
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true]);
}

#[test]
fn test_eq_false() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            let b2 = x > 3;
            b1 == b2
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![false]);
}

#[test]
fn test_ne_true() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            let b2 = x > 3;
            b1 != b2
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true]);
}

#[test]
fn test_ne_false() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            b1 != b1
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![false]);
}

#[test]
fn test_not_true() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x > 3;
            !b1
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true]);
}

#[test]
fn test_not_false() {
    let code = "
        fn f(b: bool) -> bool {
            let x: i32 = if b { 1 } else { 2 };
            let b1 = x < 3;
            !b1
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![false]);
}

#[test]
fn test_if() {
    let code = "
        fn f(b: bool) -> i32 {
            if b { 0 } else { 1 }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_if_true() {
    let code = "
        fn f(b: bool) -> i32 {
            let x = if b { 0 } else { 1 };
            let b1 = x < 3;
            if b1 { 0 } else { 1 }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0]);
}

#[test]
fn test_if_false() {
    let code = "
        fn f(b: bool) -> i32 {
            let x = if b { 0 } else { 1 };
            let b1 = x > 3;
            if b1 { 0 } else { 1 }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}
