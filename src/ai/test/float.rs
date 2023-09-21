use super::*;

#[test]
fn test_add() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: f32 = if b { 0.0 } else { 1.0 };
            let y: f32 = if b { 0.0 } else { 2.0 };
            x + y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![0.0, 1.0, 2.0, 3.0]);
}

#[test]
fn test_sub() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: f32 = if b { 1.0 } else { 3.0 };
            let y: f32 = if b { 0.0 } else { 1.0 };
            x - y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![0.0, 1.0, 2.0, 3.0]);
}

#[test]
fn test_mul() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: f32 = if b { 1.0 } else { 2.0 };
            let y: f32 = if b { 1.0 } else { 3.0 };
            x * y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![1.0, 2.0, 3.0, 6.0]);
}

#[test]
fn test_div() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: f32 = if b { 3.0 } else { 6.0 };
            let y: f32 = if b { 1.0 } else { 3.0 };
            x / y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![1.0, 2.0, 3.0, 6.0]);
}

#[test]
fn test_rem() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: f32 = if b { 7.0 } else { 8.0 };
            let y: f32 = if b { 2.0 } else { 5.0 };
            x % y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![0.0, 1.0, 2.0, 3.0]);
}

#[test]
fn test_eq() {
    let code = "
        fn f(b: bool) -> bool {
            let x: f32 = if b { 0.0 } else { 1.0 };
            let y: f32 = if b { 0.0 } else { 1.0 };
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
            let x: f32 = if b { 0.0 } else { 1.0 };
            let y: f32 = if b { 0.0 } else { 1.0 };
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
            let x: f32 = if b { 0.0 } else { 1.0 };
            let y: f32 = if b { 0.0 } else { 1.0 };
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
            let x: f32 = if b { 0.0 } else { 1.0 };
            let y: f32 = if b { 0.0 } else { 1.0 };
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
            let x: f32 = if b { 0.0 } else { 1.0 };
            let y: f32 = if b { 0.0 } else { 1.0 };
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
            let x: f32 = if b { 0.0 } else { 1.0 };
            let y: f32 = if b { 0.0 } else { 1.0 };
            x >= y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_bool(ret(&result[0])), vec![true, false]);
}

#[test]
fn test_neg() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: f32 = if b { 0.0 } else { 1.0 };
            -x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![-0.0, -1.0]);
}
