use super::*;

#[test]
fn test_i16_i8() {
    let code = "
        fn f(b: bool) -> i8 {
            let x: i16 = if b { 255 } else { 256 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![-1, 0]);
}

#[test]
fn test_u16_u8() {
    let code = "
        fn f(b: bool) -> u8 {
            let x: u16 = if b { 256 } else { 257 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_int_uint() {
    let code = "
        fn f(b: bool) -> u8 {
            let x: i8 = if b { 0 } else { -1 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 255]);
}

#[test]
fn test_uint_int() {
    let code = "
        fn f(b: bool) -> i8 {
            let x: u8 = if b { 0 } else { 255 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![-1, 0]);
}

#[test]
fn test_int_float() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: i32 = if b { 0 } else { 1 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![0.0, 1.0]);
}

#[test]
fn test_uint_float() {
    let code = "
        fn f(b: bool) -> f32 {
            let x: u32 = if b { 0 } else { 1 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_float(ret(&result[0])), vec![0.0, 1.0]);
}

#[test]
fn test_float_int() {
    let code = "
        fn f(b: bool) -> i32 {
            let x: f32 = if b { 0.0 } else { 1.0 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_float_uint() {
    let code = "
        fn f(b: bool) -> u32 {
            let x: f32 = if b { 0.0 } else { 1.0 };
            x as _
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_uint(ret(&result[0])), vec![0, 1]);
}
