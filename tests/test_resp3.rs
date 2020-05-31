use trustee::resp3;

#[test]
fn test_simple1() {
    use resp3::SimpleMsg;

    let m = SimpleMsg::Array(vec![SimpleMsg::Int(42), SimpleMsg::Bool(true)]);
    let b = m.ser_to_bytes().unwrap();

    assert_eq!("*2\r\n:42\r\n#t\r\n", std::str::from_utf8(&b).unwrap());
}

#[test]
fn test_simple2() {
    use resp3::SimpleMsg as M;
    let m = M::Array(vec![
        M::Map(vec![
            (M::Str("a".to_string()), M::Int(1)),
            (M::Str("b".to_string()), M::Int(2)),
        ]),
        M::Bool(false),
        M::Array(vec![M::Int(4), M::Int(5), M::Int(6)]),
    ]);
    let b = m.ser_to_bytes().unwrap();
    assert_eq!(
        "*3\r\n%2\r\n+a\r\n:1\r\n+b\r\n:2\r\n#f\r\n*3\r\n:4\r\n:5\r\n:6\r\n",
        std::str::from_utf8(&b).unwrap()
    );
}

// TODO
