use borsh::{BorshDeserialize, BorshSerialize};

#[derive(BorshSerialize, PartialEq, Debug)]
struct StructWithSlices<'a> {
    x: u64,
    y: &'a [u8],
    c: &'a str,
    other: u64,
}

#[test]
fn test_simple() {
    let s = StructWithSlices {
        x: 8,
        y: b"test",
        c: "other",
        other: 7,
    };

    let buffer = s.try_to_vec().unwrap();

    let buf = &mut buffer.as_slice();

    // Just doing manually because derive is borked
    let x = u64::deserialize_ref(buf).unwrap();
    let y = <&[u8]>::deserialize_ref(buf).unwrap();
    let c = <&str>::deserialize_ref(buf).unwrap();
    let other = <u64>::deserialize_ref(buf).unwrap();
    assert_eq!(s, StructWithSlices { x, y, c, other })
}
