use core::marker::PhantomData;
use core::{
    convert::{TryFrom, TryInto},
    hash::{BuildHasher, Hash},
    mem::{forget, size_of},
};

use crate::maybestd::{
    borrow::{Borrow, Cow, ToOwned},
    boxed::Box,
    collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque},
    format,
    io::{Error, ErrorKind, Result},
    string::{String, ToString},
    vec,
    vec::Vec,
};

#[cfg(feature = "rc")]
use crate::maybestd::{rc::Rc, sync::Arc};

mod hint;

const ERROR_NOT_ALL_BYTES_READ: &str = "Not all bytes read";
const ERROR_UNEXPECTED_LENGTH_OF_INPUT: &str = "Unexpected length of input";
const ERROR_OVERFLOW_ON_MACHINE_WITH_32_BIT_USIZE: &str = "Overflow on machine with 32 bit usize";
const ERROR_INVALID_ZERO_VALUE: &str = "Expected a non-zero value";

/// A data-structure that can be de-serialized from binary format by NBOR.
pub trait BorshDeserialize<'de>: Sized {
    /// Deserializes this instance from a given slice of bytes.
    /// Updates the buffer to point at the remaining bytes.
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self>;

    /// Deserialize this instance from a slice of bytes.
    fn try_from_slice(v: &'de [u8]) -> Result<Self> {
        let mut v_mut = v;
        let result = Self::deserialize(&mut v_mut)?;
        if !v_mut.is_empty() {
            return Err(Error::new(ErrorKind::InvalidData, ERROR_NOT_ALL_BYTES_READ));
        }
        Ok(result)
    }

    #[inline]
    #[doc(hidden)]
    fn vec_from_bytes(len: u32, buf: &mut &'de [u8]) -> Result<Option<Vec<Self>>> {
        let _ = len;
        let _ = buf;
        Ok(None)
    }

    #[inline]
    #[doc(hidden)]
    fn copy_from_bytes(buf: &mut &'de [u8], out: &mut [Self]) -> Result<bool> {
        let _ = buf;
        let _ = out;
        Ok(false)
    }
}

/// Owned equivalent of [`BorshDeserialize`] that only deserializes owned values and does not
/// require a lifetime.
pub trait BorshDeserializeOwned: for<'de> BorshDeserialize<'de> {}
impl<T> BorshDeserializeOwned for T where T: for<'de> BorshDeserialize<'de> {}

impl<'de> BorshDeserialize<'de> for u8 {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        if buf.is_empty() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let res = buf[0];
        *buf = &buf[1..];
        Ok(res)
    }

    #[inline]
    #[doc(hidden)]
    fn vec_from_bytes(len: u32, buf: &mut &[u8]) -> Result<Option<Vec<Self>>> {
        let len = len.try_into().map_err(|_| ErrorKind::InvalidInput)?;
        if buf.len() < len {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let (front, rest) = buf.split_at(len);
        *buf = rest;
        Ok(Some(front.to_vec()))
    }

    #[inline]
    #[doc(hidden)]
    fn copy_from_bytes(buf: &mut &[u8], out: &mut [Self]) -> Result<bool> {
        if buf.len() < out.len() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let (front, rest) = buf.split_at(out.len());
        out.copy_from_slice(front);
        *buf = rest;
        Ok(true)
    }
}

macro_rules! impl_for_integer {
    ($type: ident) => {
        impl<'de> BorshDeserialize<'de> for $type {
            #[inline]
            fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
                if buf.len() < size_of::<$type>() {
                    return Err(Error::new(
                        ErrorKind::InvalidInput,
                        ERROR_UNEXPECTED_LENGTH_OF_INPUT,
                    ));
                }
                let res = $type::from_le_bytes(buf[..size_of::<$type>()].try_into().unwrap());
                *buf = &buf[size_of::<$type>()..];
                Ok(res)
            }
        }
    };
}

impl_for_integer!(i8);
impl_for_integer!(i16);
impl_for_integer!(i32);
impl_for_integer!(i64);
impl_for_integer!(i128);
impl_for_integer!(u16);
impl_for_integer!(u32);
impl_for_integer!(u64);
impl_for_integer!(u128);

macro_rules! impl_for_nonzero_integer {
    ($type: ty) => {
        impl<'de> BorshDeserialize<'de> for $type {
            #[inline]
            fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
                <$type>::new(BorshDeserialize::deserialize(buf)?)
                    .ok_or_else(|| Error::new(ErrorKind::InvalidData, ERROR_INVALID_ZERO_VALUE))
            }
        }
    };
}

impl_for_nonzero_integer!(core::num::NonZeroI8);
impl_for_nonzero_integer!(core::num::NonZeroI16);
impl_for_nonzero_integer!(core::num::NonZeroI32);
impl_for_nonzero_integer!(core::num::NonZeroI64);
impl_for_nonzero_integer!(core::num::NonZeroI128);
impl_for_nonzero_integer!(core::num::NonZeroU8);
impl_for_nonzero_integer!(core::num::NonZeroU16);
impl_for_nonzero_integer!(core::num::NonZeroU32);
impl_for_nonzero_integer!(core::num::NonZeroU64);
impl_for_nonzero_integer!(core::num::NonZeroU128);
impl_for_nonzero_integer!(core::num::NonZeroUsize);

impl<'de> BorshDeserialize<'de> for usize {
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let u: u64 = BorshDeserialize::deserialize(buf)?;
        let u = usize::try_from(u).map_err(|_| {
            Error::new(
                ErrorKind::InvalidInput,
                ERROR_OVERFLOW_ON_MACHINE_WITH_32_BIT_USIZE,
            )
        })?;
        Ok(u)
    }
}

// Note NaNs have a portability issue. Specifically, signalling NaNs on MIPS are quiet NaNs on x86,
// and vice-versa. We disallow NaNs to avoid this issue.
macro_rules! impl_for_float {
    ($type: ident, $int_type: ident) => {
        impl<'de> BorshDeserialize<'de> for $type {
            #[inline]
            fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
                if buf.len() < size_of::<$type>() {
                    return Err(Error::new(
                        ErrorKind::InvalidInput,
                        ERROR_UNEXPECTED_LENGTH_OF_INPUT,
                    ));
                }
                let res = $type::from_bits($int_type::from_le_bytes(
                    buf[..size_of::<$int_type>()].try_into().unwrap(),
                ));
                *buf = &buf[size_of::<$int_type>()..];
                if res.is_nan() {
                    return Err(Error::new(
                        ErrorKind::InvalidInput,
                        "For portability reasons we do not allow to deserialize NaNs.",
                    ));
                }
                Ok(res)
            }
        }
    };
}

impl_for_float!(f32, u32);
impl_for_float!(f64, u64);

impl<'de> BorshDeserialize<'de> for bool {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        if buf.is_empty() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let b = buf[0];
        *buf = &buf[1..];
        if b == 0 {
            Ok(false)
        } else if b == 1 {
            Ok(true)
        } else {
            let msg = format!("Invalid bool representation: {}", b);

            Err(Error::new(ErrorKind::InvalidInput, msg))
        }
    }
}

impl<'de, T> BorshDeserialize<'de> for Option<T>
where
    T: BorshDeserialize<'de>,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        if buf.is_empty() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let flag = buf[0];
        *buf = &buf[1..];
        if flag == 0 {
            Ok(None)
        } else if flag == 1 {
            Ok(Some(T::deserialize(buf)?))
        } else {
            let msg = format!(
                "Invalid Option representation: {}. The first byte must be 0 or 1",
                flag
            );

            Err(Error::new(ErrorKind::InvalidInput, msg))
        }
    }
}

impl<'de, T, E> BorshDeserialize<'de> for core::result::Result<T, E>
where
    T: BorshDeserialize<'de>,
    E: BorshDeserialize<'de>,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        if buf.is_empty() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let flag = buf[0];
        *buf = &buf[1..];
        if flag == 0 {
            Ok(Err(E::deserialize(buf)?))
        } else if flag == 1 {
            Ok(Ok(T::deserialize(buf)?))
        } else {
            let msg = format!(
                "Invalid Result representation: {}. The first byte must be 0 or 1",
                flag
            );

            Err(Error::new(ErrorKind::InvalidInput, msg))
        }
    }
}

impl<'de> BorshDeserialize<'de> for &'de [u8] {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let len = u32::deserialize(buf)? as usize;
        if buf.len() < len {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let (front, rest) = buf.split_at(len);
        *buf = rest;
        Ok(front)
    }
}

impl<'de> BorshDeserialize<'de> for &'de str {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        core::str::from_utf8(<&'de [u8]>::deserialize(buf)?).map_err(|err| {
            let msg = err.to_string();
            Error::new(ErrorKind::InvalidData, msg)
        })
    }
}

impl<'de> BorshDeserialize<'de> for String {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        String::from_utf8(Vec::<u8>::deserialize(buf)?).map_err(|err| {
            let msg = err.to_string();
            Error::new(ErrorKind::InvalidData, msg)
        })
    }
}

impl<'de, T> BorshDeserialize<'de> for Vec<T>
where
    T: BorshDeserialize<'de>,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let len = u32::deserialize(buf)?;
        if len == 0 {
            Ok(Vec::new())
        } else if let Some(vec_bytes) = T::vec_from_bytes(len, buf)? {
            Ok(vec_bytes)
        } else if size_of::<T>() == 0 {
            let mut result = vec![T::deserialize(buf)?];

            let p = result.as_mut_ptr();
            unsafe {
                forget(result);
                let len = len.try_into().map_err(|_| ErrorKind::InvalidInput)?;
                let result = Vec::from_raw_parts(p, len, len);
                Ok(result)
            }
        } else {
            // TODO(16): return capacity allocation when we can safely do that.
            let mut result = Vec::with_capacity(hint::cautious::<T>(len));
            for _ in 0..len {
                result.push(T::deserialize(buf)?);
            }
            Ok(result)
        }
    }
}

impl<'de, T> BorshDeserialize<'de> for Cow<'_, T>
where
    T: ToOwned + ?Sized,
    T::Owned: BorshDeserialize<'de>,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        Ok(Cow::Owned(BorshDeserialize::deserialize(buf)?))
    }
}

impl<'de, T> BorshDeserialize<'de> for VecDeque<T>
where
    T: BorshDeserialize<'de>,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let vec = <Vec<T>>::deserialize(buf)?;
        Ok(vec.into())
    }
}

impl<'de, T> BorshDeserialize<'de> for LinkedList<T>
where
    T: BorshDeserialize<'de>,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let vec = <Vec<T>>::deserialize(buf)?;
        Ok(vec.into_iter().collect::<LinkedList<T>>())
    }
}

impl<'de, T> BorshDeserialize<'de> for BinaryHeap<T>
where
    T: BorshDeserialize<'de> + Ord,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let vec = <Vec<T>>::deserialize(buf)?;
        Ok(vec.into_iter().collect::<BinaryHeap<T>>())
    }
}

impl<'de, T, H> BorshDeserialize<'de> for HashSet<T, H>
where
    T: BorshDeserialize<'de> + Eq + Hash,
    H: BuildHasher + Default,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let vec = <Vec<T>>::deserialize(buf)?;
        Ok(vec.into_iter().collect::<HashSet<T, H>>())
    }
}

impl<'de, K, V, H> BorshDeserialize<'de> for HashMap<K, V, H>
where
    K: BorshDeserialize<'de> + Eq + Hash,
    V: BorshDeserialize<'de>,
    H: BuildHasher + Default,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let len = u32::deserialize(buf)?;
        // TODO(16): return capacity allocation when we can safely do that.
        let mut result = HashMap::with_hasher(H::default());
        for _ in 0..len {
            let key = K::deserialize(buf)?;
            let value = V::deserialize(buf)?;
            result.insert(key, value);
        }
        Ok(result)
    }
}

impl<'de, T> BorshDeserialize<'de> for BTreeSet<T>
where
    T: BorshDeserialize<'de> + Ord,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let vec = <Vec<T>>::deserialize(buf)?;
        Ok(vec.into_iter().collect::<BTreeSet<T>>())
    }
}

impl<'de, K, V> BorshDeserialize<'de> for BTreeMap<K, V>
where
    K: BorshDeserialize<'de> + Ord + core::hash::Hash,
    V: BorshDeserialize<'de>,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let len = u32::deserialize(buf)?;
        let mut result = BTreeMap::new();
        for _ in 0..len {
            let key = K::deserialize(buf)?;
            let value = V::deserialize(buf)?;
            result.insert(key, value);
        }
        Ok(result)
    }
}

#[cfg(feature = "std")]
impl<'de> BorshDeserialize<'de> for std::net::SocketAddr {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let kind = u8::deserialize(buf)?;
        match kind {
            0 => std::net::SocketAddrV4::deserialize(buf).map(std::net::SocketAddr::V4),
            1 => std::net::SocketAddrV6::deserialize(buf).map(std::net::SocketAddr::V6),
            value => Err(Error::new(
                ErrorKind::InvalidInput,
                format!("Invalid SocketAddr variant: {}", value),
            )),
        }
    }
}

#[cfg(feature = "std")]
impl<'de> BorshDeserialize<'de> for std::net::SocketAddrV4 {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let ip = std::net::Ipv4Addr::deserialize(buf)?;
        let port = u16::deserialize(buf)?;
        Ok(std::net::SocketAddrV4::new(ip, port))
    }
}

#[cfg(feature = "std")]
impl<'de> BorshDeserialize<'de> for std::net::SocketAddrV6 {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let ip = std::net::Ipv6Addr::deserialize(buf)?;
        let port = u16::deserialize(buf)?;
        Ok(std::net::SocketAddrV6::new(ip, port, 0, 0))
    }
}

#[cfg(feature = "std")]
impl<'de> BorshDeserialize<'de> for std::net::Ipv4Addr {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        if buf.len() < 4 {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let bytes: [u8; 4] = buf[..4].try_into().unwrap();
        let res = std::net::Ipv4Addr::from(bytes);
        *buf = &buf[4..];
        Ok(res)
    }
}

#[cfg(feature = "std")]
impl<'de> BorshDeserialize<'de> for std::net::Ipv6Addr {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        if buf.len() < 16 {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let bytes: [u8; 16] = buf[..16].try_into().unwrap();
        let res = std::net::Ipv6Addr::from(bytes);
        *buf = &buf[16..];
        Ok(res)
    }
}

impl<'de, T, U> BorshDeserialize<'de> for Box<T>
where
    U: Into<Box<T>> + Borrow<T>,
    T: ToOwned<Owned = U> + ?Sized,
    T::Owned: BorshDeserialize<'de>,
{
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        Ok(T::Owned::deserialize(buf)?.into())
    }
}

#[cfg(not(feature = "const-generics"))]
const _: () = {
    macro_rules! impl_arrays {
        ($($len:expr)+) => {
        $(
            impl<'de, T> BorshDeserialize<'de> for [T; $len]
            where
                T: BorshDeserialize<'de> + Default + Copy
            {
                #[inline]
                fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
                    let mut result = [T::default(); $len];
                    if !T::copy_from_bytes(buf, &mut result)? {
                        for i in 0..$len {
                            result[i] = T::deserialize(buf)?;
                        }
                    }
                    Ok(result)
                }
            }
        )+
        };
    }

    impl_arrays!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 64 65 128 256 512 1024 2048);

    impl<'de, T> BorshDeserialize<'de> for [T; 0]
    where
        T: BorshDeserialize<'de> + Default + Copy,
    {
        #[inline]
        fn deserialize(_buf: &mut &'de [u8]) -> Result<Self> {
            Ok([T::default(); 0])
        }
    }
};

#[cfg(feature = "const-generics")]
impl<'de, T, const N: usize> BorshDeserialize<'de> for [T; N]
where
    T: BorshDeserialize<'de> + Default + Copy,
{
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let mut result = [T::default(); N];
        if N > 0 && !T::copy_from_bytes(buf, &mut result)? {
            for i in 0..N {
                result[i] = T::deserialize(buf)?;
            }
        }
        Ok(result)
    }
}

impl<'de> BorshDeserialize<'de> for () {
    fn deserialize(_buf: &mut &'de [u8]) -> Result<Self> {
        Ok(())
    }
}

macro_rules! impl_tuple {
    ($($name:ident)+) => {
      impl<'de, $($name),+> BorshDeserialize<'de> for ($($name),+)
      where $($name: BorshDeserialize<'de>,)+
      {
        #[inline]
        fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
            Ok(($($name::deserialize(buf)?,)+))
        }
      }
    };
}

impl_tuple!(T0 T1);
impl_tuple!(T0 T1 T2);
impl_tuple!(T0 T1 T2 T3);
impl_tuple!(T0 T1 T2 T3 T4);
impl_tuple!(T0 T1 T2 T3 T4 T5);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19);

#[cfg(feature = "rc")]
impl<'de, T, U> BorshDeserialize<'de> for Rc<T>
where
    U: Into<Rc<T>> + Borrow<T>,
    T: ToOwned<Owned = U> + ?Sized,
    T::Owned: BorshDeserialize<'de>,
{
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        Ok(T::Owned::deserialize(buf)?.into())
    }
}

#[cfg(feature = "rc")]
impl<'de, T, U> BorshDeserialize<'de> for Arc<T>
where
    U: Into<Arc<T>> + Borrow<T>,
    T: ToOwned<Owned = U> + ?Sized,
    T::Owned: BorshDeserialize<'de>,
{
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        Ok(T::Owned::deserialize(buf)?.into())
    }
}

impl<'de, T: ?Sized> BorshDeserialize<'de> for PhantomData<T> {
    fn deserialize(_: &mut &'de [u8]) -> Result<Self> {
        Ok(Self::default())
    }
}
