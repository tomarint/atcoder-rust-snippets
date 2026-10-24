// https://github.com/tomarint/atcoder-rust-snippets
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_macros)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(non_snake_case)]
use proconio::input;
use proconio::marker::{Chars, Isize1, Usize1, Bytes};
use superslice::Ext;
// mod superslice;
// use superslice::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque, BinaryHeap};
use std::io::{Read, Write};
use std::ops::Bound::{Excluded, Included, Unbounded};
use std::cmp::Reverse;
use std::thread::panicking;
//----------------------------------------------------------------------------
macro_rules! parse_input {
    ($x:expr, $t:ident) => {
        $x.trim().parse::<$t>().unwrap()
    };
}

fn input() -> String {
    let mut input_line = String::new();
    std::io::stdin().read_line(&mut input_line).unwrap();
    input_line
}

fn read<T>() -> T
where
    T: std::str::FromStr,
    T::Err: std::fmt::Debug,
{
    input().trim().parse().unwrap()
}
fn readvec<T>() -> Vec<T>
where
    T: std::str::FromStr,
    T::Err: std::fmt::Debug,
{
    input()
        .split_whitespace()
        .map(|x| x.parse::<T>().unwrap())
        .collect::<Vec<T>>()
}
//----------------------------------------------------------------------------
macro_rules! addto {
    ($dst:expr, $src:expr $(,)?) => {{
        let value = $src;
        $dst += value;
    }};
}

macro_rules! chmax {
    ($dst:expr, $candidate:expr $(,)?) => {{
        let candidate = $candidate;
        let dst = &mut $dst;

        if *dst < candidate {
            *dst = candidate;
            true
        } else {
            false
        }
    }};
}

macro_rules! chmin {
    ($dst:expr, $candidate:expr $(,)?) => {{
        let candidate = $candidate;
        let dst = &mut $dst;

        if candidate < *dst {
            *dst = candidate;
            true
        } else {
            false
        }
    }};
}
//----------------------------------------------------------------------------
#[derive(Debug, PartialEq, PartialOrd)]
struct FloatCmp(f64);

impl Eq for FloatCmp {}

impl Ord for FloatCmp {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.0.partial_cmp(&self.0).unwrap()
    }
}
//----------------------------------------------------------------------------
// MOD は素数であること。
pub const MOD: i64 = 998_244_353;
// pub const MOD: i64 = 1_000_000_007;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
#[must_use]
pub struct Mint {
    val: i64,
}

impl Mint {
    pub const ZERO: Self = Self { val: 0 };
    pub const ONE: Self = Self { val: 1 };

    /// 各整数型や Mint から生成する。
    ///
    /// 例:
    /// Mint::new(-1)
    /// Mint::new(10usize)
    pub fn new<T>(n: T) -> Self
    where
        T: std::convert::Into<Self>,
    {
        n.into()
    }

    fn from_i128_impl(n: i128) -> Self {
        Self {
            val: n.rem_euclid(MOD as i128) as i64,
        }
    }

    fn from_u128_impl(n: u128) -> Self {
        Self {
            val: (n % MOD as u128) as i64,
        }
    }

    /// 0 以上 MOD 未満に正規化された値を返す。
    pub const fn value(self) -> i64 {
        self.val
    }

    pub const fn modulus() -> i64 {
        MOD
    }

    pub const fn is_zero(self) -> bool {
        self.val == 0
    }

    /// self^exp を返す。
    ///
    /// 0^0 は 1 とする。
    pub fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut result = Self::ONE;

        while exp != 0 {
            if exp & 1 != 0 {
                result *= base;
            }

            base = base * base;
            exp >>= 1;
        }

        result
    }

    /// 逆元を返す。
    ///
    /// MOD が素数であることを前提とする。
    /// self == 0 の場合は None。
    pub fn checked_inv(self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(self.pow((MOD - 2) as u64))
        }
    }

    /// 逆元を返す。
    ///
    /// # Panics
    ///
    /// self == 0 の場合。
    #[track_caller]
    pub fn inv(self) -> Self {
        self.checked_inv()
            .expect("zero has no modular multiplicative inverse")
    }

    pub fn checked_div<T>(self, rhs: T) -> Option<Self>
    where
        T: std::convert::Into<Self>,
    {
        let rhs = rhs.into();
        rhs.checked_inv().map(|inv| self * inv)
    }

    fn mul_raw(lhs: i64, rhs: i64) -> i64 {
        ((lhs as i128 * rhs as i128) % MOD as i128) as i64
    }
}

impl std::fmt::Display for Mint {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl std::fmt::Debug for Mint {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl<T> std::ops::Add<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    type Output = Self;

    fn add(self, rhs: T) -> Self::Output {
        let rhs = rhs.into();

        let val = if self.val >= MOD - rhs.val {
            self.val - (MOD - rhs.val)
        } else {
            self.val + rhs.val
        };

        Self { val }
    }
}

impl<T> std::ops::Sub<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    type Output = Self;

    fn sub(self, rhs: T) -> Self::Output {
        let rhs = rhs.into();

        let val = if self.val >= rhs.val {
            self.val - rhs.val
        } else {
            MOD - (rhs.val - self.val)
        };

        Self { val }
    }
}

impl<T> std::ops::Mul<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    type Output = Self;

    fn mul(self, rhs: T) -> Self::Output {
        let rhs = rhs.into();

        Self {
            val: Self::mul_raw(self.val, rhs.val),
        }
    }
}

impl<T> std::ops::Div<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    type Output = Self;

    /// # Panics
    ///
    /// rhs == 0 の場合。
    #[track_caller]
    fn div(self, rhs: T) -> Self::Output {
        let inv = rhs.into().inv();

        Self {
            val: Self::mul_raw(self.val, inv.val),
        }
    }
}

impl<T> std::ops::AddAssign<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    fn add_assign(&mut self, rhs: T) {
        *self = *self + rhs;
    }
}

impl<T> std::ops::SubAssign<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    fn sub_assign(&mut self, rhs: T) {
        *self = *self - rhs;
    }
}

impl<T> std::ops::MulAssign<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    fn mul_assign(&mut self, rhs: T) {
        *self = *self * rhs;
    }
}

impl<T> std::ops::DivAssign<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    fn div_assign(&mut self, rhs: T) {
        *self = *self / rhs;
    }
}

impl std::ops::Neg for Mint {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.is_zero() {
            Self::ZERO
        } else {
            Self {
                val: MOD - self.val,
            }
        }
    }
}

macro_rules! impl_mint_from_signed {
    ($($t:ty),* $(,)?) => {
        $(
            impl std::convert::From<$t> for Mint {
                fn from(n: $t) -> Self {
                    Self::from_i128_impl(n as i128)
                }
            }
        )*
    };
}

macro_rules! impl_mint_from_unsigned {
    ($($t:ty),* $(,)?) => {
        $(
            impl std::convert::From<$t> for Mint {
                fn from(n: $t) -> Self {
                    Self::from_u128_impl(n as u128)
                }
            }
        )*
    };
}

impl_mint_from_signed!(
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
);

impl_mint_from_unsigned!(
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
);

impl std::convert::From<bool> for Mint {
    fn from(value: bool) -> Self {
        if value {
            Self::ONE
        } else {
            Self::ZERO
        }
    }
}

impl std::convert::From<&Mint> for Mint {
    fn from(value: &Mint) -> Self {
        *value
    }
}

impl std::convert::From<Mint> for i64 {
    fn from(value: Mint) -> Self {
        value.val
    }
}

impl std::str::FromStr for Mint {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<i128>().map(Self::from_i128_impl)
    }
}

impl<T> std::iter::Sum<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: std::iter::Iterator<Item = T>,
    {
        iter.fold(Self::ZERO, |acc, value| acc + value)
    }
}

impl<T> std::iter::Product<T> for Mint
where
    T: std::convert::Into<Mint>,
{
    fn product<I>(iter: I) -> Self
    where
        I: std::iter::Iterator<Item = T>,
    {
        iter.fold(Self::ONE, |acc, value| acc * value)
    }
}
//----------------------------------------------------------------------------
pub struct MintComb {
    fact: Vec<Mint>,
    ifact: Vec<Mint>,
}

impl MintComb {
    pub fn new(n: usize) -> Self {
        let mut obj = Self {
            fact: vec![Mint::new(1); n + 1],
            ifact: vec![Mint::new(1); n + 1],
        };
        assert!(n < (MOD as usize));
        obj.fact[0] = Mint::new(1);
        for i in 1..=n {
            obj.fact[i] = obj.fact[i - 1] * Mint::new(i as i64);
        }
        obj.ifact[n] = obj.fact[n].inv();
        for i in (1..=n).rev() {
            obj.ifact[i - 1] = obj.ifact[i] * Mint::new(i as i64);
        }
        obj
    }
    pub fn permutation(&self, n: usize, k: usize) -> Mint {
        if n < k {
            Mint::new(0)
        } else {
            self.fact[n] * self.ifact[n - k]
        }
    }
    pub fn combination(&self, n: usize, k: usize) -> Mint {
        if n < k {
            Mint::new(0)
        } else {
            self.fact[n] * self.ifact[k as usize] * self.ifact[n - k]
        }
    }
}
//----------------------------------------------------------------------------
// 有理数（分数）
#[derive(Copy, Clone, Eq)]
struct Ratio {
    numerator: i64,   // 分子
    denominator: i64, // 分母
}

// ユークリッドの互除法
fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

impl std::fmt::Display for Ratio {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl std::fmt::Debug for Ratio {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl Ratio {
    fn new(p: i64, q: i64) -> Ratio {
        if q == 0 {
            panic!("Ratio: divide by zero");
        }
        let g = gcd(p.abs(), q.abs());
        let s = if q < 0 { -1 } else { 1 };
        Ratio {
            numerator: s * p / g,
            denominator: s * q / g,
        }
    }

    fn from_integer(n: i64) -> Ratio {
        Ratio {
            numerator: n,
            denominator: 1,
        }
    }

    fn as_int(&self) -> i64 {
        self.numerator / self.denominator
    }
    fn as_float(&self) -> f64 {
        self.numerator as f64 / self.denominator as f64
    }

    fn numer(&self) -> i64 {
        self.numerator
    }
    fn denom(&self) -> i64 {
        self.denominator
    }

    fn is_integer(&self) -> bool {
        self.denominator == 1
    }
}

impl PartialOrd for Ratio {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (self.numerator * other.denominator).partial_cmp(&(other.numerator * self.denominator))
    }
}

impl Ord for Ratio {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.numerator * other.denominator).cmp(&(other.numerator * self.denominator))
    }
}

impl PartialEq for Ratio {
    fn eq(&self, other: &Self) -> bool {
        self.numerator * other.denominator == other.numerator * self.denominator
    }
}

impl std::ops::Add for Ratio {
    type Output = Ratio;
    fn add(self, other: Ratio) -> Ratio {
        let p = self.numerator * other.denominator + other.numerator * self.denominator;
        let q = self.denominator * other.denominator;
        Ratio::new(p, q)
    }
}

impl std::ops::Sub for Ratio {
    type Output = Ratio;
    fn sub(self, other: Ratio) -> Ratio {
        let p = self.numerator * other.denominator - other.numerator * self.denominator;
        let q = self.denominator * other.denominator;
        Ratio::new(p, q)
    }
}

impl std::ops::Mul for Ratio {
    type Output = Ratio;
    fn mul(self, other: Ratio) -> Ratio {
        let p = self.numerator * other.numerator;
        let q = self.denominator * other.denominator;
        Ratio::new(p, q)
    }
}

impl std::ops::Div for Ratio {
    type Output = Ratio;
    fn div(self, other: Ratio) -> Ratio {
        let p = self.numerator * other.denominator;
        let q = self.denominator * other.numerator;
        Ratio::new(p, q)
    }
}
//----------------------------------------------------------------------------
// 加算用Binary Indexed Tree
#[derive(Clone, Debug)]
struct FenwickSum {
    n: usize,
    data: Vec<i64>,
}

impl FenwickSum {
    fn new(n: usize) -> Self {
        Self {
            n,
            data: vec![0; n + 1],
        }
    }

    /// a[index] += delta
    fn add(&mut self, index: usize, delta: i64) {
        assert!(index < self.n);

        let mut i = index + 1;

        while i <= self.n {
            self.data[i] += delta;
            i += i & i.wrapping_neg();
        }
    }

    /// a[0..end] の合計を返す。
    fn prefix_sum(&self, end: usize) -> i64 {
        assert!(end <= self.n);

        let mut i = end;
        let mut result = 0;

        while i > 0 {
            result += self.data[i];
            i &= i - 1;
        }

        result
    }

    /// a[left..right] の合計を返す。
    fn sum(&self, left: usize, right: usize) -> i64 {
        assert!(left <= right);
        assert!(right <= self.n);

        self.prefix_sum(right) - self.prefix_sum(left)
    }
}
// prefix最大値用Binary Indexed Tree
#[derive(Clone, Debug)]
struct FenwickMax {
    n: usize,
    identity: i64,
    data: Vec<i64>,
}

impl FenwickMax {
    /// 空区間の最大値を i64::MIN とする。
    fn new(n: usize) -> Self {
        Self::with_identity(n, i64::MIN)
    }

    /// identityを任意に指定する。
    ///
    /// DPで「何も選ばない場合は0」としたい場合などは、
    /// `FenwickMax::with_identity(n, 0)` とする。
    fn with_identity(n: usize, identity: i64) -> Self {
        Self {
            n,
            identity,
            data: vec![identity; n + 1],
        }
    }

    /// a[index] = max(a[index], value) 相当の更新。
    ///
    /// 以前の値より小さくする更新には対応しない。
    fn chmax(&mut self, index: usize, value: i64) {
        assert!(index < self.n);

        let mut i = index + 1;

        while i <= self.n {
            self.data[i] = self.data[i].max(value);
            i += i & i.wrapping_neg();
        }
    }

    /// a[0..end] の最大値を返す。
    fn prefix_max(&self, end: usize) -> i64 {
        assert!(end <= self.n);

        let mut i = end;
        let mut result = self.identity;

        while i > 0 {
            result = result.max(self.data[i]);
            i &= i - 1;
        }

        result
    }
}
//----------------------------------------------------------------------------
// multiset
#[derive(Clone, Debug)]
struct MultiSet<T> {
    map: BTreeMap<T, usize>,
    len: usize,
}

struct MultiSetIterator<'a, T> {
    iter: std::collections::btree_map::Iter<'a, T, usize>,
    remaining: usize,
    current: Option<&'a T>,
}

impl<'a, T: Ord> Iterator for MultiSetIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining > 0 {
            self.remaining -= 1;
            self.current
        } else {
            let (key, count) = self.iter.next()?;
            self.current = Some(key);
            self.remaining = count - 1;
            self.current
        }
    }
}

impl<'a, T: Ord> DoubleEndedIterator for MultiSetIterator<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining > 0 {
            self.remaining -= 1;
            self.current
        } else {
            let (key, count) = self.iter.next_back()?;
            self.current = Some(key);
            self.remaining = count - 1;
            self.current
        }
    }
}

impl<T: Ord + Clone> MultiSet<T> {
    fn new() -> MultiSet<T> {
        MultiSet {
            map: BTreeMap::new(),
            len: 0,
        }
    }

    fn insert(&mut self, value: T) {
        *self.map.entry(value.clone()).or_insert(0) += 1;
        self.len += 1;
    }

    fn remove(&mut self, value: &T) -> bool {
        if let Some(count) = self.map.get_mut(value) {
            if *count > 1 {
                *count -= 1;
            } else {
                self.map.remove(value);
            }
            self.len -= 1;
            true
        } else {
            false
        }
    }

    fn contains(&self, value: &T) -> bool {
        self.map.contains_key(value)
    }

    fn count(&self, value: &T) -> usize {
        *self.map.get(value).unwrap_or(&0)
    }

    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn len(&self) -> usize {
        self.len
    }

    fn iter(&self) -> MultiSetIterator<'_, T> {
        MultiSetIterator {
            iter: self.map.iter(),
            remaining: 0,
            current: None,
        }
    }

    fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let value = self.front().unwrap().clone();
        self.remove(&value);
        Some(value)
    }

    fn front(&self) -> Option<&T> {
        self.map.iter().next().map(|(key, _)| key)
    }

    fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let value = self.back().unwrap().clone();
        self.remove(&value);
        Some(value)
    }

    fn back(&self) -> Option<&T> {
        self.map.iter().next_back().map(|(key, _)| key)
    }
}
//----------------------------------------------------------------------------
// 区間Set
#[derive(Clone, Debug)]
struct IntervalSet<T> {
    st: std::collections::BTreeSet<(T, T)>,
}
impl<T: Ord + Copy> IntervalSet<T> {
    fn new() -> Self {
        Self {
            st: std::collections::BTreeSet::new(),
        }
    }
    // Add [l, r)
    fn add(&mut self, kukan: (T, T)) {
        let mut kukan = kukan;
        loop {
            let mut rng = self.st.range(kukan..);
            if let Some(it) = rng.next() {
                if it.0 <= kukan.1 {
                    kukan.1 = kukan.1.max(it.1);
                    let it = it.clone();
                    self.st.remove(&it);
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        loop {
            let mut rng = self.st.range(..kukan);
            if let Some(it) = rng.next_back() {
                if kukan.0 <= it.1 {
                    kukan.0 = kukan.0.min(it.0);
                    kukan.1 = kukan.1.max(it.1);
                    let it = it.clone();
                    self.st.remove(&it);
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.st.insert(kukan);
    }
}
//----------------------------------------------------------------------------
// RMQ（Range Maximum Query）を実装したセグメントツリー（区間更新対応）
struct RangeMaximumQuery {
    n: usize,                // 葉の数（データのサイズを超える最小の2のべき乗）
    tree: Vec<i64>,          // セグメントツリーを格納する配列
    lazy: Vec<Option<i64>>,  // 遅延評価配列
}

impl RangeMaximumQuery {
    // 新しいセグメントツリーを構築する
    fn new(arr: &[i64]) -> Self {
        let n = arr.len();
        let mut size = 1;
        while size < n {
            size *= 2;
        }
        let mut tree = vec![i64::MIN; 2 * size];
        let lazy = vec![None; 2 * size];
        let mut st = RangeMaximumQuery { n: size, tree, lazy };
        // 葉に値を設定
        for i in 0..n {
            st.tree[st.n + i] = arr[i];
        }
        // 内部ノードを構築
        for i in (1..st.n).rev() {
            st.tree[i] = std::cmp::max(st.tree[2 * i], st.tree[2 * i + 1]);
        }
        st
    }

    // 遅延評価の伝搬
    fn push(&mut self, node: usize, node_left: usize, node_right: usize) {
        if let Some(value) = self.lazy[node] {
            self.tree[node] = value;
            if node_left + 1 != node_right { // 葉でない場合
                self.lazy[2 * node] = Some(value);
                self.lazy[2 * node + 1] = Some(value);
            }
            self.lazy[node] = None;
        }
    }

    // 区間 [l, r) の値を value に更新
    fn update_range(&mut self, l: usize, r: usize, value: i64) {
        self.update_range_rec(1, 0, self.n, l, r, value);
    }

    fn update_range_rec(
        &mut self,
        node: usize,
        node_left: usize,
        node_right: usize,
        l: usize,
        r: usize,
        value: i64,
    ) {
        self.push(node, node_left, node_right);
        if node_right <= l || r <= node_left {
            // 重ならない場合
            return;
        }
        if l <= node_left && node_right <= r {
            // 完全に含まれる場合
            self.lazy[node] = Some(value);
            self.push(node, node_left, node_right);
        } else {
            // 一部だけ重なる場合
            let mid = (node_left + node_right) / 2;
            self.update_range_rec(2 * node, node_left, mid, l, r, value);
            self.update_range_rec(2 * node + 1, mid, node_right, l, r, value);
            self.tree[node] = std::cmp::max(self.tree[2 * node], self.tree[2 * node + 1]);
        }
    }

    // 区間 [left, right) の最大値を求める
    fn query(&mut self, left: usize, right: usize) -> i64 {
        self.query_rec(1, 0, self.n, left, right)
    }

    fn query_rec(
        &mut self,
        node: usize,
        node_left: usize,
        node_right: usize,
        l: usize,
        r: usize,
    ) -> i64 {
        self.push(node, node_left, node_right);
        if node_right <= l || r <= node_left {
            // 重ならない場合
            return i64::MIN;
        }
        if l <= node_left && node_right <= r {
            // 完全に含まれる場合
            return self.tree[node];
        } else {
            // 一部だけ重なる場合
            let mid = (node_left + node_right) / 2;
            let left_max = self.query_rec(2 * node, node_left, mid, l, r);
            let right_max = self.query_rec(2 * node + 1, mid, node_right, l, r);
            std::cmp::max(left_max, right_max)
        }
    }

    // 1点の値を更新する
    fn update(&mut self, index: usize, value: i64) {
        self.update_range(index, index + 1, value);
    }
}

struct RangeMinimumQuery {
    n: usize,                // 葉の数（データのサイズを超える最小の2のべき乗）
    tree: Vec<i64>,          // セグメントツリーを格納する配列
    lazy: Vec<Option<i64>>,  // 遅延評価配列
}
impl RangeMinimumQuery {
    // 新しいセグメントツリーを構築する
    fn new(arr: &[i64]) -> Self {
        let n = arr.len();
        let mut size = 1;
        while size < n {
            size *= 2;
        }
        let mut tree = vec![i64::MAX; 2 * size];
        let lazy = vec![None; 2 * size];
        let mut st = RangeMinimumQuery { n: size, tree, lazy };
        // 葉に値を設定
        for i in 0..n {
            st.tree[st.n + i] = arr[i];
        }
        // 内部ノードを構築
        for i in (1..st.n).rev() {
            st.tree[i] = std::cmp::min(st.tree[2 * i], st.tree[2 * i + 1]);
        }
        st
    }
    // 遅延評価の伝搬
    fn push(&mut self, node: usize, node_left: usize, node_right: usize) {
        if let Some(value) = self.lazy[node] {
            self.tree[node] = value;
            if node_left + 1 != node_right { // 葉でない場合
                self.lazy[2 * node] = Some(value);
                self.lazy[2 * node + 1] = Some(value);
            }
            self.lazy[node] = None;
        }
    }
    // 区間 [l, r) の値を value に更新
    fn update_range(&mut self, l: usize, r: usize, value: i64) {
        self.update_range_rec(1, 0, self.n, l, r, value);
    }
    fn update_range_rec(
        &mut self,
        node: usize,
        node_left: usize,
        node_right: usize,
        l: usize,
        r: usize,
        value: i64,
    ) {
        self.push(node, node_left, node_right);
        if node_right <= l || r <= node_left {
            // 重ならない場合
            return;
        }
        if l <= node_left && node_right <= r {
            // 完全に含まれる場合
            self.lazy[node] = Some(value);
            self.push(node, node_left, node_right);
        } else {
            // 一部だけ重なる場合
            let mid = (node_left + node_right) / 2;
            self.update_range_rec(2 * node, node_left, mid, l, r, value);
            self.update_range_rec(2 * node + 1, mid, node_right, l, r, value);
            self.tree[node] = std::cmp::min(self.tree[2 * node], self.tree[2 * node + 1]);
        }
    }
    // 区間 [left, right) の最小値を求める
    fn query(&mut self, left: usize, right: usize) -> i64 {
        self.query_rec(1, 0, self.n, left, right)
    }
    fn query_rec(
        &mut self,
        node: usize,
        node_left: usize,
        node_right: usize,
        l: usize,
        r: usize,
    ) -> i64 {
        self.push(node, node_left, node_right);
        if node_right <= l || r <= node_left {
            // 重ならない場合
            return i64::MAX;
        }
        if l <= node_left && node_right <= r {
            // 完全に含まれる場合
            return self.tree[node];
        } else {
            // 一部だけ重なる場合
            let mid = (node_left + node_right) / 2;
            let left_min = self.query_rec(2 * node, node_left, mid, l, r);
            let right_min = self.query_rec(2 * node + 1, mid, node_right, l, r);
            std::cmp::min(left_min, right_min)
        }
    }
    // 1点の値を更新する
    fn update(&mut self, index: usize, value: i64) {
        self.update_range(index, index + 1, value);
    }
}

use std::ops::{Add, Sub, Mul, Div};

/// Range Sum + Range Assign（区間和クエリ＋区間代入）をサポートする遅延セグ木
pub struct RangeSumQuery<T> {
    n: usize,
    size: usize,
    data: Vec<T>,             // 各ノードの区間和
    lazy: Vec<Option<T>>,     // 区間代入用の遅延値
}

impl<T> RangeSumQuery<T>
where
    T: Copy
     + Clone
     + Default             // T::default() は 0 を返す想定
     + Add<Output = T>
     + Mul<Output = T>
     + From<usize>,        // usize → T の変換に必要
{
    /// a: 0-based の初期配列
    pub fn new(a: &[T]) -> Self {
        let n = a.len();
        let size = n.next_power_of_two();
        // 配列長を 2*size に拡張、data[i] = 0 で初期化
        let mut data = vec![T::default(); 2*size];
        // 葉ノードへコピー
        for i in 0..n {
            data[size + i] = a[i];
        }
        // 内部ノードを構築
        for i in (1..size).rev() {
            data[i] = data[2*i] + data[2*i+1];
        }
        let lazy = vec![None; 2*size];
        RangeSumQuery { n, size, data, lazy }
    }

    /// ノード k に対して、長さ seg_len の区間をすべて v に上書きするときの内部処理
    fn apply_assign(&mut self, k: usize, v: T, seg_len: usize) {
        self.data[k] = v * T::from(seg_len);
        self.lazy[k] = Some(v);
    }

    /// k 番のノードが持つ遅延代入を子に伝搬
    fn push(&mut self, k: usize, seg_len: usize) {
        if let Some(v) = self.lazy[k].take() {
            let half = seg_len / 2;
            self.apply_assign(2*k,     v, half);
            self.apply_assign(2*k + 1, v, half);
        }
    }

    /// 区間 [l, r) をすべて v に代入
    pub fn assign(&mut self, l: usize, r: usize, v: T) {
        self.assign_rec(l, r, v, 1, 0, self.size);
    }
    fn assign_rec(&mut self, l: usize, r: usize, v: T,
                  k: usize, nl: usize, nr: usize) {
        if nr <= l || r <= nl {
            return;
        }
        if l <= nl && nr <= r {
            // 完全に内側：ノード k 全体を上書き
            self.apply_assign(k, v, nr - nl);
            return;
        }
        // 部分的にかぶる場合は伝搬してから子を再帰
        self.push(k, nr - nl);
        let mid = (nl + nr) / 2;
        self.assign_rec(l, r, v, 2*k,     nl,  mid);
        self.assign_rec(l, r, v, 2*k + 1, mid, nr);
        // 親ノードの値を更新
        self.data[k] = self.data[2*k] + self.data[2*k + 1];
    }

    /// 区間 [l, r) の和を返す
    pub fn sum(&mut self, l: usize, r: usize) -> T {
        self.sum_rec(l, r, 1, 0, self.size)
    }
    fn sum_rec(&mut self, l: usize, r: usize,
               k: usize, nl: usize, nr: usize) -> T {
        if nr <= l || r <= nl {
            return T::default();
        }
        if l <= nl && nr <= r {
            return self.data[k];
        }
        self.push(k, nr - nl);
        let mid = (nl + nr) / 2;
        let vl = self.sum_rec(l, r, 2*k,     nl,  mid);
        let vr = self.sum_rec(l, r, 2*k + 1, mid, nr);
        vl + vr
    }
}

//----------------------------------------------------------------------------
// トポロジカルソート
fn tsort_dfs(n: usize, to: &Vec<Vec<usize>>, visited: &mut Vec<u8>, result: &mut Vec<usize>) -> bool {
    if visited[n] == 1 { // 一時的の印がついている
        // 閉路がある
        return false;
    }
    else if visited[n] == 0 { // まだ印がついていない
        visited[n] = 1;
        for &t in &to[n] {
            if !tsort_dfs(t, to, visited, result) {
                return false;
            }
        }
        visited[n] = 2;
        result.push(n);
    }
    true
}
fn tsort(n: usize, to: &Vec<Vec<usize>>) -> Vec<usize> {
    let mut visited = vec![0u8; n];
    let mut result = vec![];
    for i in 0..n {
        if !tsort_dfs(i, to, &mut visited, &mut result) {
            return vec![];
        }
    }
    result.reverse();
    result
}
//----------------------------------------------------------------------------
#[derive(Clone)]
struct UnionFind {
    n: usize,
    parent: Vec<i64>,
}
impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            n,
            parent: vec![-1; n + 1],
        }
    }
    fn root(&mut self, a: usize) -> usize {
        if self.parent[a] < 0 {
            return a;
        }
        let r = self.root(self.parent[a] as usize);
        self.parent[a] = r as i64; // 経路圧縮
        r
    }
    fn size(&mut self, a: usize) -> usize {
        let r = self.root(a);
        -self.parent[r] as usize
    }
    fn connect(&mut self, a: usize, b: usize) -> bool {
        let a = self.root(a);
        let b = self.root(b);
        if a == b {
            return false;
        }
        if self.size(a) > self.size(b) {
            self.parent[a] += self.parent[b];
            self.parent[b] = a as i64;
        } else {
            self.parent[b] += self.parent[a];
            self.parent[a] = b as i64;
        }
        true
    }
    fn same(&mut self, a: usize, b: usize) -> bool {
        self.root(a) == self.root(b)
    }
}
//----------------------------------------------------------------------------
// Z algorithm
fn z_algorithm(s: &[u8]) -> Vec<usize> {
    let slen = s.len();
    if slen == 0 {
        return vec![];
    }
    let mut z = vec![0; slen];
    z[0] = slen;
    let mut i = 1;
    let mut j = 0;
    while i < slen {
        while i + j < slen && s[j] == s[i + j] {
            j += 1;
        }
        z[i] = j;
        if j == 0 {
            i += 1;
            continue;
        }
        let mut k = 1;
        while k < j && k + z[k] < j {
            z[i + k] = z[k];
            k += 1;
        }
        i += k;
        j -= k;
    }
    z
}
//----------------------------------------------------------------------------
// 強連結成分分解 (Kosaraju’s Algorithm)
fn kosaraju_scc(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; n];
    let mut rg = vec![vec![]; n];
    for &(u, v) in edges {
        g[u].push(v);
        rg[v].push(u);
    }
    let mut used = vec![false; n];
    let mut order = vec![];
    let mut component = vec![];

    fn dfs(v: usize, g: &Vec<Vec<usize>>, used: &mut Vec<bool>, order: &mut Vec<usize>) {
        used[v] = true;
        for &u in &g[v] {
            if !used[u] {
                dfs(u, g, used, order);
            }
        }
        order.push(v);
    }

    fn rdfs(v: usize, rg: &Vec<Vec<usize>>, used: &mut Vec<bool>, component: &mut Vec<usize>) {
        used[v] = true;
        component.push(v);
        for &u in &rg[v] {
            if !used[u] {
                rdfs(u, rg, used, component);
            }
        }
    }

    for v in 0..n {
        if !used[v] {
            dfs(v, &g, &mut used, &mut order);
        }
    }
    used.fill(false);
    let mut scc = vec![];
    for &v in order.iter().rev() {
        if !used[v] {
            component.clear();
            rdfs(v, &rg, &mut used, &mut component);
            scc.push(component.clone());
        }
    }
    scc
}
//----------------------------------------------------------------------------
macro_rules! printvec {
    ($vec:expr) => {{
        print!(
            "{}",
            $vec.iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        );
    }};
}
macro_rules! printvecln {
    ($vec:expr) => {{
        printvec!($vec);
        println!();
    }};
}
//----------------------------------------------------------------------------
const INF: i64 = 2222222222222222222;
//----------------------------------------------------------------------------
fn main() {
    let T: usize = 1; // read();
    // input! {
    //     T: usize,
    // }
    for _ in 0..T {
        solve();
    }
}
fn solve() {
}
