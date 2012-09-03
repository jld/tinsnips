use std;
import std::{sort,map};
import cmp::{Eq,Ord};
import to_bytes::{IterBytes,
                  iter_le_bytes_2,iter_le_bytes_3,
                  iter_be_bytes_2,iter_be_bytes_3};
import hash::Hash;

enum re = uint;
impl re : Eq {
    pure fn eq(&&other: re) -> bool { *self == *other }
}
impl re : Ord {
    pure fn lt(&&other: re) -> bool { *self < *other }
    pure fn le(&&other: re) -> bool { *self <= *other }
    pure fn ge(&&other: re) -> bool { *self >= *other }
    pure fn gt(&&other: re) -> bool { *self > *other }
}

enum node<L> {
    epsilon,
    lit(L),
    seq(re, re),
    or(@~[re]),
    star(re),
    not(re)
}

struct smap<L: copy Eq Ord, T> {
    lits: ~[L];
    vals: ~[T];
    default: T;
}

struct deriv<L: copy Eq Ord> {
    null: bool;
    d: smap<L, re>;
}

fn keyed_ctx<L: copy const Eq Ord IterBytes>(k0: u64, k1: u64) -> ctx<L> {
    let nodes = ~[or(@~[]), epsilon, not(re(0))];
    let rnode = map::hashmap::<node<L>, re>(|n| n.hash_keyed(k0, k1) as uint,
                                            core::cmp::eq);
    do nodes.iteri |i, n| {
        let added = rnode.insert(n, re(i));
        assert(added);
    }
    let derivs = ~[@deriv{ null: false, d: smap0(re(0)) }];
    let c = ctx{ nodes: nodes, rnode: rnode, derivs: derivs,
                 r_empty: re(0), r_eps: re(1), r_univ: re(2),
                 busy: false};
    c.compute_derivs();
    return c;
}

fn ctx<L: copy const Eq Ord IterBytes>() -> ctx<L> {
    let r = rand::Rng();
    keyed_ctx(r.gen_u64(), r.gen_u64())
}

struct ctx<L: copy Eq Ord> {
    mut nodes: ~[node<L>];
    rnode: map::hashmap<node<L>, re>;
    mut derivs: ~[@deriv<L>];
    mut busy: bool;
    r_empty: re;
    r_eps: re;
    r_univ: re;

    fn intern(n: node<L>) -> re {
        let r : re;
        let mut added = false;
        match self.rnode.find(n) {
            Some(rf) => r = rf,
            None => {
                r = re(self.nodes.len());
                vec::push(self.nodes, n);
                self.rnode.insert(n, r);
                added = true;
            }
        }
        if added && !self.busy {
            self.busy = true;
            self.compute_derivs();
            self.busy = false;
        }
        return r;
    }
    fn empty() -> re { self.r_empty }
    fn epsilon() -> re { self.r_eps }
    fn univ() -> re { self.r_univ }
    fn lit(l: L) -> re { self.intern(lit(l)) }

    fn seq(r0: re, r1: re) -> re {
        if r0 == self.r_empty || r1 == self.r_eps { return r0; }
        if r1 == self.r_empty || r0 == self.r_eps { return r1; }
        match copy self.nodes[*r0] {
            seq(r00, r01) => self.intern(seq(r00, self.seq(r01, r1))),
            _ => self.intern(seq(r0, r1))
        }
    }
    
    fn star(r: re) -> re {
        if r == self.r_empty || r == self.r_eps || r == self.r_univ {
            return r;
        }
        match self.nodes[*r] {
            star(_) => r,
            _ => self.intern(star(r))
        }
    }

    fn not(r: re) -> re {
        match self.nodes[*r] {
            not(nr) => nr,
            _ => self.intern(not(r))
        }
    }

    fn and(rs: &[re]) -> re {
        self.not(self.or(rs.map(|ri| self.not(ri))))
    }

    fn or(rs: &[re]) -> re {
        let mut cases = ~[mut];
        let mut saw_univ = false;
        for rs.each |r| {
            if r == self.r_univ { saw_univ = true; break }
            match copy self.nodes[*r] {
                or(rs) => vec::push_all(cases, *rs),
                _ => vec::push(cases, r)
            }
        }
        if saw_univ { return self.univ(); }
        sort::quick_sort3(cases);
        vec::unique(cases);
        if cases.len() == 1 {
            cases[0]
        } else {
            self.intern(or(@vec::from_mut(cases)))
        }
    }

    fn seqv(rs: &[re]) -> re {
        let mut acc = self.epsilon();
        do rs.riter |r| {
            acc = self.seq(r, acc);
        }
        acc
    }

    fn compute_derivs() {
        while self.derivs.len() < self.nodes.len() {
            let rn = re(self.derivs.len());
            let d = match copy self.nodes[*rn] {
                epsilon => deriv{ null: true, d: smap0(self.empty()) },
                lit(l) => deriv{ null: false, d: smap1(l, self.epsilon(),
                                                       self.empty()) },
                not(r) => {
                    let dr = self.derivs[*r];
                    deriv{ null: !dr.null,
                           d: smap_map(dr.d, |ri| self.not(ri)) }
                }
                star(r) => {
                    let dr = self.derivs[*r];
                    deriv{ null: true,
                          d: smap_map(dr.d, |ri| self.seq(ri, rn)) }
                }
                or(rs) => {
                    let amap = smap_reduce(*rs, |r| smap_map(self.derivs[*r].d,
                                                             |nr| ~[nr]),
                                           |v0, v1| v0 + v1);
                    deriv{ null: vec::any(*rs, |r| self.derivs[*r].null),
                           d: smap_map(amap, |nrs| self.or(nrs)) }
                }
                seq(r0, r1) => {
                    let dr0 = self.derivs[*r0];
                    let tmp = smap_map(dr0.d, |ri| self.seq(ri, r1));
                    if !dr0.null {
                        deriv{ null: false, d: tmp }
                    } else {
                        let dr1 = self.derivs[*r1];
                        deriv{ null: dr1.null, 
                               d: smap_add(tmp, dr1.d,
                                           |r0, r1| self.or(~[r0, r1])) }
                    }
                }
            };
            vec::push(self.derivs, @d);
        }
    }

    fn dump_with_fn(named: &[(~str, re)], ltos: pure fn(l: L) -> ~str) {
        (do named.map |sr| {
            match sr { (s,r) => fmt!("%s = e%u", s, *r) }
        }).iter(|s| io::println(s));
        (do self.nodes.mapi |i, n| {
            let s = match n {
                epsilon => ~"ε",
                lit(l) => ltos(l),
                seq(r0, r1) => fmt!("e%u + e%u", *r0, *r1),
                or(@rs) if rs.len() == 0 => ~"∅",
                or(@rs) => str::connect(vec::map(rs, |r| fmt!("e%u", *r)),
                                        " | "),
                star(r) => fmt!("e%u*", *r),
                not(r) => fmt!("!e%u", *r)
            };
            fmt!("e%u = %s", i, s)
        }).iter(|s| io::println(s));
        (do self.derivs.mapi |i, d| {
            let s_eps = fmt!("e%u %c ε", i, if d.null { '∋' } else { '∌' });
            let v_derivs = do d.d.lits.mapi |j, l| {
                fmt!("d%se%u = e%u", ltos(l), i, *(d.d.vals[j]))
            };
            let s_dfl = fmt!("d_e%u = e%u", i, *(d.d.default));
            ~[s_eps] + v_derivs + ~[s_dfl]
        }).iter(|v| v.iter(|s| io::println(s)));
    }
}

impl ctx<u8> {
    fn str(s: &str) -> re {
        self.seqv(str::byte_slice(s, |v| v.map(|b| self.lit(b))))
    }

    fn dump(named: &[(~str, re)]) {
        pure fn btos(&&b: u8) -> ~str {
            if 32 < b && b < 127 { fmt!("'%c'", b as char) } 
            else { fmt!("'\\%o'", b as uint) }
        }
        self.dump_with_fn(named, btos);
    }
}


pure fn smap_map<L: copy Eq Ord, T, U>(m: smap<L, T>, 
                                  f: fn(v: T) -> U) -> smap<L, U>
{
    smap{ lits: m.lits,
          vals: vec::map(m.vals, f),
          default: f(m.default) }
}

fn smap_add<L: copy Eq Ord, T, U, V>(m0: smap<L, T>, m1: smap<L, U>,
                                     f: fn(v0: T, v1: U) -> V) -> smap<L, V>
{
    let mut la = ~[], va = ~[], i0 = 0, i1 = 0;
    let dfl = f(m0.default, m1.default);

    while(i0 < m0.lits.len() || i1 < m1.lits.len()) {
        let leftp : bool, rightp : bool;
        if i0 >= m0.lits.len() {
            leftp = false;
            rightp = true;
        } else if i1 >= m1.lits.len() {
            leftp = true;
            rightp = false;
        } else {
            leftp = m0.lits[i0] <= m1.lits[i1];
            rightp = m0.lits[i0] >= m1.lits[i1];
        }
        assert(leftp || rightp);
        let l = if leftp { m0.lits[i0] } else { m1.lits[i1] };
        let v0 = if leftp { &m0.vals[i0] } else { &m0.default };
        let v1 = if rightp { &m1.vals[i1] } else { &m1.default };
        let v = f(*v0, *v1);
        if leftp { i0 += 1; }
        if rightp { i1 += 1; }
        if v != dfl {
            vec::push(la, l);
            vec::push(va, v);
        }
    }
    smap{ lits: la, vals: va, default: dfl }
}

fn smap_reduce<L: copy Eq Ord, T, I>(ms: &[I],
                                     f: fn(i: I) -> smap<L, T>,
                                     g: fn(v0: T, v1: T) -> T) -> smap<L, T>
{
    assert(ms.len() > 0);
    if (ms.len() == 1) {
        f(ms[0])
    } else {
        smap_add(smap_reduce(vec::view(ms, 0, ms.len() / 2), f, g),
                 smap_reduce(vec::view(ms, ms.len() / 2, ms.len()), f, g),
                 g)
    }
}

fn smap0<L: copy Eq Ord, T>(+dfl: T) -> smap<L, T>
{
    smap{ lits: ~[], vals: ~[], default: dfl }
}

fn smap1<L: copy Eq Ord, T>(l: L, +v: T, +dfl: T) -> smap<L, T>
{
    smap{ lits: ~[l], vals: ~[v], default: dfl }
}


impl re : IterBytes {
    fn iter_le_bytes(f: to_bytes::Cb) { (*self).iter_le_bytes(f) }
    fn iter_be_bytes(f: to_bytes::Cb) { (*self).iter_be_bytes(f) }
}
impl<L: IterBytes> node<L> : IterBytes {
    fn iter_le_bytes(f: to_bytes::Cb) {
        match self {
            epsilon => 0u.iter_le_bytes(f),
            lit(ref l) => iter_le_bytes_2(&1u, l, f),
            seq(ref r0, ref r1) => iter_le_bytes_3(&2u, r0, r1, f),
            or(rs) => iter_le_bytes_2(&3u, &to_r(*rs), f),
            star(ref r) => iter_le_bytes_2(&4u, r, f),
            not(ref r) => iter_le_bytes_2(&5u, r, f)
        }
    }
    fn iter_be_bytes(f: to_bytes::Cb) {
        match self {
            epsilon => 0u.iter_be_bytes(f),
            lit(ref l) => iter_be_bytes_2(&1u, l, f),
            seq(ref r0, ref r1) => iter_be_bytes_3(&2u, r0, r1, f),
            or(rs) => iter_be_bytes_2(&3u, &to_r(*rs), f),
            star(ref r) => iter_be_bytes_2(&4u, r, f),
            not(ref r) => iter_be_bytes_2(&5u, r, f)
        }
    }
}
fn to_r<A>(v: &r/[const A]) -> &r/[const A] { v } // XXX

impl<L: Eq> node<L> : Eq {
    pure fn eq(&&other: node<L>) -> bool {
        match self {
            epsilon => match other { epsilon => true, _ => false },
            lit(ls) => match other { lit(lo) => ls == lo, _ => false },
            seq(rs0, rs1) => match other { seq(ro0, ro1) => rs0 == ro0
                                              && rs1 == ro1, _ => false },
            or(rss) => match other { or(ros) => *rss == *ros, _ => false },
            star(rs) => match other { star(ro) => rs == ro, _ => false },
            not(rs) => match other { not(ro) => rs == ro, _ => false },
        }
    }
}
