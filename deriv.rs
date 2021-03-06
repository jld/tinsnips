extern mod std;
use std::{sort,map};
use cmp::{Eq,Ord};
use to_bytes::{IterBytes,iter_bytes_2,iter_bytes_3};
use hash::Hash;

enum RE = uint;
impl RE : Eq {
    pure fn eq(other: &RE) -> bool { *self == **other }
    pure fn ne(other: &RE) -> bool { *self != **other }
}
impl RE : Ord {
    pure fn lt(other: &RE) -> bool { *self < **other }
    pure fn le(other: &RE) -> bool { *self <= **other }
    pure fn ge(other: &RE) -> bool { *self >= **other }
    pure fn gt(other: &RE) -> bool { *self > **other }
}

enum Node<L> {
    Epsilon,
    Lit(L),
    Seq(RE, RE),
    Or(@~[RE]),
    Star(RE),
    Not(RE)
}

struct SMap<L: Copy Eq Ord, T> {
    lits: ~[L],
    vals: ~[T],
    default: T
}

struct Deriv<L: Copy Eq Ord> {
    null: bool,
    d: SMap<L, RE>
}

fn Ctx<L: Copy Const Eq Ord IterBytes>() -> Ctx<L> {
    let nodes = ~[Or(@~[]), Epsilon, Not(RE(0))];
    let rnode = map::HashMap::<Node<L>, RE>();
    for nodes.eachi |i, n| {
        let added = rnode.insert(*n, RE(i));
        assert(added);
    }
    let derivs = ~[@Deriv{ null: false, d: smap0(RE(0)) }];
    let c = Ctx{ nodes: nodes, rnode: rnode, derivs: derivs,
                 r_empty: RE(0), r_eps: RE(1), r_univ: RE(2),
                 busy: false};
    c.compute_derivs();
    return c;
}

struct Ctx<L: Copy Eq Ord IterBytes> {
    mut nodes: ~[Node<L>],
    rnode: map::HashMap<Node<L>, RE>,
    mut derivs: ~[@Deriv<L>],
    mut busy: bool,
    r_empty: RE,
    r_eps: RE,
    r_univ: RE
}

impl<L: Copy Eq Ord IterBytes> Ctx<L> {
    fn intern(n: Node<L>) -> RE {
        let r : RE;
        let mut added = false;
        match self.rnode.find(n) {
            Some(rf) => r = rf,
            None => {
                r = RE(self.nodes.len());
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
    fn empty() -> RE { self.r_empty }
    fn epsilon() -> RE { self.r_eps }
    fn univ() -> RE { self.r_univ }
    fn lit(l: L) -> RE { self.intern(Lit(l)) }

    fn seq(r0: RE, r1: RE) -> RE {
        if r0 == self.r_empty || r1 == self.r_eps { return r0; }
        if r1 == self.r_empty || r0 == self.r_eps { return r1; }
        match copy self.nodes[*r0] {
            Seq(r00, r01) => self.intern(Seq(r00, self.seq(r01, r1))),
            _ => self.intern(Seq(r0, r1))
        }
    }
    
    fn star(r: RE) -> RE {
        if r == self.r_empty || r == self.r_eps || r == self.r_univ {
            return r;
        }
        match self.nodes[*r] {
            Star(_) => r,
            _ => self.intern(Star(r))
        }
    }

    fn not(r: RE) -> RE {
        match self.nodes[*r] {
            Not(nr) => nr,
            _ => self.intern(Not(r))
        }
    }

    fn and(rs: &[RE]) -> RE {
        self.not(self.or(rs.map(|ri| self.not(*ri))))
    }

    fn or(rs: &[RE]) -> RE {
        let mut cases = ~[];
        let mut saw_univ = false;
        for rs.each |r| {
            if *r == self.r_univ { saw_univ = true; break }
            match copy self.nodes[**r] {
                Or(rs) => vec::push_all(cases, *rs),
                _ => vec::push(cases, *r)
            }
        }
        if saw_univ { return self.univ(); }
        sort::quick_sort3(cases);
        vec::dedup(cases);
        if cases.len() == 1 {
            cases[0]
        } else {
            self.intern(Or(@cases))
        }
    }

    fn seqv(rs: &[RE]) -> RE {
        let mut acc = self.epsilon();
        for vec::rev_each(rs) |r| {
            acc = self.seq(*r, acc);
        }
        acc
    }

    fn compute_derivs() {
        while self.derivs.len() < self.nodes.len() {
            let rn = RE(self.derivs.len());
            let d = match copy self.nodes[*rn] {
                Epsilon => Deriv{ null: true, d: smap0(self.empty()) },
                Lit(l) => Deriv{ null: false, d: smap1(l, self.epsilon(),
                                                       self.empty()) },
                Not(r) => {
                    let dr = self.derivs[*r];
                    Deriv{ null: !dr.null,
                           d: smap_map(dr.d, |ri| self.not(*ri)) }
                }
                Star(r) => {
                    let dr = self.derivs[*r];
                    Deriv{ null: true,
                          d: smap_map(dr.d, |ri| self.seq(*ri, rn)) }
                }
                Or(rs) => {
                    let amap = smap_reduce(*rs, 
                                           |r| smap_map(self.derivs[**r].d,
                                                        |nr| ~[*nr]),
                                           |v0, v1| *v0 + *v1);
                    Deriv{ null: vec::any(*rs, |r| self.derivs[*r].null),
                           d: smap_map(amap, |nrs| self.or(*nrs)) }
                }
                Seq(r0, r1) => {
                    let dr0 = self.derivs[*r0];
                    let tmp = smap_map(dr0.d, |ri| self.seq(*ri, r1));
                    if !dr0.null {
                        Deriv{ null: false, d: tmp }
                    } else {
                        let dr1 = self.derivs[*r1];
                        Deriv{ null: dr1.null, 
                               d: smap_add(tmp, dr1.d,
                                           |r0, r1| self.or(~[*r0, *r1])) }
                    }
                }
            };
            vec::push(self.derivs, @d);
        }
    }

    fn dump_with_fn(named: &[(~str, RE)], ltos: pure fn(l: L) -> ~str) {
        for (do named.map |sr| {
            match *sr { (s,r) => fmt!("%s = e%u", s, *r) }
        }).each |s| {
            io::println(*s);
        }
        for (do self.nodes.mapi |i, n| {
            let s = match *n {
                Epsilon => ~"ε",
                Lit(l) => ltos(l),
                Seq(r0, r1) => fmt!("e%u + e%u", *r0, *r1),
                Or(@rs) if rs.len() == 0 => ~"∅",
                Or(@rs) => str::connect(vec::map(rs, |r| fmt!("e%u", **r)),
                                        " | "),
                Star(r) => fmt!("e%u*", *r),
                Not(r) => fmt!("!e%u", *r)
            };
            fmt!("e%u = %s", i, s)
        }).each |s| {
            io::println(*s);
        }
        for (do self.derivs.mapi |i, d| {
            let s_eps = fmt!("e%u %c ε", i, if d.null { '∋' } else { '∌' });
            let v_derivs = do d.d.lits.mapi |j, l| {
                fmt!("d%se%u = e%u", ltos(*l), i, *(d.d.vals[j]))
            };
            let s_dfl = fmt!("d_e%u = e%u", i, *(d.d.default));
            ~[s_eps] + v_derivs + ~[s_dfl]
        }).each |v| {
            for v.each |s| {
                io::println(*s);
            }
        }
    }
}

impl Ctx<u8> {
    fn str(s: &str) -> RE {
        self.seqv(str::byte_slice(s, |v| v.map(|b| self.lit(*b))))
    }

    fn dump(named: &[(~str, RE)]) {
        pure fn btos(+b: u8) -> ~str {
            if 32 < b && b < 127 { fmt!("'%c'", b as char) } 
            else { fmt!("'\\%o'", b as uint) }
        }
        self.dump_with_fn(named, btos);
    }
}


pure fn smap_map<L: Copy Eq Ord, T, U>(m: SMap<L, T>, 
                                  f: fn(v: &T) -> U) -> SMap<L, U>
{
    SMap{ lits: m.lits,
          vals: vec::map(m.vals, f),
          default: f(&m.default) }
}

fn smap_add<L: Copy Eq Ord, T, U, V: Eq>(m0: SMap<L, T>, m1: SMap<L, U>,
                                         f: fn(v0: &T, v1: &U) -> V)
    -> SMap<L, V>
{
    let mut la = ~[], va = ~[], i0 = 0, i1 = 0;
    let dfl = f(&m0.default, &m1.default);

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
        let v = f(v0, v1);
        if leftp { i0 += 1; }
        if rightp { i1 += 1; }
        if v != dfl {
            vec::push(la, l);
            vec::push(va, v);
        }
    }
    SMap{ lits: la, vals: va, default: dfl }
}

fn smap_reduce<L: Copy Eq Ord, T: Eq, I>(ms: &[I],
                                         f: fn(i: &I) -> SMap<L, T>,
                                         g: fn(v0: &T, v1: &T) -> T)
    -> SMap<L, T>
{
    assert(ms.len() > 0);
    if (ms.len() == 1) {
        f(&ms[0])
    } else {
        smap_add(smap_reduce(vec::view(ms, 0, ms.len() / 2), f, g),
                 smap_reduce(vec::view(ms, ms.len() / 2, ms.len()), f, g),
                 g)
    }
}

fn smap0<L: Copy Eq Ord, T>(+dfl: T) -> SMap<L, T>
{
    SMap{ lits: ~[], vals: ~[], default: dfl }
}

fn smap1<L: Copy Eq Ord, T>(l: L, +v: T, +dfl: T) -> SMap<L, T>
{
    SMap{ lits: ~[l], vals: ~[v], default: dfl }
}


impl RE : IterBytes {
    pure fn iter_bytes(e: bool, f: to_bytes::Cb) { (*self).iter_bytes(e, f) }
}
impl<L: IterBytes> Node<L> : IterBytes {
    pure fn iter_bytes(e: bool, f: to_bytes::Cb) {
        match self {
            Epsilon => 0u.iter_bytes(e, f),
            Lit(ref l) => iter_bytes_2(&1u, l, e, f),
            Seq(ref r0, ref r1) => iter_bytes_3(&2u, r0, r1, e, f),
            Or(rs) => iter_bytes_2(&3u, &to_r(*rs), e, f),
            Star(ref r) => iter_bytes_2(&4u, r, e, f),
            Not(ref r) => iter_bytes_2(&5u, r, e, f)
        }
    }
}
pure fn to_r<A>(v: &r/[A]) -> &r/[A] { v } // XXX

impl<L: Eq> Node<L> : Eq {
    pure fn eq(other: &Node<L>) -> bool {
        match self {
            Epsilon => match *other { Epsilon => true, _ => false },
            Lit(ls) => match *other { Lit(lo) => ls == lo, _ => false },
            Seq(rs0, rs1) => match *other { Seq(ro0, ro1) => rs0 == ro0
                                              && rs1 == ro1, _ => false },
            Or(rss) => match *other { Or(ros) => *rss == *ros, _ => false },
            Star(rs) => match *other { Star(ro) => rs == ro, _ => false },
            Not(rs) => match *other { Not(ro) => rs == ro, _ => false },
        }
    }
    pure fn ne(other: &Node<L>) -> bool { !(self == *other) }
}
