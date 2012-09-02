import deriv::{epsilon,lit,seq,or,star,not,re};

fn rstr(c: deriv::ctx<u8>, s: &str) -> re {
    c.seqv(str::byte_slice(s, |v| v.map(|b| c.lit(b))))
}

fn main()
{
    let c = deriv::ctx();
    let e = c.seqv(~[rstr(c, "/*"),
                     c.not(c.seqv(~[c.univ(), rstr(c, "*/"), c.univ()])),
                     rstr(c, "*/")]);
    io::println(fmt!("stuff = e%u", *e));
    c.compute_derivs();

    fn btos(b: u8) -> ~str {
        if 32 < b && b < 127 { fmt!("'%c'", b as char) } 
        else { fmt!("'\\%o'", b as uint) }
    }

    do c.nodes.iteri |i, n| {
        let s = match n {
            epsilon => ~"ε",
            lit(b) => btos(b),
            seq(r0, r1) => fmt!("e%u + e%u", *r0, *r1),
            or(@rs) if rs.len() == 0 => ~"∅",
            or(@rs) => str::connect(vec::map(rs, |r| fmt!("e%u", *r)), " | "),
            star(r) => fmt!("e%u*", *r),
            not(r) => fmt!("!e%u", *r)
        };
        io::println(fmt!("e%u = %s", i, s))
    }
    do c.derivs.iteri |i, d| {
        io::println(fmt!("e%u %c ε", i, if d.null { '∋' } else { '∌' }));
        do d.d.lits.iteri |j, b| {
            io::println(fmt!("d%se%u = e%u", btos(b), i, *(d.d.vals[j])))
        }
        io::println(fmt!("d_e%u = e%u", i, *(d.d.default)));
    }
}
