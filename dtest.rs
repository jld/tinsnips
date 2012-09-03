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
    c.compute_derivs();
    deriv::dump_u8ctx(c, ~[(~"stuff", e)]);
}
