fn main() {
    let c = deriv::ctx();
    let e = c.seqv(~[c.str("/*"),
                     c.not(c.seqv(~[c.univ(), c.str("*/"), c.univ()])),
                     c.str("*/")]);
    c.compute_derivs();
    c.dump(~[(~"stuff", e)]);
}
