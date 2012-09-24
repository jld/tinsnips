fn main() {
    let c = deriv::Ctx();
    let e = c.seqv(~[c.str("/*"),
                     c.not(c.seqv(~[c.univ(), c.str("*/"), c.univ()])),
                     c.str("*/")]);
    c.dump(~[(~"stuff", e)]);
}
