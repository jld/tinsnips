import option::{Option,Some,None};

trait Source {
    fn read(v: &[mut u8]) -> uint;
}

struct LexBuf {
    mut buf: ~[mut u8];
    mut offset: uint;
    mut base: uint;
    mut here: uint;
    mut limit: uint;
    src: Source;

    new(bufsize: uint, src: Source) {
        self.buf = vec::to_mut(vec::from_elem(bufsize, 0));
        self.offset = 0;
        self.base = 0;
        self.limit = 0;
        self.here = 0;
        self.src = src;
    }
    
    fn peek() -> Option<u8> { 
        if self.here >= self.limit && !self.refill() {
            return None;
        }
        return Some(self.buf[self.here - self.offset]);
    }

    fn advance() {
        assert(self.here < self.limit);
        self.here += 1;
    }

    fn rebase() {
        self.base = self.here;
    }

    fn view<R>(f: pure fn(v: &[const u8]) -> R) -> R {
        f(vec::const_view(self.buf,
                          self.base - self.offset,
                          self.here - self.offset))
    }

    fn acquire_space() {
        assert(self.offset <= self.base);
        assert(self.base <= self.here);
        assert(self.here <= self.limit);
        let r_base = self.base - self.offset;
        let r_limit = self.limit - self.offset;
        let buflen = self.buf.len();
        if r_limit - r_base > buflen / 2 {
            let newbuf = vec::to_mut(vec::from_elem(buflen * 2, 0));
            for uint::range(r_base, r_limit) |i| {
                newbuf[i - r_base] = self.buf[i];
            }
            self.buf = newbuf;
        } else {
            for uint::range(r_base, r_limit) |i| {
                self.buf[i - r_base] = self.buf[i];
            }
        }
        self.offset = self.base;
    }

    fn refill() -> bool {
        self.acquire_space();
        let n = self.src.read(vec::mut_view(self.buf, 
                                            self.limit - self.offset,
                                            self.buf.len()));
        return n > 0;
    }
}

