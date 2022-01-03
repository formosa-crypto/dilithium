require import AllCore.
require import Li2_params.
require import IntDiv.

op mod_pm m d =
  let r = m %% d in
  if r < m %/ 2 then r else r - d.

module Rounding_impl = {
  proc power2round(r : int, d : int) : int * int = {
    var r0 : int;
    r <- r %% Li2_q;
    r0 <- mod_pm r (2 ^ d);
    return ((r - r0) %/ (2 ^ d), r0);
  }

  proc decompose(r : int, alpha : int) : int * int = {
    var r0, r1 : int;
    r <- r %% Li2_q;
    r0 <- mod_pm r alpha;
    if(r - r0 = Li2_q - 1) {
      r1 <- 0;
      r0 <- r0 - 1;
    }
    else {
      r1 <- (r - r0) %/ alpha;
    }
    return (r1, r0);
  }

  proc highbits (r : int, alpha : int) : int = {
    var r0, r1 : int;
    (r1, r0) <@ decompose(r, alpha);
    return r1;
  }

  proc lowbits (r : int, alpha : int) : int = {
    var r0, r1 : int;
    (r1, r0) <@ decompose(r, alpha);
    return r0;
  }

  proc makeHint (z : int, r : int, alpha : int) = {
    var r1, v1 : int;
    r1 <@ highbits(r, alpha);
    v1 <@ highbits(r + z, alpha);
    return b2i (!(r1 = v1));
  }

  proc useHint(h : int, r : int, alpha : int) : int = {
    var m, r1, r0, result : int;
    m <- (Li2_q - 1) %/ alpha;
    (r1, r0) <@ decompose(r, alpha);
    if (h = 1 && 0 < r0) {
      result <- (r1 + 1) %% m;
    }
    elif (h = 1 && r0 <= 0) {
      result <- (r1 - 1) %% m;
    }
    else {
      result <- r1;
    }
    return result;
  }
}.


