require import List Distr DBool.
clone import Biased.
require Matrix.
require Leak.

type poly_t.
clone import Matrix as PolyMatrix with type ZR.t <- poly_t.

type leak_t = bool list.
type sk_t = matrix * vector * vector.
type pk_t = matrix * vector.
type digest_t.
type commit_t = vector.
type challenge_t = poly_t.
type hint_t = vector.
type resp_t = vector.
type sig_t = challenge_t * resp_t * hint_t.

clone import Leak as SpecLeak with
  type Sig.sk_t <- sk_t,
  type Sig.pk_t <- pk_t,
  type Sig.msg_t <- digest_t,
  type leak_t <- bool list,
  type Sig.sig_t <- sig_t.

op [lossless full uniform] dA : matrix distr.
op [lossless uniform] ds1 : vector distr.
op [lossless uniform] ds2 : vector distr.
op hash : digest_t -> commit_t -> challenge_t.
op dy : vector distr.
op highbits, lowbits : vector -> vector.
op makehint : vector -> vector.
op check_znorm, check_lowbits, checkhint : vector -> bool.

op line12_magicnumber : real.
op dsimz : vector distr.

axiom line12_magic :
  forall c s1, (exists mu w1, c = hash mu w1) => s1 \in ds1 =>
  (dmap dy (fun y =>
      let z = y + (diagc c) *^ s1 in
      if check_znorm z then Some z else None
  )) =
  (dlet (dbiased line12_magicnumber) (fun b => if b then dmap dsimz Some else dunit None)).

module SimplifiedSpec : SchemeL = {
  proc keygen() = {
    var a, s1, s2, t;
    a <$ dA;
    s1 <$ ds1;
    s2 <$ ds2;
    t <- a *^ s1 + s2;
    return ((a, t), (a, s1, s2));
  }
  proc signL(sk : sk_t, mu : digest_t) : sig_t * leak_t = {
    var a, s1, s2, t0;
    var w, w1, y, c, z, h;
    var good;
    var leak;

    leak <- [];

    (* suppress "uninitialized" warning *)
    (c, z, h) <- (ZR.zeror, zerov, zerov);

    (a, s1, s2) <- sk;
    t0 <- lowbits (a *^ s1 + s2);

    good <- false;
    while(!good) {
      leak <- true :: leak;
      y <$ dy;
      w <- a *^ y;
      w1 <- highbits w;
      c <- hash mu w1;
      z <- y + (diagc c) *^ s1;
      leak <- check_znorm z :: leak;
      if(check_znorm z) {
        leak <- check_lowbits z :: leak;
        if(check_lowbits z) {
          h <- makehint (w + (-(diagc c) *^ s2) + (diagc c) *^ t0);
          leak <- checkhint h :: leak;
          if(checkhint h) {
            good <- true;
          }
        }
      }
    }
    return ((c, z, h), leak);
  }
  proc sign(sk : sk_t, mu : digest_t) : sig_t = {
    var sigleak;
    sigleak <- signL(sk, mu);
    return sigleak.`1;
  }
  proc verify(pk:pk_t, mu:digest_t, s:sig_t) = {
    (* NYI *)
    return true;
  }
  proc leakage(pk: pk_t, mu: digest_t, sig: sig_t) : leak_t = {
    var a, t, t0;
    var z, c, h;
    var w, w1, y;
    var good, b;
    var leak;

    leak <- [];
    (a, t) <- pk;
    t0 <- lowbits t;
    good <- false;
    while(!good) {
      leak <- true :: leak;

      b <$ dbiased line12_magicnumber;
      leak <- b :: leak;
      if(b) {
        z <$ dsimz;

        y <$ dy;
        w <- a *^ y;
        w1 <- highbits w;
        c <- hash mu w1;       

        leak <- check_lowbits z :: leak;
        if(check_lowbits z) {
          h <- makehint (a *^ z + (-(diagc c) *^ t) + (diagc c) *^ t0);
          leak <- checkhint h :: leak;
          if(checkhint h) {
            good <- true;
          }
        }
      }
    }
    return leak;
  }
}.

