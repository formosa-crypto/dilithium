require import AllCore.
require import Li2_params.
require import List.
require import IntDiv.
require import SpongeROM.
import Li2_Matrix.
require import Li2_packing.
import Li2_PolyReduceZp.
require import BitEncoding.
import BS2Int.
import Zp.

op int_to_byte (x : int) = Byte.mkword (BS2Int.int2bs 8 x).
op byte_to_int (x : byte) = bs2int (Byte.ofword x).

module Expand_impl(H : SpongeRO) = {
  proc expandA_entry(rho : byte list, i j : int) : R = {
    var deg : int;
    var p : R;
    var ext;
    var val;

    H.reset(SHAKE128);
    H.absorb(rho);
    H.absorb([int_to_byte j; int_to_byte i]);
    deg <- 0;
    p <- zeroXnD1;
    while(deg < Li2_n) {
      ext <@ H.squeeze(3);
      val <- byte_to_int (nth witness ext 0)
             + (byte_to_int (nth witness ext 1)) * (2 ^ 8)
             + (byte_to_int ((nth witness ext 2)) %% 128) * (2 ^ 16);
      if(val < Li2_q) {
        p <- p + inzmod val ** pinject (BasePoly.polyXn deg);
        deg <- deg + 1;
      }
    }
    return p;
  }

  proc expandA(rho : byte list) : matrix = {
    var result : (int -> int -> R);
    var i, j : int;
    var entry;
    result <- fun _ _ => zeroXnD1;
    i <- 0;
    j <- 0;
    while(i < Li2_k) {
      while(j < Li2_l) {
        entry <@ expandA_entry(rho, i, j);
        result <- fun r c => if r = i && c = j then entry else result r c;
        j <- j + 1;
      }
      i <- i + 1;
    }
    return offunm result;
  }

  proc expandS_entry(rho' : byte list, i : int) : R = {
    var deg : int;
    var p : R;
    var ext;
    var val;

    p <- zeroXnD1;

    H.reset(SHAKE256);
    H.absorb(rho');
    H.absorb([int_to_byte i; int_to_byte 0]);
    deg <- 0;
    while(deg < Li2_n) {
      ext <@ H.squeeze(1);
      val <- (byte_to_int (nth witness ext 0)) %% 16;
      if(val <= 2 * Li2_eta) {
        p <- p + (inzmod val ** pinject (BasePoly.polyXn deg));
        deg <- deg + 1;
      }
      if(deg < Li2_n) {
        val <- (byte_to_int (nth witness ext 0)) %/ 16;
        if(val <= 2 * Li2_eta) {
          p <- p + (inzmod val ** pinject (BasePoly.polyXn deg));
          deg <- deg + 1;
        }
      }
    }
    return p;
  }

  proc expandS(rho' : byte list) : vector * vector = {
    var s1, s2 : (int -> R);
    var i : int;
    var entry;

    s1 <- fun _ => zeroXnD1;
    i <- 0;
    while(i < Li2_l) {
      entry <@ expandS_entry(rho', i);
      s1 <- fun x => if x = i then entry else s1 x;
      i <- i + 1;
    }

    s2 <- fun _ => zeroXnD1;
    i <- 0;
    while(i < Li2_k) {
      entry <@ expandS_entry(rho', Li2_l + i);
      s1 <- fun x => if x = i then entry else s1 x;
      i <- i + 1;
    }

    return (offunv s1, offunv s2);
  }

  proc expandMask_entry(rho' : byte list, kappa : int) : R = {
    var entry : R;
    var buf : byte list;

    H.reset(SHAKE256);
    H.absorb(rho');
    H.absorb([int_to_byte (kappa %% 256); int_to_byte (kappa %/ 256)]);
    (* Next two lines are level 3 settings. *)
    (* TODO abstract with respect to gamma2 value? *)
    buf <@ H.squeeze(Li2_n * 20 %/ 8);
    entry <- unpack_z_entry buf;

    return entry;
  }

  proc expandMask(rho' : byte list, nonce : int) : vector = {
    var v : R list;
    var entry : R;
    var kappa : int;
    var i : int;

    v <- [];
    i <- 0;
    while(i < Li2_l) {
      kappa <- Li2_l * nonce + i;
      entry <@ expandMask_entry(rho', kappa);
      v <- rcons v entry;
      i <- i + 1;
    }
    return offunv (fun i => nth witness v i);
  }

  proc sampleInBall(c_tilde : byte list) : polyXnD1 = {
    var coeffs : Zp list;
    var sign_bytes : byte list;
    var signs : bool list;

    var i : int;
    var j : int;
    var b : byte list;

    H.reset(SHAKE128);
    H.absorb(c_tilde);
    sign_bytes <@ H.squeeze(8);
    signs <- flatten (map Byte.ofword sign_bytes);

    coeffs <- nseq Li2_n (inzmod 0);

    i <- Li2_n - Li2_tau;
    while(i < Li2_n) {
      (* do-while.
       * rejection sampling to get j <= i. *)
      b <@ H.squeeze(1);
      j <- byte_to_int (oget (ohead b));
      while(i < j) {
        b <@ H.squeeze(1);
        j <- byte_to_int (oget (ohead b));
      }
      (* coeffs[i] = coeffs[j] *)
      coeffs <- put coeffs i (oget (onth coeffs j));
      (* coeffs[j] = 1 - 2 * sign *)
      coeffs <- put coeffs j (inzmod (1 - 2 * b2i (oget (ohead signs))));
      signs <- behead signs;
      
      i <- i + 1;
    }

    return pinject (BasePoly.polyL coeffs);
  }
}.
