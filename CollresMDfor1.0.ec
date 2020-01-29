require import AllCore DBool List Int IntExtra.

(* The type of plaintexts: bitstrings of length k, l *)
type block.
type state.
type msg.

op uMsg: (msg * msg) distr.

const IV: state.
 
const z0: block.

(** f: ハッシュ関数 **)
op f : block -> state -> state.
op fstar : block list -> state -> state.
op pad : msg -> block list.
op MD (m: msg) = fstar (pad m) IV.

op coll(xy, xy': block * state) =
  xy <> xy' && f (fst xy) (snd xy) = f (fst xy') (snd xy').
 
axiom suffix_free:
  forall (m, m': msg, bl: block list), m <> m' => pad m <> bl ++ pad m'.

axiom fstar_nil:
  forall (y: state), fstar [] y = y.

axiom fstar_cons:
  forall (x: block, y: state, xs: block list), fstar (x::xs) y = fstar xs (f x y).


axiom size_behead : forall (xs: 'a list),
  0 < size xs => size(behead xs) < size xs.


op head(xs : block list) = head z0 xs.

module CR_MD = {
  proc oracle(m: msg) : state = {
    var xs: block list <- pad m;
    var y : state <- IV;
    while (xs <> []) {
      y <- f (head z0 xs) y;
      xs <- behead xs;
    }
    return y;
  }

  proc main() : bool = {
    var m1, m2 : msg;
    var h1, h2 : state;
    (m1, m2) <$ uMsg;
    h1 <@ oracle(m1);
    h2 <@ oracle(m2);
    return (m1 <> m2 && h1 = h2);
  }
}.

module CR_f = {
  proc adv_b() : (block * state) * (block * state) = {
    var m1, m2 : msg;
    var y1, y2 : state;
    var xs', xs1, xs2 : block list;

    (m1, m2) <$ uMsg;
    xs1 <- pad m1; y1 <- IV;
    xs2 <- pad m2; y2 <- IV;
    xs' <- [];
    
    while (size xs2 < size xs1) {
      y1 <- f(head z0 xs1) y1;
      xs' <- xs' ++ [head z0 xs1];
      xs1 <- behead xs1;
    }
    while (size xs1 < size xs2) {
      y2 <- f(head z0 xs2) y2;
      xs' <- xs' ++ [head z0 xs2];
      xs2 <- behead xs2;
    }
    while (! (coll((head z0 xs1), y1) ((head z0 xs2), y2)) && xs1 <> [] ) {
      y1 <- f (head z0 xs1) y1; xs1 <- behead xs1;
      y2 <- f (head z0 xs2) y2; xs2 <- behead xs2;
    }
    return (((head z0 xs1), y1), ((head z0 xs2), y2));
  }

  proc main(): bool = {
    var xy1, xy2: block * state;
    (xy1, xy2) <@ adv_b();
    return coll xy1 xy2;
  }
}.

prover ["Alt-Ergo"].

lemma MD_Collision_Resistance &m :
    Pr[CR_MD.main() @ &m : res] <= Pr[CR_f.main() @ &m : res].
    proof. byequiv=>//.
    proc. 
    inline CR_f.adv_b. seq 1 1 : (={m1, m2}). auto.
 
    seq 1 0 : ((h1 = MD m1){1} && ={m1, m2}). 
    inline *; sp. wp.
    while{1} (fstar xs y = MD m1){1} (size xs{1}).
    auto. smt(fstar_cons). 
    skip. by progress; smt.
    seq 1 0 : ((h1 = MD m1 && h2 = MD m2){1} && ={m1, m2}).
    inline*. sp. wp.
    while{1} (fstar xs y = MD m2){1} (size xs{1}). 
    by auto; smt(fstar_cons). 
    skip. by progress; smt. 
sp.
wp.
(* m1 = m2 *)
case (m1{2} = m2{2}).
while{2} true (size xs1{2}). 
progress. wp. skip. by progress; smt().
rcondf{2} 1 => //.
rcondf{2} 1 => //.
skip. progress. smt.

(* m1 <> m2 /\ size xs1 <= size xs2 *)
case (size xs1{2} <= size xs2{2}). 
rcondf{2} 1. auto.  smt(size_behead).
while{2} (fstar xs1 y1 = MD m1 &&
    fstar xs2 y2 = MD m2 &&
    (xs1 = xs2 => y1 <> y2) &&
    size xs1 = size xs2){2} (size xs1){2}. 
progress; auto; smt.
while{2} (fstar xs2 y2 = MD m2 &&
    xs' ++ xs2 = pad m2 &&
    size xs1 <= size xs2){2}
    (size xs2 - size xs1){2}. 
by auto; progress; smt.
skip; by progress; smt.

(* m1 <> m2 /\ size xs2 < size xs1 *)

  wp.
  while{2} (fstar xs1 y1 = MD m1 && fstar xs2 y2 = MD m2 && size xs1 = size xs2 && (xs1 = xs2 => y1 <> y2)){2} (size xs1){2}. auto. smt.

(* こちらの方法でも証明可能, ただしby smtによる外部ソルバ適用回数が増える
while{2}  ((xs2{2} = pad m2{2} /\
    y2{2} = IV /\
    xs'{2} ++ xs1{2} = pad m1{2} /\
    (h1{1} = MD m1{1} &&
    h2{1} = MD m2{1}) && ={m1, m2}) /\
    m1{2} <> m2{2} /\
    size xs1{2} = size xs2{2} /\
    (fstar xs1 y1 = MD m1)){2} (size xs2){2}. auto. progress; by smt.
while{2} (fstar xs1 y1 = MD m1 && xs' ++ xs1 = pad m1 && size xs2 <= size xs1){2} (size xs1){2}. auto. progress; by smt.  
skip. progress; by smt.
*)

seq{2} 0 1 : 
    ((xs2{2} = pad m2{2} /\
    y2{2} = IV /\
    xs'{2} ++ xs1{2} = pad m1{2} /\
    (h1{1} = MD m1{1} &&
    h2{1} = MD m2{1}) && ={m1, m2}) /\
    m1{2} <> m2{2} /\
    size xs1{2} = size xs2{2} /\
    (fstar xs1 y1 = MD m1){2}).
while{2} (fstar xs1 y1 = MD m1 &&
    xs' ++ xs1 = pad m1 &&
    size xs2 <= size xs1){2}
    (size xs1){2}.
by auto; progress; smt.
skip. progress; by smt.
rcondf{2} 1. progress. skip. progress. smt.
skip. by progress; smt.
qed.
