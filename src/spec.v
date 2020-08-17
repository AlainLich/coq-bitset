Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.

Require Import ZArith Arith Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BitRepr.

Definition repr n (bs : BITS n) E := E = [set x : 'I_n | getBit bs x].

Lemma repr_rec n (bs : BITS n) (E : {set 'I_n.+1}) b :
  repr [tuple of b :: bs] E ->
  repr bs [set x : 'I_n | inord(x.+1) \in E ].
Proof.
    by move->; apply/setP=> x; rewrite !inE inordK //; exact: ltn_ord.
Qed.

Variable n : nat.             (* Represents Bit Size *)
Implicit Types (bs : BITS n) (E: {set 'I_n}).

Lemma eq_repr bs bs' E E' : repr bs E -> repr bs' E' ->
    (bs == bs') = (E == E').
Proof.
move=> -> ->; apply/eqP/eqP => [ -> // |].
move/setP=> hs; apply: allBitsEq=> i i_ord.
by have := hs (Ordinal i_ord); rewrite !inE.
Qed.

Lemma empty_repr : repr (zero n) set0.
Proof.
by apply/setP=> i; rewrite !inE -fromNat0 getBit_zero.
Qed.

Lemma subset_repr k (k_le_n : k <= n) :
  repr (decB (shlBn #1 k)) [set x : 'I_n | x < k].
Proof.  
rewrite makeOnes ?subnKC //= => ?.
apply/setP => i; rewrite !inE getBit_tcast getBit_catB.
by case: ifP => h; rewrite ?getBit_ones // -fromNat0 getBit_zero.
Qed.

Lemma singleton_repr (k: 'I_n) : repr (setBit #0 k true) [set k].
Proof.
      (* recall that #0: binary representation of 0 with unknown # bits , lemma is
          therefore  {k} is represented by k-th bit set *)
apply/setP => i.    (* also intro the quantifier hidden in =i *)
rewrite !inE.
apply/eqP/idP => [-> | ]. 
  - rewrite setBitThenGetSame =>//.
  - (* it seems that one can only read bits that have been set? *)
     apply contraTeq => /eqP  i_neq_k. 
     rewrite setBitThenGetDistinct ?ltn_ord ?getBit_zero //= .
     by move/val_inj => h; apply: i_neq_k.  (* bien compliqué pour symmetrie! auto foire *)

(* Orig :
    apply/setP=> i; rewrite !inE; apply/eqP/idP => [->|].
    by rewrite setBitThenGetSame.
    apply: contraTeq => /eqP i_neq_k.
    rewrite setBitThenGetDistinct ?ltn_ord ?getBit_zero //.
    (* XXX: The impedance here should be fixed *)
    by move/val_inj => h; apply: i_neq_k.
 *)
     
Qed.

(* XXX: I disagree with this but it is a "mal menor" for now *)
Lemma indexP (T : eqType) d (x : T) s idx :
  d != x -> nth d s idx = x ->
  (forall j, j < size s -> nth d s j = x -> idx <= j) ->
  index x s = idx.
Proof.
elim: s idx => [|s ss ihs] idx hneq; first by move/eqP: hneq; rewrite nth_nil.
case: idx => /= [->|idx]; first by rewrite eqxx.
move=> /ihs-/(_ hneq) {ihs} ihs hj.
case: ifP => [/eqP|] he; first by have /= := hj 0 erefl he; rewrite ltn0.
by congr S; apply: ihs => j hjs hnt; have := hj j.+1 hjs hnt.
Qed.

Lemma index_repr bs x E (hr : repr bs E) (h_in : x \in E) :
  index true bs = [arg min_(k < x in E) k].
Proof.
case: arg_minP => // i xin ihh.
(* XXX: I disagree with this: there is a better solution but requires
   a different library structure *)
have/indexP: nth false bs i = true.
  by have/setP:= hr => /(_ i); rewrite xin inE => ->.
apply=> // j hj hnt; rewrite size_tuple in hj.
by have:= ihh (Ordinal hj); apply; rewrite hr inE.
Qed.

Fact nth_nil_isFalse:  (nth false [::]) =1 (fun x => false).
  Proof.
      - by move => aa; apply  nth_nil.
Qed.

(* I do not like having to state these... but simpler for now! *)
Fact addnS : forall m , m.+1 = (m + 1).
Proof. Eval simpl in add1n. (* 1 + n = n.+1*)
       by move => m; rewrite -add1n; auto with arith.  
Qed.

Fact nth_BumpFun: forall x l,
      (fun i => (nth false (x::l)) (i+1)) =1 (fun i =>  (nth false l) i ).
Proof.
  move => x l i //=. 
  have HRw:= (nth_behead false (x::l) i).
  replace (behead (x :: l)) with l in HRw.
  rewrite HRw;   replace (i.+1) with (i + 1) . auto.
  by rewrite  -addnS.
  by simpl.  
Qed.
  

Fact countZero:  forall size, count (nth false [::]) (iota 0 size) = 0.
Proof.
  move => size. induction size. by simpl.
        have eqZero:=( eq_count  nth_nil_isFalse).
        have ioplus := (iota_add  0 size 1).
         - replace  (iota 0 size.+1) with (iota 0 size ++ iota (0 + size) 1).
             by rewrite  count_cat !IHsize => //= ; rewrite !addn0 !add0n nth_nil =>//=.              simpl .  rewrite !add0n. simpl in ioplus. rewrite add0n in ioplus.
             rewrite <- ioplus.
             have iop2:= (iota_add 0 1 size).
             rewrite ->  (Nat.add_comm) ; rewrite iop2 => //=.
Qed.

Fact countBump: forall x xs,     count (nth false (x :: xs)) (iota 1 (size xs))
                                 = count (nth false xs) (iota 0 (size xs)).
Proof.
  move => x xs.
      have HbumpFun := ( nth_BumpFun x xs).
      have Heqcounts := ( eq_count   HbumpFun).
      unfold eqfun in Heqcounts. move : ( Heqcounts (iota 0 (size xs))) => Heqc2.
      rewrite -Heqc2.
      admit.  (** seems a simple thing arounf functions .... equality...*)
  Search nth.
 Admitted.


(* XXX: Same as above *)
Lemma count_nth_cons x xs :
      count (nth false (x :: xs)) (iota 0 (size xs).+1) =
  x + count (nth false xs)        (iota 0 (size xs)).
Proof.
  have io1:= ( iota_add 0 (size xs) 1).
  replace (iota 0 (size xs).+1) with (iota 0 (size xs + 1)).
  rewrite io1; rewrite  !add0n.
  simpl.
  set (szXS:= (size xs)).
  have io2:=   (iota_add 0 (szXS) 1).
  move : io2 => //=; rewrite !add0n => io2. rewrite -io2 => //=.
  rewrite io1. rewrite !add0n -io2 =>//= .
  have io3 :  (iota 0 (szXS + 1)) = 0 :: (iota 1 szXS).
       by rewrite -> Nat.add_comm; rewrite ->iota_add; simpl; rewrite !add0n.
  rewrite io3.
  have  co1 := (count_cat _ (0::nil) (iota 1 szXS)).
  rewrite co1 =>//=. rewrite addn0. congr addn.
  apply  countBump.
  by rewrite  -addnS.
  (* Non working original :
    by congr addn; elim: (size _) 0 => //= size ihsz z; rewrite ihsz. Qed.
  *)

Qed.

Lemma count_repr bs E : repr bs E -> count_mem true bs = #|E|.
Proof.
move=> -> {E}; rewrite cardsE cardE size_filter.
rewrite -(count_map val) unlock val_ord_enum.
case: bs => s ss; elim: s n ss => /= [ | x xs ihs] m /eqP <-{m} //.
by rewrite count_nth_cons -ihs //; congr addn; case: x.
Qed.

End BitRepr.
