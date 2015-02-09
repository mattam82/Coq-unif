(* Authors: Beta Ziliani and Cyril Cohen *)
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path fintype.

(******************************************************************************)
(* This files definies a totally ordered and decidable relations on a         *)
(* type as canonical structure.  One need to import Order.Theory to get       *)
(* the theory of such relations. The scope order_scope (%ord) contains        *)
(* fancier notation for this kind of ordeeing.                                *)
(*                                                                            *)
(*           ordType == the type of ordered types                             *)
(* OrdType ord_mixin == builds an ordtype from a mixing containing a proof of *)
(*                             irreflexivity, transitivity and totality       *)
(*                                                                            *)
(* We provide a canonical structure of ordType for natural numbers (nat)      *)
(* for finType and for pairs of ordType by lexicographic orderering.          *)
(*                                                                            *)
(* leP ltP ltgtP are the three main lemmas for case analysis, note that       *)
(* they are doing a bit more than the one for natural numbers.                *)
(*                                                                            *)
(* We also provide specialized version of some theorems from path.v.          *)
(*                                                                            *)
(* There are three distinct uses of the symbols <, <=, > and >=:              *)
(*    0-ary, unary (prefix) and binary (infix).                               *)
(* 0. <%ord, <=%ord, >%ord, >=%ird stand respectively for lt, le, gt and ge.  *)
(* 1. (< x),  (<= x), (> x),  (>= x) stand respectively for                   *)
(*    (gt x), (ge x), (lt x), (le x).                                         *)
(*    So (< x) is a predicate characterizing elements smaller than x.         *)
(* 2. (x < y), (x <= y), ... mean what they are expected to.                  *)
(*  These convention are compatible with haskell's,                           *)
(*   where ((< y) x) = (x < y) = ((<) x y),                                   *)
(*   except that we write <%R instead of (<).                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope order_scope with ord.
Local Open Scope order_scope.

Reserved Notation "<= y" (at level 35).
Reserved Notation ">= y" (at level 35).
Reserved Notation "< y" (at level 35).
Reserved Notation "> y" (at level 35).
Reserved Notation "<= y :> T" (at level 35, y at next level).
Reserved Notation ">= y :> T" (at level 35, y at next level).
Reserved Notation "< y :> T" (at level 35, y at next level).
Reserved Notation "> y :> T" (at level 35, y at next level).

Module Order. 
Module T.
Section RawMixin.

Structure mixin_of (T : eqType) := 
  Mixin {ordering : rel T; 
         _ : irreflexive ordering;
         _ : transitive ordering;
         _ : forall x y, [|| ordering x y, x == y | ordering y x]}.

End RawMixin.

Section ClassDef.

Record class_of (T : Type) := Class {
   base : Equality.class_of T; 
   mixin : mixin_of (Equality.Pack base T)}.

Local Coercion base : class_of >-> Equality.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b (m0 : mixin_of (EqType T b)) := 
  fun m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation ordType := type.
Notation OrdMixin := Mixin.
Notation OrdType T m := (@pack T _ m _ id).
Notation "[ 'ordType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'ordType' 'of' T 'for' cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType' 'of' T ]") : form_scope.
End Exports.
End T.
Import T.Exports.

Module Def.
Section Def.
Variable (T : ordType).

Definition lt : rel T := (T.ordering (T.mixin (T.class T))).
Local Notation "x < y" := (lt x y) : order_scope.

Definition le : rel T := fun x y => (x == y) || (x < y).
Local Notation "x <= y" := (le x y) : order_scope.

Definition ge : simpl_rel T := [rel x y | y <= x].
Definition gt : simpl_rel T := [rel x y | y < x].
Definition leif x y C : Prop := ((x <= y) * ((x == y) = C))%type.
Definition min x y : T := if x <= y then x else y.
Definition max x y : T := if y <= x then x else y.

Definition le_of_leif x y C (le_xy : @leif x y C) := le_xy.1 : le x y.

End Def.
End Def.

Import Def.
Prenex Implicits lt le leif min max.
Notation lt := Def.lt.
Notation le := Def.le.
Notation gt := Def.gt.
Notation ge := Def.ge.
Notation leif := Def.leif.
Notation min := Def.min.
Notation max := Def.max.

Module Import Syntax.

Notation "<%ord" := lt : order_scope.
Notation ">%ord" := gt : order_scope.
Notation "<=%ord" := le : order_scope.
Notation ">=%ord" := ge : order_scope.
Notation "<?=%ord" := leif : order_scope.

Notation "< y" := (gt y) : order_scope.
Notation "< y :> T" := (< (y : T)) : order_scope.
Notation "> y" := (lt y) : order_scope.
Notation "> y :> T" := (> (y : T)) : order_scope.

Notation "<= y" := (ge y) : order_scope.
Notation "<= y :> T" := (<= (y : T)) : order_scope.
Notation ">= y"  := (le y) : order_scope.
Notation ">= y :> T" := (>= (y : T)) : order_scope.

Notation "x < y"  := (lt x y) : order_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : order_scope.
Notation "x > y"  := (y < x) (only parsing) : order_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : order_scope.

Notation "x <= y" := (le x y) : order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : order_scope.
Notation "x >= y" := (y <= x) (only parsing) : order_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : order_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : order_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : order_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : order_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : order_scope.

Notation "x <= y ?= 'iff' C" := (leif x y C) : order_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : order_scope.

Coercion le_of_leif : leif >-> is_true.
End Syntax.

Module Theory.
Section Theory.

Variable T : ordType.
Implicit Types x y z : T.

Lemma lt_irreflexive : irreflexive (@lt T). 
Proof. by case: T => s [b [m]]. Qed.

Lemma ltxx x : x < x = false. Proof. exact: lt_irreflexive. Qed.

Lemma lt_trans : transitive (@lt T). 
Proof. by case: T=>s [b [m]]. Qed.

Lemma lt_total x y : [|| x < y, x == y | y < x]. 
Proof. by case: T x y => s [b [m]]. Qed. 

Lemma lexx x : x <= x. Proof. by rewrite /le eqxx. Qed.

Lemma le_trans : transitive (@le T).
Proof.
rewrite /le => y x z /predU1P [-> //|xy] yz; apply/orP; right.
by move: yz => /predU1P [<- //|/(lt_trans xy) ->].
Qed.

Lemma ltW x y : x < y -> x <= y.
Proof. by rewrite /le => ->; rewrite orbT. Qed.

Lemma lt_nsym (x y : T) : lt x y -> lt y x -> False.
Proof. by move=> xy /(lt_trans xy); rewrite ltxx. Qed.

Hint Resolve lexx ltxx ltW.

Lemma le_eqVlt x y : (x <= y) = (x == y) || (x < y). Proof. done. Qed.

Lemma lt_neqAle x y : (x < y) = (x != y) && (x <= y).
Proof. by rewrite /le; case: (altP eqP) => // ->. Qed.

Lemma gt_eqF x y : y < x -> x == y = false.
Proof. by apply: contraTF => /eqP ->; rewrite ltxx. Qed.

Lemma lt_eqF x y : x < y -> x == y = false.
Proof. by move=> hyx; rewrite eq_sym gt_eqF. Qed.

CoInductive le_xor_gt (x y : T) : bool -> bool -> Set :=
  | LerNotGt of x <= y : le_xor_gt x y true false
  | GtrNotLe of y < x  : le_xor_gt x y false true.

CoInductive lt_xor_ge (x y : T) : bool -> bool -> Set :=
  | LtrNotGe of x < y  : lt_xor_ge x y false true
  | GerNotLt of y <= x : lt_xor_ge x y true false.

CoInductive comparer x y :
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerEq of x = y : comparer x y
    true true true true false false
  | ComparerLt of x < y : comparer x y
    false false true false true false
  | ComparerGt of x > y : comparer x y
    false false false true false true.

Lemma ltgtP x y :
  comparer x y (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y).
Proof.
rewrite /le [y == x]eq_sym.
have := (altP (x =P y), boolP (lt x y), boolP (lt y x), lt_total x y).
rewrite /le => [] [[[[->|neq_xy]]]]; first by rewrite ltxx; constructor.
by move=> [xy [/lt_nsym|]|? []] //=; constructor.
Qed.

Lemma leP x y : le_xor_gt x y (x <= y) (y < x).
Proof. by have [->|xy|xy] := ltgtP; constructor => //; rewrite ltW. Qed.

Lemma ltP x y : lt_xor_ge x y (y <= x) (x < y).
Proof. by have [->|xy|xy] := ltgtP; constructor => //; rewrite ltW. Qed.

Lemma le_total : total (@le T).
Proof. by move=> x y; have [] := ltgtP. Qed.

Hint Resolve le_total.

Lemma le_asym : antisymmetric (le : rel T).
Proof. by move=> x y; case: ltgtP. Qed.

Lemma eq_le x y : (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP=> [->|/le_asym]; rewrite ?lexx. Qed.

Lemma le_lt_trans y x z : x <= y -> y < z -> x < z.
Proof. by rewrite !le_eqVlt => /orP[/eqP -> //|/lt_trans]; apply. Qed.

Lemma lt_le_trans y x z : x < y -> y <= z -> x < z.
Proof. by rewrite !le_eqVlt => lxy /orP[/eqP <- //|/(lt_trans lxy)]. Qed.

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /leif le_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lt_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // lt_eqF.
Qed.

Lemma lt_asym x y : x < y < x = false.
Proof. by apply/negP=> /andP [/lt_trans hyx /hyx]; rewrite ltxx. Qed.

Lemma le_anti : antisymmetric (@le T).
Proof. by move=> x y; rewrite -eq_le=> /eqP. Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof. by rewrite lt_neqAle -andbA -eq_le eq_sym; case: (_ == _). Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC lt_le_asym. Qed.

Definition lter_anti := (=^~ eq_le, lt_asym, lt_le_asym, le_lt_asym).

Lemma lt_geF x y : x < y -> (y <= x = false).
Proof.
by move=> xy; apply: contraTF isT=> /(lt_le_trans xy); rewrite ltxx.
Qed.

Lemma le_gtF x y : x <= y -> (y < x = false).
Proof. by apply: contraTF=> /lt_geF->. Qed.

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).

Lemma lt_sorted_uniq_le (s : seq T) :
   sorted lt s = uniq s && sorted le s.
Proof.
case: s => //= n s; elim: s n => //= m s IHs n.
rewrite inE lt_neqAle negb_or IHs -!andbA.
case sn: (n \in s); last do !bool_congr.
rewrite andbF; apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
by rewrite eq_le lenm; apply: (allP (order_path_min le_trans le_ms)).
Qed.

Lemma sort_le_sorted (s : seq T) : sorted le (sort le s).
Proof. by rewrite sort_sorted. Qed.

Lemma eq_sorted_lt (s1 s2 : seq T) :
  sorted lt s1 -> sorted lt s2 -> s1 =i s2 -> s1 = s2.
Proof. by apply: eq_sorted_irr => //; apply: lt_trans. Qed.

Lemma eq_sorted_le (s1 s2 : seq T) :
   sorted le s1 -> sorted le s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. by apply: eq_sorted; [apply: le_trans|apply: le_anti]. Qed.

Lemma sort_lt_sorted (s : seq T) : sorted lt (sort le s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma sort_le_id (s : seq T) : sorted le s -> sort le s = s.
Proof.
by move=> ss; apply: eq_sorted_le; rewrite ?sort_le_sorted // perm_sort.
Qed.

End Theory. 

Section NatOrd.
Lemma irr_ltn_nat : irreflexive ltn. Proof. by move=> x; rewrite /= ltnn. Qed.
Lemma trans_ltn_nat : transitive ltn. Proof. exact: ltn_trans. Qed.
Lemma total_ltn_nat : forall x y, [|| x < y, x == y | y < x]%N. 
Proof. by move=>*; case: ltngtP. Qed.

Definition nat_ordMixin := OrdMixin irr_ltn_nat trans_ltn_nat total_ltn_nat.
Canonical nat_ordType := OrdType nat nat_ordMixin.
End NatOrd.

Section ProdOrd.
Variables K T : ordType.

(* lexicographic ordering *)
Definition lex : rel (K * T) := 
  fun x y => if x.1 == y.1 then lt x.2 y.2 else lt x.1 y.1.

Lemma irr_lex : irreflexive lex.
Proof. by move=>x; rewrite /lex eq_refl ltxx. Qed.

Lemma trans_lex : transitive lex.
Proof.
move=> [y1 y2] [x1 x2] [z1 z2]; rewrite /lex /=.
have [->|_] := altP eqP; first by case: eqP => // _; apply: lt_trans.
by have [-> xz|_ xy /(lt_trans xy) xz] := altP eqP; rewrite lt_eqF.
Qed.

Lemma total_lex x y : [|| lex x y, x == y | lex y x].
Proof.
move: x y => [x1 x2] [y1 y2]; rewrite /lex /= -pair_eqE /=.
by have [] //= := ltgtP x1 y1; have [] := ltgtP.
Qed.

Definition prod_ordMixin := OrdMixin irr_lex trans_lex total_lex.
Canonical prod_ordType := Eval hnf in OrdType (K * T) prod_ordMixin.
End ProdOrd.

Section FinTypeOrd.
Variable T : finType.

Definition ordf : rel T :=
  fun x y => index x (enum T) < index y (enum T). 

Lemma irr_ordf : irreflexive ordf.
Proof. by move=> x; rewrite /ordf ltxx. Qed.

Lemma trans_ordf : transitive ordf.
Proof. by move=> x y z; rewrite /ordf; apply: ltn_trans. Qed.

Lemma total_ordf x y : [|| ordf x y, x == y | ordf y x].
Proof.
rewrite /ordf; have [] := ltgtP; rewrite (orbT,orbF) //= => eq_xy.
have [xT yT]: x \in enum T /\ y \in enum T by rewrite !mem_enum.
by rewrite -(nth_index x xT) -(nth_index x yT) eq_xy eq_refl.
Qed.

Definition fin_ordMixin := OrdMixin irr_ordf trans_ordf total_ordf.
End FinTypeOrd.

Notation "[ 'fin_ordMixin' 'of' T ]" :=
  (fin_ordMixin _ : T.mixin_of [eqType of T]) (at level 0).

Definition ordinal_ordMixin n := [fin_ordMixin of 'I_n].
Canonical ordinal_ordType n := OrdType 'I_n (ordinal_ordMixin n).

Hint Resolve lexx ltxx ltW lt_irreflexive.
Hint Resolve le_total le_trans le_anti lt_trans.

End Theory.
End Order.

Export Order.T.Exports Order.Syntax.
