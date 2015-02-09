(* Authors: Beta Ziliani and Cyril Cohen *)
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import fintype ordtype bigop.

(****************************************************************************)
(* This file provides a representation of finitely supported maps where     *)
(* the keys K lie in an ordType and the values V in an arbitrary type.      *)
(*                                                                          *)
(*   {fmap K -> V} == finitely supported maps from K to V.                  *)
(*        {fset K} := {fmap K -> unit}                                      *)
(*                 == finite sets of elements of K                          *)
(*                                                                          *)
(*          keys f == list of keys of f                                     *)
(*          domf f == finite set ({fset K}) of keys of f                    *)
(*         k \in f == k is a key of f                                       *)
(*          [fmap] == the empty finite map                                  *)
(*        [fset k] == the singleton finite set {k}                          *)
(*      f.[k <- v] == f extended with the mapping k -> v                    *)
(*          s.[+k] == the set s extended with k                             *)
(*          f.[~k] == f where the key k has been removed                    *)
(*      f.[k | v0] == returns v      if k maps to v, otherwise v0           *)
(*           f.[k] == returns Some v if k maps to v, otherwise None         *)
(*          f ++ g == concatenation of f and g,                             *)
(*                    the keys of g override those of f                     *)
(*         f :~: g == f and g have disjoint sets of keys                    *)
(*                                                                          *)
(*      [fmap i in ks => E] == builds a finite map using E with keys ks     *)
(* [fmap g i v | i, v <- f] == builds a finite map from f by composing with *)
(*                             a function g : K -> V -> V'                  *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.Theory.
Local Open Scope order_scope.

Reserved Notation "{fmap T }" (at level 0, format "{fmap  T }").
Reserved Notation "{fset K }" (at level 0, format "{fset  K }").
Reserved Notation "x .[ k <- v ]"
  (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").
Reserved Notation "x .[~ k ]" (at level 2, k at level 200, format "x .[~  k ]").
Reserved Notation "x .[+ k ]" (at level 2, k at level 200, format "x .[+  k ]").
Reserved Notation "x .[ k | v ]"
  (at level 2, k at level 200, v at level 200, format "x .[ k  |  v ]").
Reserved Infix ":~:" (at level 52).
Reserved Notation "[ 'fset' k ]" (at level 0, k at level 99, format "[ 'fset'  k ]").

Reserved Notation "[ 'fmap' E | k , v <- s ]"
  (at level 0, E at level 99, k ident, v ident,
   format "[ '[hv' 'fmap'  E '/ '  |  k ,  v  <-  s ] ']'").
Reserved Notation "[ 'fmap' E | v <- s ]"
  (at level 0, E at level 99, v ident,
   format "[ '[hv' 'fmap'  E '/ '  |  v  <-  s ] ']'").

Reserved Notation "[ 'fmap' x 'in' A => E ]"
   (at level 0, E, x at level 99,
   format "[ '[hv' 'fmap'  x  'in'  A  =>  '/' E ] ']'").

Section extra.

Lemma mem_remF (T : eqType) (s : seq T) x : uniq s -> x \in rem x s = false.
Proof. by move=> us; rewrite mem_rem_uniq // inE eqxx. Qed.

End extra.

Section Def.
Variables (K : ordType) (V : Type).

Definition key (x : K * V) := x.1.
Definition value (x : K * V) := x.2.
Notation keys := (map key).
Notation values := (map value).

Structure finMap : Type := FinMap {
  seq_of :> seq (K * V);
  _ : sorted Order.lt (keys seq_of)}.

Definition finmap_of (_ : phant (K -> V)) := finMap.
End Def.

Prenex Implicits key value.

Notation keys := (map key).
Notation values := (map value).
Notation "{fmap T }" := (@finmap_of _ _ (Phant T)) : type_scope.
Notation "{fset K }" := {fmap K -> unit} : type_scope.

Definition pred_of_finmap (K : ordType) (V : Type)
  (f : {fmap K -> V}) : pred K := mem (keys f).
Canonical finMapPredType (K : ordType) (V : Type) :=
  Eval hnf in mkPredType (@pred_of_finmap K V).

Section Basics.
Variables (K : ordType) (V : Type).

Lemma keys_sorted (f : {fmap K -> V}) : sorted <%ord (keys f).
Proof. by case: f. Qed.

End Basics.
Hint Resolve keys_sorted.

Section Ops.

Variables (K : ordType).

Lemma nil_sorted V : sorted <%ord (map (@key K V) [::]). Proof. by []. Qed.
Definition nilf V := FinMap (@nil_sorted V).

Definition fmap_subproof V (ks : seq K) (f : K -> V) :
  sorted <%ord (keys [seq (k, f k) | k <- sort <=%ord (undup ks)]).
Proof.
rewrite -map_comp (@eq_map _ _ _ id) // map_id.
by rewrite sort_lt_sorted undup_uniq.
Qed.
Definition fmap V ks f : {fmap K -> V} := FinMap (fmap_subproof ks f).

Definition get V (v0 : V) (f : {fmap K -> V}) (k0 : K) :=
  (nth (k0,v0) f (find (pred1 k0) (keys f))).2.

Definition setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) : {fmap K -> V} :=
  fmap (k0 :: keys f) [eta get v0 f with k0 |-> v0].

Lemma filtermap_subproof V P (f : {fmap K -> V}) :
   sorted <%ord (keys [seq x <- f | P x]).
Proof.
apply: subseq_sorted (keys_sorted f); first exact: lt_trans.
apply/subseqP; exists [seq P x | x <- f]; first by rewrite !size_map.
by rewrite filter_mask map_mask.
Qed.

Definition filtermap V P (f : {fmap K -> V}) : {fmap K -> V} :=
  FinMap (filtermap_subproof P f).

Definition remf V k := (filtermap (preim (@key K V) (predC1 k))).

Lemma mapf_subproof V V' (f : {fmap K -> V}) (g : K -> V -> V') :
  sorted Order.lt (map key [seq (kv.1, g kv.1 kv.2) | kv <- f]).
Proof. by rewrite -map_comp (@eq_map _ _ _ key) //= keys_sorted. Qed.

Definition mapf V V' (f : {fmap K -> V}) (g : K -> V -> V') : {fmap K -> V'} :=
  FinMap (mapf_subproof f g).

Definition fnd V (f : {fmap K -> V}) := get None (mapf f (fun _ => some)).

End Ops.

Prenex Implicits fmap get setf remf filtermap fnd.
Arguments nilf {K V}.
Arguments get : simpl never.
Arguments setf : simpl never.
Arguments remf : simpl never.
Arguments fnd : simpl never.

Delimit Scope fmap_scope with fmap.
Local Open Scope fmap_scope.

Notation "x .[ k <- v ]" := (setf x k v) : fmap_scope.
Notation "x .[~ k ]" := (remf k x) : fmap_scope.
Notation "x .[ k ]" := (fnd x k) : fmap_scope.
Notation "x .[ k | v ]" := (get v x k) : fmap_scope.
Notation "[ 'fmap' k 'in' keys => E ]" := (fmap keys (fun k => E)) : fmap_scope.
Notation "[ 'fmap' E | k , v <- s ]" := (mapf s (fun k v => E)) : fmap_scope.
Notation "[ 'fmap' E | v <- s ]" := (mapf s (fun _ v => E)) : fmap_scope.

Notation fnd_if := (fun_if (fun x => fnd x _)).
Notation get_if := (fun_if (fun x => get _ x _)).

Canonical  finMapSubType K V := [subType for (@seq_of K V)].
Definition finMapEqMixin (K : ordType) (V : eqType) :=
  [eqMixin of {fmap K -> V} by <:].
Canonical  finMapEqType  (K : ordType) (V : eqType) :=
  EqType ({fmap K -> V}) (finMapEqMixin K V).

Section Theory.

Variables (K : ordType).

Lemma keys_fmap V (ks : seq K) (f : K -> V) :
  keys [fmap k in ks => f k] = sort <=%ord (undup ks).
Proof. by rewrite /= -map_comp (@eq_map _ _ _ id) ?map_id. Qed.

Lemma mem_fmap V (ks : seq K) (f : K -> V) : fmap ks f =i ks.
Proof. by move=> k'; rewrite inE keys_fmap mem_sort mem_undup. Qed.

Lemma keys_set V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  keys (f.[k0 <- v0]) = sort <=%ord (undup (k0 :: keys f)).
Proof. by rewrite /setf /= -map_comp (@eq_map _ _ _ id) // map_id. Qed.

Lemma mem_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) k :
  k \in f.[k0 <- v0] = (k == k0) || (k \in f).
Proof. by rewrite mem_fmap in_cons. Qed.

Lemma get_head_filter V (v0 : V) (f : {fmap K -> V}) (k : K) :
  f.[k | v0] = head v0 [seq kv.2 | kv <- f & kv.1 \in pred1 k].
Proof.
rewrite /get; case: f; elim=> [//|[k' v'] s //= IHs].
by rewrite inE; have [->|nk'k /path_sorted] //= := altP eqP.
Qed.

Lemma fmapK V (v : V) (ks : seq K) (f : K -> V) (k : K) :
   [fmap k in ks => f k].[k | v] = if k \in ks then f k else v.
Proof.
rewrite /get /=; set ks' := sort _ _.
have -> : (k \in ks) = (k \in ks') by rewrite mem_sort mem_undup.
elim: {ks} ks' => // k' ks IHks; rewrite in_cons.
have [->|] /= := altP eqP; first by rewrite eqxx.
by rewrite eq_sym => neq_kk' /=; rewrite (negPf neq_kk') /= IHks.
Qed.

Lemma mapf_fmap V V' (ks : seq K) (f : K -> V) (g : K -> V -> V') :
   [fmap g k v | k, v <- [fmap k in ks => f k]] = [fmap k in ks => g k (f k)].
Proof.
by apply: val_inj; elim: ks => //= ???; rewrite -!map_comp; case: (_ \in _).
Qed.

Lemma fnd_fmap V (ks : seq K) (f : K -> V) (k : K) :
  [fmap k in ks => f k].[k] = if k \in ks then Some (f k) else None.
Proof. by rewrite /fnd mapf_fmap fmapK. Qed.

Lemma size_keys V (f : {fmap K -> V}) : size (keys f) = size f.
Proof. by rewrite size_map. Qed.

Lemma keys_uniq V (f : {fmap K -> V}) : uniq (keys f).
Proof. by have := keys_sorted f; rewrite lt_sorted_uniq_le => /andP []. Qed.

Lemma keys_sortedW V (f : {fmap K -> V}) : sorted <=%ord (keys f).
Proof. by have := keys_sorted f; rewrite lt_sorted_uniq_le => /andP []. Qed.

Hint Resolve keys_uniq.
Hint Resolve keys_sortedW.

Lemma sort_keys V (f : {fmap K -> V}) : sort <=%ord (keys f) = keys f.
Proof. by rewrite sort_le_id. Qed.

Lemma undup_keys V (f : {fmap K -> V}) : undup (keys f) = keys f.
Proof. by rewrite undup_id. Qed.

Lemma keys_mapf V V' (f : {fmap K -> V}) (g : K -> V -> V') :
  keys [fmap g k v | k, v <- f] = keys f.
Proof. by rewrite -map_comp. Qed.

Lemma mem_mapf V V' (f : {fmap K -> V}) (g : K -> V -> V') :
  [fmap g k v | k, v <- f] =i f.
Proof. by move=> k; rewrite inE keys_mapf. Qed.

Lemma get_default V (v : V) (f : {fmap K -> V}) (k : K) :
  k \notin f -> f.[k | v] = v.
Proof.
move=> knf; rewrite /get nth_default //.
rewrite (@leq_trans (size (keys f))) //; first by rewrite size_map.
by rewrite leqNgt -has_find has_pred1.
Qed.

Lemma fnd_default V (f : {fmap K -> V}) (k : K) :
  k \notin f -> fnd f k = None.
Proof. by move=> kf; rewrite /fnd get_default ?inE ?keys_mapf. Qed.

Lemma get_mapf V V' (v : V) (f : {fmap K -> V}) (g : K -> V -> V') (k : K) :
  [fmap g k v | k, v <- f].[k | g k v] = g k (f.[k | v]).
Proof.
have [k_key|k_Nkey]:= boolP (k \in f); last first.
  by rewrite !get_default // inE -map_comp.
rewrite /get /= -map_comp (@eq_map _ _ _ key) //.
have find_k : (find (pred1 k) (keys f) < size f)%N.
  by rewrite -size_keys -has_find has_pred1.
rewrite (nth_map (k, v)) //=; congr g; rewrite -(nth_map _ k) //.
by apply/eqP; apply: (@nth_find _ _ (pred1 k)); rewrite has_pred1.
Qed.

Lemma ex_value V (f : {fmap K -> V}) : keys f != [::] -> V.
Proof. by case: f => [[|[_ v] Hs] //]; exact: v. Qed.

Lemma key_ex_value V (f : {fmap K -> V}) (k : K) : k \in f -> V.
Proof.
by rewrite inE => kf; apply: (@ex_value V f); apply: contraTneq kf => ->.
Qed.

Lemma eq_in_fmap V (ks : seq K) (f f' : K -> V) :
  {in ks, f =1 f'} <-> fmap ks f = fmap ks f'.
Proof.
split=> [eq_ff'| eq_ff' k kks].
  apply: val_inj => /=; apply/eq_in_map => k.
  by rewrite mem_sort mem_undup => /eq_ff' ->.
have := congr1 (fun u : finMap _ _ => get (f k) u k) eq_ff'.
by rewrite !fmapK kks.
Qed.

Lemma eq_fmap V (ks : seq K) (f f' : K -> V) :
  f =1 f' -> fmap ks f = fmap ks f'.
Proof. by move=> eq_ff'; apply/eq_in_fmap => k; rewrite eq_ff'. Qed.

Lemma finmap_nil V (f : {fmap K -> V}) : keys f = [::] -> f = nilf.
Proof. by case: f => [[] //= ?] _; apply: val_inj. Qed.

Lemma getK V (f : {fmap K -> V}) (v0 : V) : fmap (keys f) (get v0 f) = f.
Proof.
rewrite (eq_fmap _ (get_head_filter _ _)); symmetry; apply: val_inj => /=.
case: f; elim=> [|[k v] s IHs] Hs //=; move: Hs IHs.
rewrite lt_sorted_uniq_le /= => /andP[/andP [ks us] pks].
have sks:= path_sorted pks; move=> {1}->; last by rewrite lt_sorted_uniq_le us.
rewrite (negPf ks) !sort_le_id ?undup_id //= !inE eqxx /=.
congr (_ :: _); apply/eq_in_map => k' k's /=.
by rewrite inE /= [_ == _]negbTE //; apply: contraNneq ks => ->.
Qed.

Lemma getEfnd V (v0 : V) (f : {fmap K -> V}) (k : K) :
      f.[k | v0] = odflt v0 f.[k].
Proof. by rewrite -[f](getK _ v0) fmapK fnd_fmap; case: (_ \in _). Qed.

Lemma eq_get V (v v' : V) (f : {fmap K -> V}) (k : K) :
  k \in f -> f.[k | v] = f.[k | v'].
Proof. by move=> kf; rewrite -[f](getK _ (key_ex_value kf)) !fmapK kf. Qed.

Lemma setfK V (v0 : V) (f : {fmap K -> V}) (k : K) (v : V) :
  f.[k <- v].[k | v0] = v.
Proof. by rewrite fmapK //= ?eqxx ?mem_head. Qed.

Lemma setfNK V (v0 : V) (f : {fmap K -> V}) (k k' : K) (v : V) :
   k' != k -> f.[k <- v].[k' | v0] = f.[k' | v0].
Proof.
rewrite fmapK //= in_cons => /negPf -> /=.
by case: ifP => // k'f; [apply:eq_get|rewrite get_default // k'f].
Qed.

Lemma get_set V (v0 : V) (f : {fmap K -> V}) (k k' : K) (v : V) :
   f.[k <- v].[k' | v0] = (if k' == k then v else f.[k' | v0]).
Proof. by have [->|/(setfNK _ _ _)->//] := altP eqP; rewrite setfK. Qed.

Lemma mapf_set V V' (f : {fmap K -> V}) (g : K -> V -> V') (k : K) (v : V) :
  [fmap g k v | k, v <- f.[k <- v]] = [fmap g k v | k, v <- f].[k <- g k v].
Proof.
rewrite mapf_fmap /setf keys_mapf. apply/eq_in_fmap => k' /=.
rewrite in_cons; have [-> //|/= neq_k'k k'_f] := altP eqP.
by rewrite -get_mapf; apply: eq_get; rewrite mem_mapf.
Qed.

Lemma getP V (v : V) (f g : {fmap K -> V}) :
  keys f = keys g -> {in f, get v f =1 get v g} -> f = g.
Proof.
move=> kfg eq_fg; rewrite -[g](getK _ v) -[f](getK _ v) kfg.
by apply/eq_in_fmap => k kg; rewrite eq_fg ?inE ?kfg //.
Qed.

Lemma fnd_set V (f : {fmap K -> V}) (k k' : K) (v : V) :
   f.[k <- v].[k'] = (if k' == k then Some v else f.[k']).
Proof. by rewrite /fnd mapf_set get_set. Qed.

Lemma fndSome V (f : {fmap K -> V}) (k : K) : f.[k] = (k \in f) :> bool.
Proof.
have [kf|/fnd_default -> //] := boolP (_ \in _).
by rewrite -[f](getK _ (key_ex_value kf)) fnd_fmap kf.
Qed.

Lemma not_fnd V (f : {fmap K -> V}) (k : K) : k \notin f -> fnd f k = None.
Proof. by rewrite -fndSome; case: fnd. Qed.

Lemma fndE V (v : V) (f : {fmap K -> V}) (k : K) :
  f.[k] = if k \in f then Some f.[k | v] else None.
Proof.
have [kf|nkf] := boolP (_ \in _); last by rewrite fnd_default.
by move: kf; rewrite -fndSome getEfnd; case: fnd.
Qed.

CoInductive pre_finmap_spec V (f : {fmap K -> V}) :
  {fmap K -> V} -> seq K -> pred K -> bool -> Type :=
| PreFinmapNil of f = nilf : pre_finmap_spec f nilf [::] (mem [::]) true
| PreFinmapNNil (v : V) (k : K) of k \in f :
  pre_finmap_spec f f (keys f) (mem f) false.

Lemma pre_finmapP V (f : {fmap K -> V}) :
  pre_finmap_spec f f (keys f) (mem f) (keys f == [::]).
Proof.
have [/finmap_nil->|kf] := altP (keys f =P [::]); first by constructor.
have v := ex_value kf; case ekf: keys kf => [//|k ks] _.
by rewrite -ekf; apply: (@PreFinmapNNil _ _ v k); rewrite inE ekf mem_head.
Qed.

Lemma fnd_mapf V V' (f : {fmap K -> V}) (g : K -> V -> V') (k : K) :
  [fmap g k v | k, v <- f].[k] = omap (g k) f.[k].
Proof.
have [_ //|v] := pre_finmapP f.
by rewrite (fndE (g k v)) (fndE v) mem_mapf get_mapf; case: (_ \in _).
Qed.

Lemma finmap_fndNone V (f : {fmap K -> V}) : fnd f =1 (fun _=> None) -> f = nilf.
Proof.
have [[k kf _]|] := altP (@hasP _ predT (keys f)).
  by move=> /(_ k) /(congr1 isSome); rewrite fndSome kf.
by rewrite has_filter filter_predT negbK => /eqP /finmap_nil->.
Qed.

Lemma fndP V (f g : {fmap K -> V}) : fnd f =1 fnd g -> f = g.
Proof.
have [_|v _ _ efg] := pre_finmapP g; first by apply: finmap_fndNone => k.
apply: (@getP _ v) => // [|k kf]; last by rewrite !getEfnd efg.
by apply: eq_sorted_lt; rewrite ?keys_sorted // => k; rewrite -!fndSome efg.
Qed.

Lemma congr_fmap V (ks ks' : seq K) (f f' : K -> V) :
  ks =i ks' -> f =1 f' -> fmap ks f = fmap ks' f'.
Proof. by move=> eks ef; apply: fndP => k; rewrite !fnd_fmap eks ef. Qed.

Lemma keys_rem V (f : {fmap K -> V}) (k : K) : keys f.[~ k] = rem k (keys f).
Proof. by rewrite -filter_map -rem_filter. Qed.

Lemma mem_remf V (f : {fmap K -> V}) (k k' : K) :
   k \in f.[~ k'] = (k != k') && (k \in f).
Proof. by rewrite inE keys_rem mem_rem_uniq. Qed.

Lemma mem_remfF V (f : {fmap K -> V}) (k : K) : k \in f.[~ k] = false.
Proof. by rewrite inE keys_rem mem_remF. Qed.

Lemma finmapE V (v0 : V) (f : {fmap K -> V}) :
  f = [seq (k, get v0 f k) | k <- keys f] :> seq _.
Proof. by rewrite -{1}[f](getK _ v0) /= undup_keys sort_keys. Qed.

Lemma filtermapE V (v0 : V) P (f : {fmap K -> V}) :
  filtermap P f = fmap [seq k <- keys f | P (k, get v0 f k)] (get v0 f).
Proof.
apply: val_inj => /=; rewrite undup_id ?filter_uniq //.
rewrite sort_le_id ?(sorted_filter (@le_trans _)) //.
by rewrite {1}(finmapE v0) filter_map.
Qed.

Lemma remfE V (v0 : V) (f : {fmap K -> V}) (k : K) :
  f.[~k] = fmap (rem k (keys f)) (get v0 f).
Proof. by rewrite /remf (filtermapE v0) /= rem_filter. Qed.

Lemma get_rem V (v0 : V) (f : {fmap K -> V}) (k k' : K) :
  (f.[~ k]).[k' | v0] = if k' == k then v0 else f.[k' | v0].
 Proof.
rewrite (remfE v0) fmapK mem_rem_uniq // inE /=; case: eqP => //= _.
by have [//|kf] := boolP (_ \in _); rewrite get_default.
Qed.

Lemma fnd_rem V (f : {fmap K -> V}) (k k' : K) :
  f.[~ k].[k'] = if k' == k then None else f.[k'].
Proof.
have [_|v _ _] := pre_finmapP f; first by rewrite !fnd_default // if_same.
by rewrite !(fndE v) get_rem mem_remf; case: eqP; case: (_ \in _).
Qed.

Lemma setf_get V (v0 : V) (f : {fmap K -> V}) (k : K) :
 f.[k <- f.[k | v0]] = if k \in f then f else f.[k <- v0].
Proof.
case: ifP => kf; last by rewrite get_default // kf.
apply: (@getP _ v0); first by rewrite keys_set /= kf undup_keys sort_keys.
by move=> k' _; have [->|nk''] := eqVneq k' k;  rewrite (setfK,setfNK).
Qed.

Lemma setf_rem V (f : {fmap K -> V}) (k : K) (v : V) : k \in f ->
  f.[~ k].[k <- v] = f.[k <- v].
Proof.
move=> kf; apply: congr_fmap => k' /=; last by rewrite get_rem; case: eqP.
by rewrite keys_rem !in_cons mem_rem_uniq // inE /=; case: eqP.
Qed.

Lemma setf_mapf V V' (f : {fmap K -> V}) (g : K -> V -> V') (k : K) (v : V) :
  [fmap g k v | k, v <- f].[k <- g k v] = [fmap g k v | k, v <- f.[k <- v]].
Proof.
by apply: fndP => k'; rewrite !(fnd_set, fnd_mapf); case: eqP => // ->.
Qed.

Lemma finMapP V (f : {fmap K -> V}) (k : K) : k \in f ->
  {gv : {fmap K -> V} * V | k \notin gv.1 & f = gv.1.[k <- gv.2]}.
Proof.
move=> kf; have v0 := key_ex_value kf.
exists (remf k f, get v0 f k) => /=; first by rewrite mem_remfF.
by rewrite setf_rem // setf_get kf.
Qed.

CoInductive mem_finmap_spec V (k : K) (f : {fmap K -> V}) :
  {fmap K -> V} -> option V -> bool -> bool -> Type :=
| MemFinmapNil of k \notin f :
    mem_finmap_spec k f f None (keys f == [::]) false
| MemFinmapNNil (v : V) g of f = g.[k <- v] & k \notin g :
    mem_finmap_spec k f (setf g k v) (Some v) false true.

Lemma mem_finmapP V k (f : {fmap K -> V}) :
  mem_finmap_spec k f f f.[k] (keys f == [::]) (k \in f).
Proof.
have [kf|kf] := boolP (_ \in _); last first.
  by rewrite fnd_default //; constructor.
have [[g v] /= kg {-4}->] := finMapP kf.
by rewrite inE in kf *; rewrite fnd_set eqxx; case: keys kf => //; constructor.
Qed.

CoInductive get_finmap_spec V (v0 : V) (k : K) (f : {fmap K -> V}) :
  {fmap K -> V} -> bool -> bool -> option V -> V -> Type :=
| GetFinmapNil of k \notin f :
    get_finmap_spec v0 k f f (keys f == [::]) false None v0
| GetFinmapNNil (v : V) g of f = g.[k <- v] :
    get_finmap_spec v0 k f (g.[k <- v]) false true (Some v) v.

Lemma get_finmapP V v0 k (f : {fmap K -> V}) :
  get_finmap_spec v0 k f f (keys f == [::]) (k \in f)
                           (f.[k]) (f.[k | v0]).
Proof.
have [kf|v g _] := mem_finmapP; first by rewrite get_default //; constructor.
by rewrite setfK; constructor.
Qed.

Lemma setfC V (f : {fmap K -> V}) k1 k2 v1 v2 :
   f.[k1 <- v1].[k2 <- v2] =
   if k2 == k1 then f.[k2 <- v2] else f.[k2 <- v2].[k1 <- v1].
Proof.
apply: fndP => k /=; have [->|Nk12] := altP eqP.
  by rewrite !fnd_set; case: eqP.
by rewrite !fnd_set; have [->|//] := altP eqP; rewrite (negPf Nk12).
Qed.

Lemma remf_id V (f : {fmap K -> V}) k : k \notin f -> f.[~ k] = f.
Proof.
move=> kf; apply: fndP => k'; rewrite fnd_rem.
by case: eqP => // ->; rewrite not_fnd.
Qed.

Lemma remf_set V (f : {fmap K -> V}) (k k' : K) (v : V) :
  f.[k' <- v].[~ k] = if k == k' then f.[~ k] else f.[~ k].[k' <- v].
Proof.
apply: fndP => k'' /=; have [->|Nk12] := altP eqP.
  by rewrite !fnd_rem fnd_set; case: eqP.
by rewrite !(fnd_rem, fnd_set); have [->|//] := altP eqP; rewrite (negPf Nk12).
Qed.

Lemma is_fnd V (f : {fmap K -> V}) k : k \in f -> exists v, f.[k] = Some v.
Proof. by rewrite -fndSome; case: fnd => v //; exists v. Qed.

Lemma setf_inj V (f f' : {fmap K -> V}) k v :
  k \notin f -> k \notin f' -> f.[k <- v] = f'.[k <- v]-> f = f'.
Proof.
move=> kf kf' eq_fkv; apply: fndP => k'; have := congr1 (fnd^~ k') eq_fkv.
by rewrite !fnd_set; case: eqP => // ->; rewrite !fnd_default.
Qed.

CoInductive finmap_spec V (f : {fmap K -> V}) :
  {fmap K -> V} -> seq K -> bool -> Type :=
| FinmapNil of f = nilf : finmap_spec f nilf [::] true
| FinmapNNil (v : V) (k : K) g of f = g.[k <- v] & k \notin g :
    finmap_spec f g.[k <- v] (k :: keys g) false.

Lemma finmapP V (f : {fmap K -> V}) : finmap_spec f f (keys f) (keys f == [::]).
Proof.
have [/finmap_nil->|kf] := altP (keys f =P [::]); first by constructor.
case ekf: keys kf => [//|k ks] _.
case: (mem_finmapP k f); first by rewrite inE ekf mem_head.
move=> v g eq_f kNg; rewrite -{1}eq_f.
suff -> : ks = keys g by constructor.
have -> : g = f.[~ k] by rewrite eq_f remf_set eqxx remf_id.
by rewrite keys_rem ekf /= eqxx.
Qed.

End Theory.
Hint Resolve keys_uniq.
Hint Resolve keys_sortedW.

Section Cat.
Variables (K : ordType).

Definition catf V (f g : {fmap K -> V}) :=
  if (keys g != [::]) =P true is ReflectT P
  then let v := ex_value P in
    fmap (keys f ++ keys g)
         (fun k => if k \in g then g.[k | v] else f.[k | v])
  else f.

Definition disjf V (f g : {fmap K -> V}) : bool :=
  all (predC (mem (keys g))) (keys f).

Lemma disjfP {V} {f g : {fmap K -> V}} :
  reflect {in f & g, forall k k', k != k'} (disjf f g).
Proof.
apply: (iffP idP) => [dfg k k' kf k'g|Hfg].
  by have /allP /(_ _ kf) := dfg; apply: contraNneq => ->.
by apply/allP=> k kf; have /contraTN := Hfg _ k kf; apply.
Qed.

Lemma disjfC  V (f g : {fmap K -> V}) : disjf f g = disjf g f.
Proof. by apply/disjfP/disjfP => Hfg ????; rewrite eq_sym; apply: Hfg. Qed.

Lemma disjfPr {V} {f g : {fmap K -> V}} :
  reflect {in f, forall k, k \in g = false} (disjf f g).
Proof.
apply: (iffP disjfP) => [dfg k kf|dfg k k' kf kg].
  by apply: contraTF isT => /(dfg _ _ kf); rewrite eqxx.
by apply: contraTneq kg => <-; rewrite dfg.
Qed.

Lemma disjfPl {V} {f g : {fmap K -> V}} :
  reflect {in g, forall k, k \in f = false} (disjf f g).
Proof. by rewrite disjfC; apply: disjfPr. Qed.

Lemma disjf0 V (f : {fmap K -> V}) : disjf f nilf.
Proof. by apply/disjfP => k k'. Qed.

Lemma disj0f V (f : {fmap K -> V}) : disjf nilf f.
Proof. by apply/disjfP => k k'. Qed.

Lemma catf0 V (f : {fmap K -> V}) : catf f nilf = f.
Proof. by rewrite /catf; case: eqP. Qed.

Lemma catfE V v0 (f g : {fmap K -> V}) : catf f g =
  fmap (keys f ++ keys g)
       (fun k => if k \in g then g.[k | v0] else f.[k | v0]).
Proof.
rewrite /catf; case: eqP => /= [P|]; last first.
  by have [|//] := finmapP; rewrite cats0 /= getK.
apply/eq_in_fmap => /= k; rewrite mem_cat orbC => kfg.
by case: (boolP (_ \in g)) kfg => //= ? ?; apply: eq_get.
Qed.

Lemma get_cat V v0 (f g : {fmap K -> V}) k :
  get v0 (catf f g) k = if k \in g then g.[k | v0] else f.[k | v0].
Proof.
rewrite (catfE v0) !fmapK mem_cat orbC.
by case: mem_finmapP => //; case: get_finmapP.
Qed.

Lemma keys_cat V (f g : {fmap K -> V}) :
  keys (catf f g) = sort <=%ord (undup (keys f ++ keys g)).
Proof.
have [_//=|v _ _] := pre_finmapP g; last by rewrite (catfE v) keys_fmap.
by rewrite catf0 cats0 undup_keys sort_keys.
Qed.

Lemma mem_catf V (f g : {fmap K -> V}) k :
 k \in catf f g = (k \in f) || (k \in g).
Proof. by rewrite inE keys_cat mem_sort mem_undup mem_cat. Qed.

Lemma fnd_cat V (f g : {fmap K -> V}) k :
  fnd (catf f g) k = if k \in g then g.[k] else f.[k].
Proof.
have [_//=|v _ _] := pre_finmapP g; first by rewrite catf0.
by rewrite !(fndE v) /= get_cat mem_catf orbC; do !case: (_ \in _).
Qed.

Lemma cat0f V (f : {fmap K -> V}) : catf nilf f = f.
Proof.
apply: fndP => k; rewrite fnd_cat.
by case: mem_finmapP => // v {f} f _; rewrite fnd_set eqxx.
Qed.

Lemma catf_setl V f g k (v : V) :
  catf f.[k <- v] g = if k \in g then catf f g else (catf f g).[k <- v].
Proof.
apply: fndP => k'0; rewrite !(fnd_cat,fnd_if,fnd_set).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma catf_setr V f g k (v : V) : catf f g.[k <- v] = (catf f g).[k <- v].
Proof.
apply: fndP => k'; rewrite !(fnd_cat, fnd_set) mem_setf.
by case: (_ == _); case: (_ \in _).
Qed.

Lemma catf_reml V k (f g : {fmap K -> V}) :
  catf f.[~ k] g = if k \in g then catf f g else (catf f g).[~ k].
Proof.
apply: fndP => k'; rewrite !(fnd_if, fnd_cat, fnd_rem).
by have [->|?] := altP eqP; do !case: (_ \in _).
Qed.

Lemma disjf_setr V (f g : {fmap K -> V}) k v :
  disjf f g.[k <- v] = (k \notin f) && (disjf f g).
Proof.
apply/idP/idP => [dfg|/andP [kf dfg]].
  rewrite (disjfPl dfg) ?mem_setf ?eqxx //=; apply/disjfPl=> k' k'g.
  by rewrite (disjfPl dfg) // mem_setf k'g orbT.
apply/disjfPl => k'; rewrite mem_setf.
by have [->|_ /disjfPl->] := altP eqP; first by rewrite (negPf kf).
Qed.

End Cat.

Section DisjointUnion.
Variables (K : ordType) (V : Type).
Notation finmap := ({fmap K -> V}).
Notation nil := (@nil K V).

Lemma disjf_remr k (s1 s2 : finmap) :
  k \notin s1 -> disjf s1 s2.[~k] = disjf s1 s2.
Proof.
move=> kNs1; apply/disjfPr/disjfPr => Hs2 x xs1; last first.
  by rewrite mem_remf Hs2 // andbF.
have := Hs2 x xs1; rewrite mem_remf; apply: contraFF => ->; rewrite andbT.
by apply: contraNneq kNs1 => <-.
Qed.

Lemma disjf_reml k (s1 s2 : finmap) :
  k \notin s2 -> disjf s1.[~k] s2 = disjf s1 s2.
Proof. by move=> kNs2; rewrite disjfC disjf_remr // disjfC. Qed.

Lemma disjf_catl (s s1 s2 : finmap) :
  disjf s (catf s1 s2) = disjf s s1 && disjf s s2.
Proof.
apply/disjfPr/idP => [Ncat|/andP[/disjfPr Ns1 /disjfPr Ns2]]; last first.
  by move=> k ks /=; rewrite mem_catf Ns1 ?Ns2.
apply/andP; split; apply/disjfPr=> k ks; have := Ncat k ks;
by rewrite mem_catf; apply: contraFF => ->; rewrite ?orbT.
Qed.

Lemma catfC (s1 s2 : finmap) : disjf s1 s2 -> catf s1 s2 = catf s2 s1.
Proof.
move=> ds1s2; apply/fndP => x; rewrite !fnd_cat.
case: ifPn=> [xs2|xNs2]; first by rewrite (disjfPl ds1s2).
by case: ifPn=> [//|xNs1]; rewrite !fnd_default.
Qed.

Lemma catfA (s1 s2 s3 : finmap) :
        disjf s2 s3 -> catf s1 (catf s2 s3) = catf (catf s1 s2) s3.
Proof.
move=> ds2s3; apply: fndP => x; rewrite !fnd_cat !mem_catf.
have [xs3|/= xNs3] := boolP (_ \in s3); last by rewrite orbF.
by rewrite (disjfPl ds2s3).
Qed.

Lemma catfAC (s1 s2 s3 : finmap) :
  [&& disjf s1 s2, disjf s2 s3 & disjf s1 s3] ->
    catf (catf s1 s2) s3 = catf (catf s1 s3) s2.
Proof. by case/and3P=>???; rewrite -!catfA ?(@catfC s2) // disjfC. Qed.

Lemma catfCA (s1 s2 s3 : finmap) :
  [&& disjf s1 s2, disjf s2 s3 & disjf s1 s3] ->
    catf s1 (catf s2 s3) = catf s2 (catf s1 s3).
Proof. by case/and3P=>???; rewrite !catfA ?(@catfC s2) // disjfC. Qed.

Lemma catfsK (s s1 s2 : finmap) :
  disjf s1 s && disjf s2 s -> catf s1 s = catf s2 s -> s1 = s2.
Proof.
move=> /andP[ds1s ds2s] eq_s12s; apply: fndP => k.
move: eq_s12s => /(congr1 (fnd^~ k)); rewrite !fnd_cat.
by case: ifP => // ks _; rewrite !fnd_default ?(disjfPl ds1s) ?(disjfPl ds2s).
Qed.

Lemma catfKs (s s1 s2 : finmap) :
  disjf s s1 && disjf s s2 -> catf s s1 = catf s s2 -> s1 = s2.
Proof.
move=> /andP [??]; rewrite !(@catfC s) //.
by move => /catfsK -> //; apply/andP; split; rewrite disjfC.
Qed.

End DisjointUnion.

Section EqType.
Variables (K : ordType) (V : eqType).

Definition feq (s1 s2 : {fmap K -> V}) := seq_of s1 == seq_of s2.

Lemma feqP : Equality.axiom feq.
Proof.
move=> s1 s2; rewrite /feq; apply: (iffP eqP) => [|->//].
move: s1 s2 => [s1 Hs1] [s2 Hs2] //= eq_s12.
by case: _ / eq_s12 in Hs2 *; rewrite [Hs1]bool_irrelevance.
Qed.

Canonical Structure finmap_eqMixin := EqMixin feqP.
Canonical Structure finmap_eqType := EqType {fmap K -> V} finmap_eqMixin.
End EqType.

Delimit Scope fmap_scope with fset.
Open Scope fmap_scope.

Notation "[ 'fmap' ]" := nilf : fmap_scope.
Infix "++" := catf : fmap_scope.
Infix ":~:" := disjf : fmap_scope.

Section FSet.
Variables (K : ordType).
Implicit Type s : seq K.

Definition fset s : {fset K} := fmap s (fun _=> tt).
Notation "u .[+ k ]" := (u.[k <- tt]) : fmap_scope.
Notation "[ 'fset' k ]" := (fset [::k]) : fmap_scope.

Lemma mem_fset (u : {fset K}) i : (i \in u) = (fnd u i == Some tt).
Proof.
by have [/is_fnd [] [->] //|iNu] := boolP (_ \in _); rewrite fnd_default.
Qed.

Lemma mem_fsetP (u : {fset K}) i : reflect (fnd u i = Some tt) (i \in u).
Proof. by rewrite mem_fset; apply: eqP. Qed.

Lemma fsetP (u v : {fset K}) : u =i v <-> u = v.
Proof.
split => [eq_uv|->//]; apply/fndP => i.
have := eq_uv i; have [iv iu|iNv iNu] := boolP (i \in v).
  by rewrite !(mem_fsetP _ _ _).
by rewrite !fnd_default ?iNv ?iNu.
Qed.

Lemma fset_rem s k : uniq s -> fset (rem k s) = remf k (fset s).
Proof.
by move=> s_uniq; apply/fsetP => i; rewrite ?(mem_fmap, mem_remf) mem_rem_uniq.
Qed.

Lemma catf1 u k : u ++ [fset k] = u.[+ k].
Proof.
apply/fsetP=> i.
by rewrite mem_catf mem_fmap in_cons in_nil orbF mem_setf orbC.
Qed.

Lemma add0f k : [fmap].[+ k] = [fset k]. Proof. by apply/fsetP=> i. Qed.

Lemma fset_cat s s' : fset (s ++ s') = fset s ++ fset s'.
Proof. by apply/fsetP=> i; rewrite !(mem_fmap, mem_catf) mem_cat. Qed.

Lemma fset_cons s k : fset (k :: s) = (fset s).[+ k].
Proof. by apply/fsetP => i; rewrite !(mem_fmap, mem_setf) in_cons. Qed.

Lemma fset_rcons s k : fset (rcons s k) = (fset s).[+ k].
Proof.
by apply/fsetP => i; rewrite !(mem_fmap, mem_setf) mem_rcons in_cons.
Qed.

Lemma fset_sort s r : fset (sort r s) = fset s.
Proof. by apply/fsetP => i; rewrite !(mem_fmap, mem_sort). Qed.

Lemma fset_undup s : fset (undup s) = fset s.
Proof. by apply/fsetP => i; rewrite !(mem_fmap, mem_undup). Qed.

Variable (V : Type).
Implicit Types (f g : {fmap K -> V}) (k : K) (v : V).

Definition domf f := fset (keys f).

Lemma mem_domf f k : (k \in domf f) = (k \in f).
Proof. by rewrite mem_fmap. Qed.

Lemma domf_rem f k : domf f.[~k] = (domf f).[~ k].
Proof. by rewrite /domf keys_rem fset_rem. Qed.

Lemma domf_set f k v : domf f.[k <- v] = (domf f).[+ k].
Proof. by rewrite /domf keys_set fset_sort fset_undup fset_cons. Qed.

Lemma domf_cat f g : domf (f ++ g) = domf f ++ domf g.
Proof. by rewrite /domf keys_cat fset_sort fset_undup fset_cat. Qed.

Lemma domf_disj f g : domf f :~: domf g = f :~: g.
Proof.
apply/disjfPr/disjfPl => Hfg k; apply: contraTF.
  by rewrite -mem_domf => /Hfg; rewrite mem_domf => ->.
by rewrite mem_domf => /Hfg; rewrite mem_domf => ->.
Qed.

End FSet.

Section KeysInd.
Variable (K : ordType) (V : Type).

Lemma keys_eq0P {f : {fmap K -> V}} : reflect (f = [fmap]) (keys f == [::]).
Proof. by apply: (iffP idP) => [|-> //]; case: finmapP. Qed.

Lemma fmap_ind (P : {fmap K -> V} -> Type) :
  P [fmap] ->
 (forall (f : {fmap K -> V}) k v,
    k \notin f -> P f -> P f.[k <- v]) ->
 forall f, P f.
Proof.
move=> Pnil Pset f; have := erefl (keys f).
elim: (keys f) {-2}f => [|k ks iks] {f} f.
  by move/eqP; case: (finmapP f).
case: finmapP => // v k' g eq_f kNg [eqk'k kg].
rewrite eqk'k in kNg eq_f * => {k' eqk'k}.
by apply: Pset => //; apply: iks.
Qed.

End KeysInd.
