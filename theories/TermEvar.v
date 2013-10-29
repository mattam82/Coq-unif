Require Import ssreflect.
Require Export Arith.
Require Export Compare_dec.
Require Export Relations.
Require Import ssrnat ssrfun ssrbool eqtype seq choice.

Hint Resolve t_step rt_step rt_refl: core.
Hint Unfold transp: core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section extra_nat.

Lemma ltn_gtF m n : m < n -> n < m = false.
Proof. by case: ltngtP. Qed.

End extra_nat.

Section all2.
  Context {A} (f : rel A).
  
  Fixpoint all2 (s s' : seq A) : bool :=
    match s, s' with
      | [::], [::] => true
      | a :: s, a' :: s' => f a a' && all2 s s'
      | _, _ => false
    end.

  Lemma all2E s s' : all2 s s' = all (fun x => f x.1 x.2) (zip s s') && (size s == size s').
  Proof.
    elim: s s' => [|a s IHs] [|a' s'] //=. 
    by rewrite IHs andbA.
  Qed.
End all2.

Section Termes.

Inductive sort : Set :=
  | kind : nat -> sort
  | prop : sort.

Definition sort_encode (s : sort) : nat :=
  if s is kind n then n.+1 else 0.
Definition sort_decode (n : nat) : sort :=
  if n is n.+1 then kind n else prop.
Lemma sort_codeK : cancel sort_encode sort_decode. Proof. by case. Qed.

Definition sort_eqMixin := CanEqMixin sort_codeK.
Canonical sort_eqType := EqType sort sort_eqMixin.

Inductive op : Set := App | Abs | Prod.
Definition op_encode (b : op) : nat :=
  match b with App => 0 | Abs => 1 | _ => 2 end.
Definition op_decode (n : nat) : op :=
  match n with 0 => App | 1 => Abs | _ => Prod end.
Lemma op_codeK : cancel op_encode op_decode. Proof. by case. Qed.

Definition op_eqMixin := CanEqMixin op_codeK.
Canonical op_eqType := EqType op op_eqMixin.
Definition op_choiceMixin := CanChoiceMixin op_codeK.
Canonical op_choiceType := ChoiceType op op_choiceMixin.
Definition op_countMixin := CanCountMixin op_codeK.
Canonical op_countType := CountType op op_countMixin.

Definition is_abs b := match b with Prod | Abs => true | _ => false end.

Inductive term : Set :=
  | Srt : sort -> term
  | Evar : nat -> list term -> term
  | Op : op -> term -> term -> term
  | Ref : nat -> term.

Coercion Op : op >-> Funclass.

Fixpoint depth (t : term) :=  match t with
    | Srt _ | Ref _ => 0
    | Op _ u v => (maxn (depth u) (depth v)).+1
    | Evar _ l => (foldr maxn 0 (map depth l)).+1
  end.

Fixpoint term_encode (t : term) : GenTree.tree (sort + nat) :=
  match t with
    | Srt s => GenTree.Leaf (inl s)
    | Ref n => GenTree.Leaf (inr n)
    | Op b t u => 
      GenTree.Node (op_encode b) [:: term_encode t; term_encode u]
    | Evar n l => GenTree.Node n.+3 (map term_encode l) 
  end.

Fixpoint term_decode (t : GenTree.tree (sort + nat)) : term :=
  match t with
    | GenTree.Leaf (inl s) => Srt s
    | GenTree.Leaf (inr n) => Ref n
    | GenTree.Node n.+3 l => Evar n (map term_decode l)
    | GenTree.Node n [:: t; u] =>
      (op_decode n) (term_decode t) (term_decode u)
    | _ => Srt prop
  end.

Lemma term_codeK : cancel term_encode term_decode.
Proof.
move=> t; elim: (depth t) {-2}t (leqnn (depth t)) =>
  [|d IHd] {t} [s|id l|b t u|n] //=; rewrite ?ltnS.
  by elim: l=> //= t l IHl /=; rewrite geq_max => /andP [/IHd-> /IHl [->]].
by rewrite ?geq_max => /andP [/IHd-> /IHd->]; case: b.
Qed.

Definition term_eqMixin := CanEqMixin term_codeK.
Canonical term_eqType := EqType term term_eqMixin.

Lemma term_rectl (P : term -> Type) :
(forall s : sort, P (Srt s)) ->
(forall (b : op) (t u : term), P t -> P u -> P (b t u)) ->
(forall (n : nat) (l : seq term), 
   (forall t, t \in l -> P t) ->  P (Evar n l)) ->
(forall n : nat, P (Ref n)) ->
 forall t : term, P t.
Proof.
move=> Ps Pb PEvar Pn t.
elim: (depth t) {-2}t (leqnn (depth t)) => [|d IHd] {t} [s|id l|b t u|n] //=.
  rewrite ltnS => Pl; apply: PEvar; elim: l Pl => [|t l IHl] //=.
  rewrite geq_max => /andP [/IHd Pt /IHl Pl] u.
  by rewrite in_cons; case: eqP => [->|_ /Pl].
by rewrite ltnS ?geq_max => /andP [/IHd ? /IHd ?]; apply: Pb.
Qed.


Fixpoint lift_rec (n : nat) (t : term) (k : nat) {struct t} : term :=
  match t with
  | Srt s => Srt s
  | Ref i => Ref (if k <= i then n + i else i)
  | Op b t u => b (lift_rec n t k) (lift_rec n u (is_abs b + k))
  | Evar id l => Evar id (map (fun A => lift_rec n A k) l)
  end.

Definition lift n t := lift_rec n t 0.

Fixpoint subst_rec (N M : term) (k : nat) {struct M} : term :=
  match M with
  | Srt s => Srt s
  | Ref i =>
      if i < k then Ref i
      else if k == i then lift k N
      else Ref (i.-1)
  | Op b t u => b (subst_rec N t k) (subst_rec N u (is_abs b + k))
  | Evar n l => Evar n [seq subst_rec N U k | U <- l]
  end.

Definition subst N M := subst_rec N M 0.

Inductive subterm : term -> term -> Prop :=
  | sbtrm_op_l (b : op) t u : subterm t (b t u)
  | sbtrm_op_r (b : op) t u : subterm u (b t u).

Inductive mem_sort (s : sort) : term -> Prop :=
  | mem_eq : mem_sort s (Srt s)
  | mem_op_l (b : op) u v : mem_sort s u -> mem_sort s (b u v)
  | mem_op_r (b : op) u v : mem_sort s v -> mem_sort s (b u v).

End Termes.

Hint Constructors subterm: coc.
Hint Constructors mem_sort: coc.


Section Beta_Reduction.

Inductive red1 : term -> term -> Prop :=
  | beta M N T : red1 (App (Abs T M) N) (subst N M)
  | red1l (b : op) M M' N : red1 M M' -> red1 (b M N) (b M' N)
  | red1r (b : op) M M' N : red1 M M' -> red1 (b N M) (b N M').

Inductive red (M : term) : term -> Prop :=
  | red_refl : red M M
  | red_trans1 R N : red M R -> red1 R N -> red M N.

Inductive conv (M : term) : term -> Prop :=
  | conv_refl : conv M M
  | conv_trans1 P N : conv M P -> red1 P N -> conv M N
  | conv_trans1V P N : conv M P -> red1 N P -> conv M N.

Inductive par1 : term -> term -> Prop :=
  | par1_beta M M' N N' T : par1 M M' -> par1 N N' -> 
                           par1 (App (Abs T M) N) (subst N' M')
  | par1_sort s : par1 (Srt s) (Srt s)
  | par1_ref n : par1 (Ref n) (Ref n)
  | par1_op (b : op) M M' T T' :  par1 M M' -> par1 T T' ->
                                  par1 (b T M) (b T' M').

Definition par := clos_trans term par1.

End Beta_Reduction.


Hint Constructors red1: coc.
Hint Constructors par1: coc.
Hint Unfold par: coc.

Hint Resolve red_refl conv_refl.

Section Normalisation_Forte.

Definition normal t := forall u, ~ red1 t u.

Definition sn := Acc (transp _ red1).

End Normalisation_Forte.

Hint Unfold sn: coc.

Lemma inv_lift_sort s n t k : lift_rec n t k = Srt s -> t = Srt s.
Proof. by case: t. Qed.

Lemma inv_subst_sort s x t k : subst_rec x t k = Srt s -> t = Srt s \/ x = Srt s.
Proof.
case: t => //= n; first by left.
by case: ltngtP => // -> /inv_lift_sort; right.
Qed.

Lemma lift_ref_ge k n p : p <= n -> lift_rec k (Ref n) p = Ref (k + n).
Proof. by move=> /= ->. Qed.

Lemma lift_ref_lt k n p : p > n -> lift_rec k (Ref n) p = Ref n.
Proof. by move=> /=; case: leqP. Qed.

Lemma subst_ref_lt u n k : k > n -> subst_rec u (Ref n) k = Ref n.
Proof. by move=> /=; case: ltngtP. Qed.

Lemma subst_ref_gt u n k : n > k -> subst_rec u (Ref n) k = Ref (n.-1).
Proof. by move=> /=; case: ltngtP. Qed.

Lemma subst_ref_eq u n : subst_rec u (Ref n) n = lift n u.
Proof. by rewrite /= ltnn eqxx. Qed.

Lemma lift_rec0 M k : lift_rec 0 M k = M.
Proof.
elim/term_rectl: M => // [b t u IHt IHu|n l Pl|n] /= in k *.
- by rewrite IHt IHu.
- by congr Evar; apply/map_id_in => t tl; apply: Pl.
- by case: leqP.
Qed.

Lemma lift0 M : lift 0 M = M. Proof. exact: lift_rec0. Qed.

Lemma simpl_lift_rec M n k p i :
   i <= k + n ->
   k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k.
Proof.
move=> le_i_kn leki.
elim/term_rectl: M => //= [b t u IHt IHu|m l Pl|m]
 in k p i le_i_kn leki *.
- by case: b; rewrite ?IHt ?IHu.
- by congr Evar; rewrite -!map_comp; apply/eq_in_map => t tl; apply: Pl.
have [lekm|gtkm] := leqP k m.
  by rewrite (leq_trans le_i_kn) ?addnA // addnC leq_add2l.
by rewrite leqNgt (leq_trans gtkm).
Qed.

Lemma liftS M n : lift n.+1 M = lift 1 (lift n M).
Proof. by rewrite [RHS]simpl_lift_rec. Qed.

Lemma permute_lift_rec M n k p i : i <= k ->
 lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k).
Proof.
move=> leik.
elim/term_rectl: M => //= [b t u IHt IHu|m l Pl|m] in k p i leik *.
- by case: b; rewrite ?IHt ?IHu ?addnS.
- by congr Evar; rewrite -!map_comp; apply/eq_in_map => t tl; apply: Pl.
have [lekm|gtkm] := leqP k m.
  rewrite !(leq_trans leik) ?(leq_trans _ (leq_addl n m)) //.
  by rewrite leq_add2l ?lekm addnCA.
have [leim|gtim] := leqP i m.
  by rewrite leq_add2l leqNgt gtkm.
by rewrite leqNgt (leq_trans gtkm) // leq_addl.
Qed.

Lemma permute_lift M k : lift 1 (lift_rec 1 M k) = lift_rec 1 (lift 1 M) (S k).
Proof. exact: permute_lift_rec. Qed.

Lemma simpl_subst_rec N M n p k : p <= n + k -> k <= p ->
  subst_rec N (lift_rec n.+1 M k) p = lift_rec n M k.
Proof.
move=> le_p_nk lekp.
elim/term_rectl: M => //= [b t u IHt IHu|m l Pl|m]
  in n k p le_p_nk lekp *.
- by case: b; rewrite ?IHt ?IHu ?addnS.
- by congr Evar; rewrite -!map_comp; apply/eq_in_map => t tl; apply: Pl.
have [lekm|gtkm] := leqP k m; last by rewrite (leq_trans gtkm).
have ltp: p < n.+1 + m.
  by rewrite addSn ltnS (leq_trans le_p_nk) // leq_add2l.
by rewrite ltnNge ltnW //= ltn_eqF // (leq_trans lekp gtkm).
Qed.

Lemma simpl_subst N M n p : p <= n -> subst_rec N (lift n.+1 M) p = lift n M.
Proof. by move=> ?; rewrite simpl_subst_rec ?addn0. Qed.

Lemma commut_lift_subst_rec M N n p k : k <= p ->
   lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
Proof.
move=> lekp.
elim/term_rectl: M => //= [b t u IHt IHu|m l Pl|m] in n p k lekp *.
- by case: b; rewrite ?IHt ?IHu ?(ltnS, addnS).
- by congr Evar; rewrite -!map_comp; apply/eq_in_map => t tl; apply: Pl.
have [ltpm|ltmp|<-] //= := ltngtP; first 2 last.
- by rewrite lekp ltnn eqxx /= simpl_lift_rec.
- have m_gt0: 0 < m by rewrite (leq_trans _ ltpm).
  rewrite !(leq_trans lekp) // ?(ltnW ltpm) -?[_ <= _.-1]ltnS ?prednK //.
  by rewrite ltn_add2l ltnNge ltnW //= eqn_add2l ltn_eqF // -!subn1 addnBA.
- have [lekm|gtkm] := leqP k m; first by rewrite ltn_add2l ltmp /=.
  by rewrite (leq_trans gtkm) ?(leq_trans _ (leq_addl _ _)) //= leqNgt gtkm. 
Qed.

Lemma commut_lift_subst M N k :
  subst_rec N (lift 1 M) (S k) = lift 1 (subst_rec N M k).
Proof. by rewrite -commut_lift_subst_rec. Qed.

Lemma distr_lift_subst_rec M N n p k :
   lift_rec n (subst_rec N M p) (p + k) =
   subst_rec (lift_rec n N k) (lift_rec n M ((p + k).+1)) p.
Proof.
elim/term_rectl: M => //= [b t u IHt IHu|m l Pl|m] in n p k *.
- by case: b; rewrite ?IHt ?IHu.
- by congr Evar; rewrite -!map_comp; apply/eq_in_map => t tl; apply: Pl.
have [ltpm|ltmp|<-] //= := ltngtP; first 2 last.
- by rewrite [p + k < p]ltnNge leq_addr /= ltnn eqxx -permute_lift_rec.
- have m_gt0: 0 < m by rewrite (leq_trans _ ltpm).
  rewrite -ltnS prednK //.
  have [lt_pk_m|le_m_pk] := ltnP; last by rewrite ltn_gtF ?ltn_eqF.
  rewrite ltn_gtF ?ltn_eqF ?(leq_trans ltpm) ?leq_addl //=.
  by rewrite -!subn1 addnBA.
- by rewrite leqNgt [_ < m]ltn_gtF ?(leq_trans ltmp) ?leq_addr. 
Qed.

Lemma distr_lift_subst M N n k :
   lift_rec n (subst N M) k = subst (lift_rec n N k) (lift_rec n M k.+1).
Proof. by rewrite distr_lift_subst_rec. Qed.

Lemma distr_subst_rec M N P n p :
   subst_rec P (subst_rec N M p) (p + n) =
   subst_rec (subst_rec P N n) (subst_rec P M ((p + n).+1)) p.
Proof.
elim/term_rectl: M => //= [b t u IHt IHu|m l Pl|m] in n p *.
- by case: b; rewrite ?IHt ?IHu.
- by congr Evar; rewrite -!map_comp; apply/eq_in_map => t tl; apply: Pl.
have [ltpm|ltmp|<-] //= := ltngtP.
- rewrite ltnS //=.          
  case: m ltpm => //= m; rewrite !ltnS eqSS.
  have [le_pn_m|lt_m_pn|<-] //= := ltngtP => lepm.
  - by rewrite ltnNge lepm /= ltn_eqF // (leq_trans _ le_pn_m) ?leq_addr.
  - by rewrite ltn_gtF ?ltnS // ltn_eqF.
  - by rewrite simpl_subst.
- rewrite (leq_trans ltmp) ?leq_addr ?ltnS //.
  by rewrite (leq_trans (ltnW ltmp)) ?leq_addr //= ltmp.
- by rewrite ltnS leq_addr /= ltnn eqxx -commut_lift_subst_rec.
Qed.

Lemma distr_subst P N M k :
  subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k)).
Proof. exact: distr_subst_rec. Qed.

Coercion red1_red M N : red1 M N -> red M N.
Proof. exact: red_trans1. Qed.

Lemma red_trans M N P : red M N -> red N P -> red M P.
Proof.
by move=> redMN redNP; elim: redNP => // P' N' _ /red_trans1 redMt /redMt.
Qed.

Lemma red1_red_ind N (P : term -> Prop) : P N ->
   (forall M R, red1 M R -> red R N -> P R -> P M) ->
   forall M, red M N -> P M.
Proof.
move=> PN PM M redMN; elim: redMN => [//|{N} R N redMR IHM red1RN] in PN PM *.
apply: IHM => [|M' R' red1M'R' redR'R]; first exact: PM PN.
by apply: PM => //; apply: red_trans1 redR'R _.
Qed.


Lemma red_Op (b : op) u u' v v' : 
  red u u' -> red v v' -> red (b u v) (b u' v').
Proof.
elim.
  elim => // w t redvw redb redwt.
  by apply: red_trans1 redb (red1r _ _ _).
move=> w t reduw redb red1wt redvv'.
exact: red_trans1 (redb _) (red1l _ _ _).
Qed.

Hint Resolve red_Op red1_red : coc.

Lemma red1_lift n k u v : red1 u v -> red1 (lift_rec n u k) (lift_rec n v k).
Proof.
move=> red1uv.
elim: red1uv k => //= [t w T|b w w' t|b t t' w]; do ?by auto with coc.
by move=> k; rewrite add1n distr_lift_subst; by auto with coc.
Qed.

Hint Resolve red1_lift: coc.

(* Cyril: I stopped here *)

Lemma red1_subst_r :
  forall a t u,
    red1 t u -> forall k, red1 (subst_rec a t k) (subst_rec a u k).
simple induction 1; simpl in |- *; intros; auto with coc.
rewrite distr_subst; auto with coc.
Qed.


  Lemma red1_subst_l :
   forall t u,
   red1 t u -> forall a k, red (subst_rec t a k) (subst_rec u a k).
simple induction a; simpl in |- *; auto with coc.
intros.
elim (lt_eq_lt_dec k n); intros; auto with coc.
elim a0; auto with coc.
unfold lift in |- *; auto with coc.
Qed.

  Hint Resolve red1_subst_l red1_subst_r: coc.


  Lemma red_prod_prod :
   forall u v t,
   red (Prod u v) t ->
   forall P : Prop,
   (forall a b, t = Prod a b -> red u a -> red v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc.
apply trans_red with a; auto with coc.

apply H3 with a N2; auto with coc.
apply trans_red with b; auto with coc.
Qed.


  Lemma red_sort_sort : forall s t, red (Srt s) t -> t <> Srt s -> False.
simple induction 1; intros; auto with coc.
apply H1.
generalize H2.
case P; intros; try discriminate.
inversion_clear H4.
Qed.



  Lemma one_step_conv_exp : forall M N, red1 M N -> conv N M.
intros.
apply trans_conv_exp with N; auto with coc.
Qed.


  Lemma red_conv : forall M N, red M N -> conv M N.
simple induction 1; auto with coc.
intros; apply trans_conv_red with P; auto with coc.
Qed.

  Hint Resolve one_step_conv_exp red_conv: coc.


  Lemma sym_conv : forall M N, conv M N -> conv N M.
simple induction 1; auto with coc.
simple induction 2; intros; auto with coc.
apply trans_conv_red with P0; auto with coc.

apply trans_conv_exp with P0; auto with coc.

simple induction 2; intros; auto with coc.
apply trans_conv_red with P0; auto with coc.

apply trans_conv_exp with P0; auto with coc.
Qed.

  Hint Immediate sym_conv: coc.


  Lemma trans_conv_conv : forall M N P, conv M N -> conv N P -> conv M P.
intros.
generalize M H; elim H0; intros; auto with coc.
apply trans_conv_red with P0; auto with coc.

apply trans_conv_exp with P0; auto with coc.
Qed.


  Lemma conv_conv_prod :
   forall a b c d, conv a b -> conv c d -> conv (Prod a c) (Prod b d).
intros.
apply trans_conv_conv with (Prod a d).
elim H0; intros; auto with coc.
apply trans_conv_red with (Prod a P); auto with coc.

apply trans_conv_exp with (Prod a P); auto with coc.

elim H; intros; auto with coc.
apply trans_conv_red with (Prod P d); auto with coc.

apply trans_conv_exp with (Prod P d); auto with coc.
Qed.


  Lemma conv_conv_lift :
   forall a b n k, conv a b -> conv (lift_rec n a k) (lift_rec n b k).
intros.
elim H; intros; auto with coc.
apply trans_conv_red with (lift_rec n P k); auto with coc.

apply trans_conv_exp with (lift_rec n P k); auto with coc.
Qed.
 

  Lemma conv_conv_subst :
   forall a b c d k,
   conv a b -> conv c d -> conv (subst_rec a c k) (subst_rec b d k).
intros.
apply trans_conv_conv with (subst_rec a d k).
elim H0; intros; auto with coc.
apply trans_conv_red with (subst_rec a P k); auto with coc.

apply trans_conv_exp with (subst_rec a P k); auto with coc.

elim H; intros; auto with coc.
apply trans_conv_conv with (subst_rec P d k); auto with coc.

apply trans_conv_conv with (subst_rec P d k); auto with coc.
apply sym_conv; auto with coc.
Qed.

  Hint Resolve conv_conv_prod conv_conv_lift conv_conv_subst: coc.


  Lemma refl_par1 : forall M, par1 M M.
simple induction M; auto with coc.
Qed.

  Hint Resolve refl_par1: coc.


  Lemma red1_par1 : forall M N, red1 M N -> par1 M N.
simple induction 1; auto with coc; intros.
Qed.

  Hint Resolve red1_par1: coc.


  Lemma red_par : forall M N, red M N -> par M N.
red in |- *; simple induction 1; intros; auto with coc.
apply t_trans with P; auto with coc.
Qed.


  Lemma par_red : forall M N, par M N -> red M N.
simple induction 1.
simple induction 1; intros; auto with coc.
apply trans_red with (App (Abs T M') N'); auto with coc.

intros.
apply trans_red_red with y; auto with coc.
Qed.

  Hint Resolve red_par par_red: coc.


  Lemma par1_lift :
   forall n a b,
   par1 a b -> forall k, par1 (lift_rec n a k) (lift_rec n b k).
simple induction 1; simpl in |- *; auto with coc.
intros.
rewrite distr_lift_subst; auto with coc.
Qed.


  Lemma par1_subst :
   forall a b c d,
   par1 a b ->
   par1 c d -> forall k, par1 (subst_rec a c k) (subst_rec b d k).
simple induction 2; simpl in |- *; auto with coc; intros.
rewrite distr_subst; auto with coc.

elim (lt_eq_lt_dec k n); auto with coc; intros.
elim a0; intros; auto with coc.
unfold lift in |- *.
apply par1_lift; auto with coc.
Qed.


  Lemma inv_par_abs :
   forall (P : Prop) T U x,
   par1 (Abs T U) x ->
   (forall T' U', x = Abs T' U' -> par1 U U' -> P) -> P.
do 5 intro.
inversion_clear H; intros.
apply H with T' M'; auto with coc.
Qed.

  Hint Resolve par1_lift par1_subst: coc.



  Lemma mem_sort_lift :
   forall t n k s, mem_sort s (lift_rec n t k) -> mem_sort s t.
simple induction t; simpl in |- *; intros; auto with coc.
generalize H; elim (le_gt_dec k n); intros; auto with coc.
inversion_clear H0.

inversion_clear H1.
apply mem_abs_l; apply H with n k; auto with coc.

apply mem_abs_r; apply H0 with n (S k); auto with coc.

inversion_clear H1.
apply mem_app_l; apply H with n k; auto with coc.

apply mem_app_r; apply H0 with n k; auto with coc.

inversion_clear H1.
apply mem_prod_l; apply H with n k; auto with coc.

apply mem_prod_r; apply H0 with n (S k); auto with coc.
Qed.


  Lemma mem_sort_subst :
   forall b a n s,
   mem_sort s (subst_rec a b n) -> mem_sort s a \/ mem_sort s b.
simple induction b; simpl in |- *; intros; auto with coc.
generalize H; elim (lt_eq_lt_dec n0 n); intro.
elim a0; intros.
inversion_clear H0.

left.
apply mem_sort_lift with n0 0; auto with coc.

intros.
inversion_clear H0.

inversion_clear H1.
elim H with a n s; auto with coc.

elim H0 with a (S n) s; auto with coc.

inversion_clear H1.
elim H with a n s; auto with coc.

elim H0 with a n s; auto with coc.

inversion_clear H1.
elim H with a n s; auto with coc.

elim H0 with a (S n) s; intros; auto with coc.
Qed.


  Lemma red_sort_mem : forall t s, red t (Srt s) -> mem_sort s t.
intros.
pattern t in |- *.
apply red1_red_ind with (Srt s); auto with coc.
do 4 intro.
elim H0; intros.
elim mem_sort_subst with M0 N 0 s; intros; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.
Qed.



  Lemma red_normal : forall u v, red u v -> normal u -> u = v.
simple induction 1; auto with coc; intros.
absurd (red1 u N); auto with coc.
absurd (red1 P N); auto with coc.
elim (H1 H3).
unfold not in |- *; intro; apply (H3 N); auto with coc.
Qed.



  Lemma sn_red_sn : forall a b, sn a -> red a b -> sn b.
unfold sn in |- *.
simple induction 2; intros; auto with coc.
apply Acc_inv with P; auto with coc.
Qed.


  Lemma commut_red1_subterm : commut _ subterm (transp _ red1).
red in |- *.
simple induction 1; intros.
exists (Abs z B); auto with coc.

exists (Abs A z); auto with coc.

exists (App z B); auto with coc.

exists (App A z); auto with coc.

exists (Prod z B); auto with coc.

exists (Prod A z); auto with coc.
Qed.


  Lemma subterm_sn : forall a, sn a -> forall b, subterm b a -> sn b.
unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
elim commut_red1_subterm with x b y; intros; auto with coc.
apply H1 with x0; auto with coc.
Qed.


  Lemma sn_prod : forall A, sn A -> forall B, sn B -> sn (Prod A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc.
apply H1; auto with coc.
apply Acc_intro; auto with coc.
Qed.


  Lemma sn_subst : forall T M, sn (subst T M) -> sn M.
intros.
cut (forall t, sn t -> forall m, t = subst T m -> sn m).
intros.
apply H0 with (subst T M); auto with coc.

unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
apply H2 with (subst T y); auto with coc.
rewrite H3.
unfold subst in |- *; auto with coc.
Qed.
