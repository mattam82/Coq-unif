Require Import ssreflect.
Require Export Arith.
Require Export Compare_dec.
Require Export Relations.
Require Import ssrnat ssrfun ssrbool eqtype seq choice.
Require Import ordtype finmap.
Require Import Utf8.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope SEQ.

Require Import TermEvar.

Arguments fst {A B} _.
Notation type := term.

(** Typing local context *) 
Definition ctx := list type.

Notation odef := (option term * type)%type.
Definition evar_context := list (ident * odef).

Inductive evar_decl : Set := 
  { evar_ctx : evar_context;
    evar_body : option term;
    evar_concl : type }.

Fixpoint closedn (n : nat) (t : term) : bool := 
  match t with
    | Srt s => true
    | Bnd n' => n' < n
    | Ref i => true
    | Op b t u => closedn n t && closedn (is_abs b + 1) u
    | Evar k l => all (closedn n) l
  end.

Definition closed := closedn 0.

Fixpoint fvs (t : term) : list ident :=
  match t with
    | Srt s => [::]
    | Bnd n' => [::]
    | Ref i => [:: i]
    | Op b t u => fvs t ++ fvs u
    | Evar k l => flatten (map fvs l)
  end.

Definition ctx_fvs (ctx : evar_context) := map fst ctx.

Fixpoint fevs (t : term) : list nat :=
  match t with
    | Srt s => [::]
    | Bnd n' => [::]
    | Ref i => [::]
    | Op b t u => fevs t ++ fevs u
    | Evar k l => k :: flatten (map fevs l)
  end.

Definition ctx_fevs (ctx : evar_context) := foldr (λ x acc, 
            let: (id, (b, ty)) := x in
              acc ++ oapp fevs [::] b ++ fevs ty) [::] ctx.

Definition evar_decl_fevs evd :=
  ctx_fevs evd.(evar_ctx) ++ 
  fevs evd.(evar_concl) ++
  oapp fevs [::] evd.(evar_body).

Definition wf_term (t : term) := 
  closed t.

Definition incl {A : eqType} (l l' : seq A) := 
  all (λ x, x \in l') l.

Definition wf_open_term (ctx : evar_context) (t : term) :=
  incl (fvs t) (ctx_fvs ctx).

Definition owf_open_term (ctx : evar_context) (b : option term) :=
  oapp (wf_open_term ctx) true b.

Definition wf_evar_context (ctx : evar_context) := 
  let: (wfctx, b) := 
     foldr (λ x acc, 
            let: (wfctx, wf) := acc in
            let: (id, (b, ty)) := x in
              (x :: wfctx, wf && wf_open_term wfctx ty &&
                              owf_open_term wfctx b))
           ([::], true) ctx
  in b.

Definition wf_evar_decl evd :=
  let ctx := evd.(evar_ctx) in
  wf_evar_context ctx &&
  owf_open_term ctx evd.(evar_body) &&
  wf_open_term ctx evd.(evar_concl).

Import Order.Theory.
Notation evar_map := {fmap nat -> evar_decl}.

Notation named_ctx := evar_context.
Notation local_ctx := (seq odef).

Notation def_elem := (None, Srt prop).

Fixpoint oget_def (N : named_ctx) (i : ident) : option odef :=
  match N with
  | [::] => None
  | ((j, e) :: N') => if i == j then Some e else oget_def N' i
  end.

Definition get_def (d : odef) (N : named_ctx) (i : ident) : odef :=
  if oget_def N i is Some def then def else d.

Notation "'[db' s ']' t" := (subst s t) (at level 20).

Reserved Notation "'[n' x ':=' t1 ']' t2" (at level 40).

Fixpoint nsubs x t1 t2 :=
  match t2 with
    | Srt _ | Bnd _ => t2
    | Ref i => if i == x then t1 else t2
    | Op b t u => 
      Op b ([n x:=t1]t) ([n x:=t1]u)
    | Evar n l => Evar n (map (nsubs x t1) l)
  end
where "'[n' x ':=' t1 ']' t2" := (nsubs x t1 t2).

Fixpoint nmulti_subs (n : named_ctx) (s : seq term) t :=
  match n, s with
    | [::], [::] => Some t
    | ((x, _) :: n'), (t' :: s') => nmulti_subs n' s' ([n x:=t']t)
    | _ , _ => None
  end.

Notation "'[n' l '::=' t1 ']' t2" := (nmulti_subs l t1 t2) (at level 40).

Reserved Notation "E '||-' t '~' T" (at level 40).
Reserved Notation "E '||-*' s '~' c" (at level 40).

Reserved Notation "E '||-' t1 '-->' t2" (at level 40).

Inductive red1 : (evar_map * named_ctx * local_ctx) -> term -> term -> Prop :=
  | beta C M N T : C ||- App (Abs T M) N --> subst N M
  | deltaN E N L i t T :
      oget_def N i = Some (Some t, T) ->
      (E, N, L) ||- Ref i --> t
  | deltaL E N L n t T : 
      n < size L -> nth def_elem L n = (Some t, T) ->
      (E, N, L) ||- Bnd n --> t
  | deltaE E N L e s d b b':
      E.[e] = Some d -> d.(evar_body) = Some b ->
      [n d.(evar_ctx) ::= s]b = Some b' ->
      (E, N, L) ||- Evar e s --> b'
  | red1l (b : op) C M M' N : 
      C ||- M --> M' -> 
      C ||- b M N --> b M' N
  | red1r (b : op) C M M' N : 
      C ||- M --> M' -> 
      C ||- b N M --> b N M'
where  "E '||-' t1 '-->' t2" := (red1 E t1 t2).


Inductive conv (E : (evar_map * named_ctx * local_ctx)) (M : term) : term -> Prop :=
  | conv_refl : conv E M M
  | conv_trans1 P N : conv E M P -> red1 E P N -> conv E M N
  | conv_trans1V P N : conv E M P -> red1 E N P -> conv E M N.

Notation "E '||-' t '=?=' u" := (conv E t u) (at level 40). 


Definition bhas_type (C : (evar_map * named_ctx * local_ctx)) (t1 t2 : term) :=
  let: (E, N, L) := C in
  match t1, t2 with
  | Srt prop, Srt (kind _) => true
  | Srt (kind i), Srt (kind j) => i <= j
  | Bnd i, _ => if i < size L then t2 == (nth def_elem L i).2
                else false
  | Ref i, _ => if i \in map fst N then t2 == (get_def def_elem N i).2
                else false
  | _, _ => false
  end.
  


(* TODO: missing acyclic test in evar_map *)
Inductive has_type : (evar_map * named_ctx * local_ctx) -> term -> type -> Prop :=
| TBase C t1 t2 : bhas_type C t1 t2 -> has_type C t1 t2
(*| TAx1 E N L: 
    (E, N, L) ||- Srt prop ~ Srt (kind 1)
| TAx2 E N L i j:
    i <= j -> 
    (E, N, L) ||- Srt (kind i) ~ Srt (kind j)
| TVar E N L i:
    i < size L -> 
    (E, N, L) ||- Bnd i ~ (nth def_elem L i).2
| TConst E N L i:
    i \in map fst N ->
    (E, N, L) ||- Ref i ~ (get_def def_elem N i).2
*)
| TProd1 E N L T U s:
    (E, N, L) ||- T ~ Srt s -> 
    (E, N, (None, T) :: L) ||- U ~ Srt prop ->
    (E, N, L) ||- Op Prod T U ~ Srt prop
| TProd2 E N L T U i j k:
    i <= k -> j <= k ->
    (E, N, L) ||- T ~ Srt (kind i) -> 
    (E, N, (None, T) :: L) ||- U ~ Srt (kind j) ->
    (E, N, L) ||- Op Prod T U ~ Srt (kind k)
| TLam E N L T t U s1 s2:
    (E, N, L) ||- T ~ s1 -> 
    (E, N, (None, T) :: L) ||- t ~ U ->
    (E, N, L) ||- Op Prod T U ~ s2 ->
    (E, N, L) ||- Op Abs T t ~ Op Prod T U
| TApp C t u T U:
    C ||- t ~ Op Prod U T ->
    C ||- u ~ U ->
    C ||- Op App t u ~ [db u]T 
| TEvar E N L e d s T:
    E.[e] = Some d ->
    (E, N, L) ||-* s ~ d.(evar_ctx) ->
    [n d.(evar_ctx) ::= s](d.(evar_concl)) = Some T ->
    (E, N, L) ||- Evar e s ~ T
| TConv E t T U : 
    E ||- t ~ T ->
    E ||- T =?= U ->
    E ||- t ~ U
with has_types : (evar_map * named_ctx * local_ctx) -> seq term -> named_ctx -> Prop :=  
| CTId E : E ||-* [::] ~ [::]
| CTAss E x t T T' s N :
    E ||-* s ~ N ->
    [n N ::= s]T = Some T' ->
    E ||- t ~ T' ->
    E ||-* (t :: s) ~ ((x, (None, T)) :: N)
| CTDef E x t t' T T' s N :
    E ||-* s ~ N ->
    [n N ::= s]T = Some T' ->
    E ||- t ~ T' ->
    E ||- t =?= t' ->
    E ||-* (t :: s) ~ ((x, (Some t', T)) :: N)
where "E '||-' t '~' T" := (has_type E t T)
and "E '||-*' s '~' N" := (has_types E s N).

Definition wfE E := forall k v t, 
  E.[k] = Some v -> 
  (v.(evar_body) = None -> 
   exists s, (E, v.(evar_ctx), [::]) ||- v.(evar_concl) ~ Srt s) /\ 
  (v.(evar_body) = Some t -> 
   (E, v.(evar_ctx), [::]) ||- t ~ v.(evar_concl)).

Inductive wfN : evar_map -> named_ctx -> Prop :=
| WFN0 E : wfN E [::]
| WFNAss E (N : named_ctx) (x : ident) T s:
    x \notin (map fst N) ->
    (E, N, [::]) ||- T ~ Srt s ->
    wfN E ((x, (None, T)) :: N)
| WFNDef E (N : named_ctx) (x : ident) t T:
    x \notin (map fst N) ->
    (E, N, [::]) ||- t ~ T ->
    wfN E ((x, (Some t, T)) :: N).

Inductive wfL : (evar_map * named_ctx) -> local_ctx -> Prop :=
| WFL0 E N : wfL (E, N) [::] 
| WFLAss E N L T s: 
    (E, N, L) ||- T ~ Srt s ->  
    wfL (E, N) ((None, T) :: L)
| WFLDef E N L t T: 
    (E, N, L) ||- t ~ T ->  
    wfL (E, N) ((Some t, T) :: L).

Definition WF E N L := wfE E /\ wfN E N /\ wfL (E, N) L.

Lemma get_def_weak d N i i' e : i != i' -> 
  get_def d N i = get_def d ((i', e) :: N) i.
Proof. by move=>H; rewrite {2}/get_def /= (negbTE H). Qed.
Arguments get_def_weak [_ _ _] i' e _.

Lemma weakeningN E N L t T i V : 
  i \notin (map fst N) ->
  (E, N, L) ||- t ~ T ->
  (E, (i, V) :: N, L) ||- t ~ T.
Proof.
  move=>Hi H.
  induction H. ; subst; try by constructor.
  - rewrite (get_def_weak i V). apply TConst.
  - case Hi0: (i0 \in (map fst N)).
    rewrite /get_def.
    
  elim: t=>[s| n l | o t | | ] H.
  - inversion H; subst; try by constructor.
    apply (TConv H0 H1).
Lemma wfL_ref E N L i t T: 
  WF E N L -> (i, (Some t, T)) \in N -> 
  (E, N, L) ||- t ~ T.
Proof.
  elim: N=>[//| [j [ot' T']] N' IH].
  move=>H1 H2. move: H2 H1.
  rewrite inE.
  case/orP.
  - move/eqP. case=><- <- <-.
    move=>[WFE [WFN WFL]].
    inversion WFN; subst.
  move=>H1 H2.
Theorem progress E t u T : 
  E ||- t ~ T -> 
  E ||- t --> u ->
  E ||- u ~ T.
Proof.
elim; (try by (intros;
              match goal with
                  x : _ ||- _ --> _ |- _ => inversion x
              end)); move: E=>_.
- move=>E N L i.
  move=>H1 H2 H3.
  inversion H3; subst.
  rewrite H8.
  rewrite H8 in H2.
  rewrite /= in H2 *.
  inversion H2; subst.