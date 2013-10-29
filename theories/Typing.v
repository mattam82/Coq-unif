Require Import ssreflect.
Require Export Arith.
Require Export Compare_dec.
Require Export Relations.
Require Import ssrnat ssrfun ssrbool eqtype seq choice.
Require Import Utf8.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import TermEvar.

Arguments fst {A B} _.
Notation type := term.

(** Typing local context *) 
Definition ctx := list type.

Definition evar_context := list (ident * (option term * type)).

Inductive evar_decl : Set := 
  { evar_ctx : evar_context;
    evar_body : option term;
    evar_concl : type }.

Definition evar_map : Set :=
  nat -> option evar_decl.


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

Definition evar_map_fevs (e : evar_map) : list nat := [::].

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

Definition wf_evar_map (m : evar_map) :=
  let mfevs := evar_map_fevs m in
  forall k, if m k is Some x then 
              wf_evar_decl x && incl (evar_decl_fevs x) mfevs
            else false.

                                    