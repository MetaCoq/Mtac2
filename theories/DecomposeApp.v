From Mtac2 Require Import Base Datatypes List Sorts Specif MTele Tactics MFixDef MTeleMatchDef.
Import Sorts.S.
Import M.notations.
Import ListNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** Given `(A T : Type) (t : T)`, derive
    - `m : MTele`
    - `MTele_Const A m`
    such that
    - `T = MTele_Const A m`
    - `t : MTele_Const A m`
*)

(* FIX: proper error messaging *)
Definition MTele_of (A : Type) : forall T, T -> M (msigT (MTele_Const (s:=Typeₛ) A)) :=
  let matchtele := fun T => mTele (fun _ : T => mBase) in
  let fixtele := mTele (matchtele) in
  mfix'
    (m:=fixtele)
    (fun T (_ : T) => msigT (MTele_Const (s:=Typeₛ) A))
    (
      fun f T =>
        mtmmatch'
          _
          matchtele
          _
          T
          [m:
             branch_pattern (@pbase
                _
                (fun T => T -> M (msigT (MTele_Const (s:=Typeₛ) A)))
                A
                (fun t : A => M.ret (mexistT (MTele_Const (s:=Typeₛ) A) mBase t))
                UniCoq
             )
          |  branch_pattern (ptele (fun (X : Type) => ptele (fun (F : forall x : X, Type) =>
              @pbase
                _
                (fun T => T -> M (msigT (MTele_Const (s:=Typeₛ) A)))
                (forall x : X, F x)
                (fun t : _ =>
                   M.nu (FreshFrom T) mNone (fun x =>
                                   let Fx := reduce (RedOneStep [rl:RedBeta]) (F x) in
                                   let tx := (* rone_step *) (t x) in
                                   '(mexistT _ n T) <- f Fx tx;
                                   n' <- M.abs_fun (P:=fun _ => MTele) x n;
                                   T' <- M.coerce T;
                                   T' <- M.abs_fun (P:=fun x => MTele_Const (s:=Typeₛ) A (n' x)) x T';
                                   M.ret (mexistT (MTele_Const (s:=Typeₛ) A) (mTele n') T')
                                )
                )
                UniCoq
             )))
          ]
    ).

Definition decompose_app {m : MTele} {A : Type} {B : A -> Type} {C : MTele_ConstT A m} {T: Type} (a : A) (t : T)
  :
  M (Unification -> MTele_sort (MTele_ConstMap (si:=Typeₛ) Propₛ (fun a : A => M (B a)) C) -> M (B a)) :=
  (
    '(mexistT _ m' T') <- MTele_of A T t;
    M.unify m m' UniCoq;;
    M.cumul UniCoq C t;;
    let x := fun u => @M.decompose_app' A B m u a C in
    M.ret x
  ).

Notation "'<[decapp' a 'return' T 'with' b ]>" :=
  (
    ltac:(mrun (decompose_app (B:=T) a b))
  )
  (at level 0, a at next level, b at next level) : M_scope.

Notation "'<[decapp' a 'with' b ]>" :=
  (
    ltac:(mrun (decompose_app (A:=?[A]) (B:=fun _ : ?A => _) a b))
  )
  (at level 0, a at next level, b at next level) : M_scope.


Local Definition mtele_convert' {A : Type} {B : A -> Prop} {G : Type} {mt:MTele} {C : MTele_ConstT A mt} :
  MTele_sort (MTele_ConstMap (si:=Typeₛ) Propₛ (fun a => G -> B a) C)
  -> (G -> MTele_sort (MTele_ConstMap (si:=Typeₛ) Propₛ B C)).
induction mt as [|X F IHmt].
- cbn. refine (fun x => x).
- cbn. intros ? ? ?.
  refine (IHmt _ _ _ _); auto.
  apply X0.
Defined.

Definition decompose_app_tactic {m : MTele} {A : Type} {B : A -> Type} {C : MTele_ConstT A m} {T: Type} (a : A) (t : T) :
  M (Unification -> MTele_sort (MTele_ConstMap (si:=Typeₛ) Propₛ (fun a : A => gtactic (B a)) C) -> gtactic (B a)) :=
  (
    '(mexistT _ m' T') <- MTele_of A T t;
    M.unify m m' UniCoq;;
    M.cumul UniCoq C t;;
    let x := fun uni f (g : goal gs_open) => @M.decompose_app' A (fun a => mlist (mprod (B a) (goal gs_any))) m uni a C (f g) in
    let y := fun uni f => x uni (mtele_convert' f) in
    M.ret y
  ).

Notation "'<[decapp' a 'return' T 'with' b ]>" :=
  (
      ltac:(mrun (decompose_app_tactic (B:=T) a b))
  )
  (at level 0, a at next level, b at next level) : tactic_scope.

Notation "'<[decapp' a 'with' b ]>" :=
  (
    ltac:(mrun (decompose_app_tactic (A:=?[A]) (B:=fun _ : ?A => _) a b))
  )
  (at level 0, a at next level, b at next level) : tactic_scope.