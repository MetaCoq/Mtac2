Require Import Coq.Strings.String.
From Mtac2 Require Import Base Specif Logic Datatypes MTele MTeleMatchDef.
Import M.notations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition MTele_of {A:Type} (T : A -> Prop) : M (A -> msigT MTele_Ty) :=
  M.nu (FreshFrom T) mNone (fun a =>
  let T' := reduce (RedOneStep [rl:RedBeta]) (T a) in
  (mfix1 f (T : Prop) : M (msigT MTele_Ty) :=
    mmatch T return M (msigT MTele_Ty) with
    | [?X : Type] M X =u> M.ret (mexistT _ mBase X)
    | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =u>
      M.nu (FreshFrom T) mNone (fun x =>
                      let T' := reduce (RedOneStep [rl:RedBeta]) (F x) in
                      '(mexistT _ n T) <- f T';
                      n' <- M.abs_fun x n;
                      T' <- (M.coerce (B:=MTele_Ty (n' x)) T >>= M.abs_fun x);
                      M.ret (mexistT _ (mTele n') T')
                   )
   end
  ) (T') >>= (fun t =>
                (* M.print_term t;; *)
                t' <- M.abs_fun a t;
                (* M.print_term t';; *)
                M.ret t')).


Local Example test :=
fun x => mexistT MTele_Ty (mTele (fun _ : nat => mBase)) (fun y : nat => x = y).
Eval hnf in ltac:(mrun (MTele_of (fun x : nat => forall y:nat, M (x = y)))).
Local Example MTele_of_Test : nat -> msigT MTele_Ty :=
  Eval hnf in ltac:(mrun (MTele_of (fun x : nat => forall y:nat, M (x = y)))).

Class TC_UNIFY {T : Type} (A B : T) := tc_unify : (A =m= B).
Arguments tc_unify {_} _ _ {_}.
Definition tc_unify_mtac T (A B : T) :=
  (* M.print "tc_unify 1";; *)
  o <- @M.unify T A B UniCoq;
  (* M.print "tc_unify 2";; *)
  match o with
  | mSome eq => M.ret eq
  | mNone =>
    let A := reduce (RedStrong RedAll) A in
    let B := reduce (RedStrong RedAll) B in
    (* M.print_term (A,B);; *)
    M.failwith "cannot (tc_)unify."
  end.
Hint Extern 0 (@TC_UNIFY ?T ?A ?B) => mrun (tc_unify_mtac T A B) : typeclass_instances.

Class MT_OF {A} (T : A -> Prop) := mt_of : A -> msigT MTele_Ty.
Arguments mt_of {_} _ {_}.
Hint Extern 0 (@MT_OF ?A ?t) => mrun (@MTele_of A t) : typeclass_instances.


Notation "'mtmmatch' x 'as' y 'return' T 'with' p 'end'" :=
  (
    let mt1 := mt_of (fun y => T) in
    match tc_unify (fun _z => MTele_ty M (mprojT2 (mt1 _z))) ((fun y => T))
          in _ =m= R return mlist (branch _ R) -> R x with
    | meq_refl => mtmmatch' _ (fun _z => mprojT1 (mt1 _z)) (fun _z => mprojT2 (mt1 _z)) x
    end
    (p)
  ) (at level 200, p custom Mtac2_with_branch).

Local Example mt_of_test : MT_OF (fun x:nat => forall y:nat, M nat).
Proof. apply _. Qed.
(* Set Printing All. *)
Set Printing Universes.
Definition bluf := (fun x:(nat:Type) => forall y:(nat:Type), M (nat:Type)).
Eval hnf in ltac:(mrun (MTele_of (bluf))).
Local Example test1 :=
    let mt1 := ltac:(mrun (MTele_of bluf)) in
    let _ := ltac:(mrun (let mt1 := reduce (RedOneStep [rl:RedDelta]) mt1 in M.print_term mt1)) in
    ltac:(mrun(tc_unify_mtac _ (fun _z : (nat:Type) => MTele_ty M (mprojT2 (mt1 _z))) ((fun x:(nat:Type) => forall y:(nat:Type), M (nat:Type))))).


Local Program Example mtmmatch_prog_test (x : (nat : Type)) :=
  mtmmatch x as x return forall y, M (x = y) with
  | [?i] i =n>  fun y => M.failwith ""
end.


(* Alternative version, currently broken because of bidir. annotations. *)

Polymorphic Class MTY_OF {A} := MTt_Of { mty_of : A -> Prop }.
Arguments MTt_Of [_] _.

Polymorphic Class RET_TY (A : Type) := Ret_Ty { ret_ty : A }.
Arguments Ret_Ty [_] _.
Arguments ret_ty {_ _}.

Notation "'mtmmatch_alt' x 'as' y 'return' T 'with' p 'end'" :=
  (
    let mt1 := M.eval (MTele_of (fun y => T)) in
    let F : RET_TY _ := Ret_Ty (fun y => T) in
    let mt : MTY_OF := MTt_Of (fun _z => MTele_ty M (n:=mprojT1 (mt1 _z)) (mprojT2 (mt1 _z))) in
    mtmmatch' _ (fun y => mprojT1 (mt1 y)) (fun y => mprojT2 (mt1 y)) x p
  ) (at level 90, p custom Mtac2_with_branch).

Fail Local Example test_mtmmatch (n : nat) :=
  mtmmatch_alt n as n' return n = n' -> M (n = 1) with
  | 1 =n> fun H => M.ret H
  | _ as _catchall => fun H : n = _catchall => M.failwith "test"
  end.
