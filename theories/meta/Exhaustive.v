From Mtac2 Require Import Base List Datatypes.
Import M.notations.
Import Datatypes.ProdNotations.


Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

(** This file implements exhaustive [mmatch]es by introducing the [mmatch t
    exhaustively_with ... end] syntax.

    We currently consider only [[# ] c | x .. y ] nodes, and only those that
    have an unapplied constructor [c] on the left-hand side of [|].
 *)

Definition ConstrNotFound : Exception. constructor. Qed.
Definition ConstrsUnmentioned (m : mlist dyn) : Exception. constructor. Qed.

Definition find_in_constrs {C} (c : C)  : mlist dyn -> M (mlist dyn) :=
  mfix1 f (cs : _) : M _ :=
    match cs with
    | mnil => M.ret mnil
    | mcons c' cs =>
      '(m: c, _) <- M.decompose c;
      dcase c as C, c in
      let C := reduce (RedVmCompute) C in
      mmatch c' with
      | @Dyn C c =n> M.ret cs
      | _ => l <- f cs; M.ret (c' :m: l)
      end
    end.


Definition check_exhaustiveness {A B}
           (ps_in : mlist (branch A B))
           (ops : moption (mlist (branch A B))) :
  M (mlist (branch A B)) :=
  '(mkInd_dyn _ _ _ constrs) <- M.constrs A;
  (
    mfix2 f (ps : _) (constrs : _) : M _ :=
      match ps, constrs with
      | mnil, mnil =>
        match ops with
        | mNone => M.ret ps_in
        | mSome ps' => let ps := dreduce (@mapp) (mapp ps_in ps') in
                       M.ret ps
        end
      | mcons p ps, _ =>
        match p with
        | branch_app_static U C _ =>
          constrs <- find_in_constrs C constrs;
          f ps constrs
        | _ => f ps constrs
        end
      | _, _ => M.raise (ConstrsUnmentioned constrs)
      end
  ) ps_in constrs
.

Notation "'exhaustively' ls" :=
  (
    ltac:(mrun (check_exhaustiveness ls (mNone)))
  )
    (in custom Mtac2_with_branch at level 91, ls custom Mtac2_with_branch).
