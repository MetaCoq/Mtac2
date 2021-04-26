From Mtac2 Require Import Base Logic Datatypes List MTele.
Import M.notations.
Import Sorts.S.
Import ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.


Local Notation MFA T := (MTele_val (MTele_C Typeₛ Propₛ M T)).

Definition open_pattern {A} {m} {T : forall x, MTele_Ty (m x)} {y : A} {a : ArgsOf (m y)} :
  forall(p : pattern A (fun x => MFA (T x))), M (apply_sort (T y) a) :=
  Eval lazy beta iota match zeta delta [meq_sym] in
  fix go p :=
  match p return M _ with
  | pany f => apply_C Propₛ (f y) a
  | pbase x f u =>
    oeq <- M.unify x y u;
    match oeq return M (apply_sort (T y) a) with
    | mSome eq =>
      match eq in meq _ z return forall a : ArgsOf (m z), M (apply_sort (T z) a) with
      | meq_refl => apply_C Propₛ f
      end a
    | mNone => M.raise DoesNotMatch
    end
  | ptele f => c <- M.evar _; go (f c)
  | psort f =>
    M.mtry'
      (go (f Propₛ))
      (fun e =>
         oeq <- M.unify e DoesNotMatch UniMatchNoRed;
         match oeq with
         | mSome _ => go (f Typeₛ)
         | mNone => M.raise e
         end
      )
  end
.

Import String.
Open Scope string_scope.
Definition open_branch {A} {m} {T : forall x, MTele_Ty (m x)} {y : A} {a : ArgsOf (m y)}
           (b : branch A (fun x => MFA (T x))) : M (apply_sort (T y) a) :=
  let open_pattern' := @open_pattern A m T y a in
  match b in branch A P return (pattern A P -> _) -> M _ with
  | branch_pattern p => fun open_pattern' => open_pattern' p
  | _ => fun _ => mfail "Unsupported branch type in mtmmatch: " b
  end open_pattern'.

Definition mtmmatch' A m (T : forall x, MTele_Ty (m x)) (y : A)
           (ps : mlist (branch A (fun x => MFA (T x)))) : selem_of (MFA (T y)) :=
  curry_C
    Propₛ
    (fun a : ArgsOf (m y) =>
       (fix mmatch' (ps : mlist (branch A (fun x => MFA (T x)))) :=
          match ps with
          | [m:] => M.raise NoPatternMatches
          | p :m: ps' =>
            M.mtry' (open_branch p)
                    (fun e =>
                       mif M.unify e DoesNotMatch UniMatchNoRed then mmatch' ps' else M.raise e)
          end) ps
    ).


Module TestFin.
Require Fin.
Polymorphic Definition mt : nat -> MTele := fun n => mTele (fun _ : Fin.t n => mBase).
Definition T : forall n, MTele_Ty (mt n) := fun n _ => True.
Definition pO u : pattern nat _ := @pbase _ (fun x => MTele_ty M (n:=mt x) (T x)) 0 ((* ex_intro _ 0 *) (fun x => Fin.case0 (fun _ => M True) x)) u.
Definition p1 u : pattern nat _ := @pbase _ (fun x => MTele_ty M (n:=mt x) (T x)) 1 ((* ex_intro _ 1 *) (fun n => M.ret I)) u.
Definition pi u : pattern nat (fun x => MTele_ty M (n:=mt x) (T x)) :=
  ptele (fun i : nat =>
             @pbase _ _  i ((* ex_intro _ i *) (fun n => M.ret I)) u
          ).

Program Example pbeta : pattern nat (fun x => MTele_ty M (n:=mt x) (T x)) :=
  ptele (fun i : nat =>
            @pbase _ (* (fun x => MTele_ty M (mt x)) *) _ (i+1) ((* ex_intro _ (i + 1) *) (fun n : Fin.t (i + 1) => M.ret I)) UniCoq
         ).
End TestFin.
