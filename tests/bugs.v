From Mtac2 Require Import Logic Datatypes Mtac2.

Require Import Bool.Bool.
Import T.

(** A bug with destruct *)
Goal forall n:nat, 0 <= n.
MProof.
  intros.
  (* destruct n. *) (* the type of the match seems to be wrong *)
Abort.

(** It was throwing an exception, but now it works *)
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
MProof.
intros n. cintros m {- destruct m -}.
Abort.

(** A bug with the call to UniCoq (solved) *)
Example fubar (T : Type) (A : T) : M Prop:=
  oeq <- M.unify Prop T UniCoq;
  match oeq with
  | mSome eq => M.ret (meq_rect Prop (fun T=>T -> Prop) id T eq A)
  | _ => M.raise exception
end.

Definition fubarType :=
  Eval compute in
  ltac:(mrun (mtry fubar Type (True <-> True) with _ => M.ret True end)%MC).

(* TODO: this test no longer works unless we want to import MTeleMatch here *)
(** With mmatch should be the same *)
(* Example fubar_mmatch (T : Type) (A : T) : M Prop:= *)
(*   mmatch T with *)
(*   | Prop => [H] M.ret (meq_rect Prop (fun T=>T -> Prop) id T (meq_sym H) A) *)
(*   | _ => M.raise exception *)
(*   end. *)

(* Definition fubarType_mmatch := *)
(*   Eval compute in *)
(*   ltac:(mrun (mtry fubar_mmatch Type (True <-> True) with _ => M.ret True end)%MC). *)

(** the bind overloaded notation was reducing terms using typeclasses. destcase expects a match, but it finds false *)
Definition destcase_fail := ltac:(mrun (r <- M.ret (match 3 with 0 => true | _ => false end); _ <- M.destcase r; M.ret I)%MC).

(** with the bind construct it works. this proves that the <- ; notation is reducing *)
Definition destcase_work := ltac:(mrun (M.bind (M.destcase (match 3 with 0 => true | _ => false end)) (fun _=> M.ret I))).





(* Regression test for a bug in `T.bind` where goals were filtered after both tactics were executed instead of filtering after the first tactic. *)
(* Force a solved goal to be returned. *)
Definition faulty_exact {A} (x : A) : tactic := fun g =>
  (match g with
   | Metavar _ _ g' =>
     M.cumul UniCoq x g';; M.ret [m: (m: tt, AnyMetavar _ _ g')]
  end)%MC.
Goal True /\ 1=1.
MProof.
(* Work around previous bad behavior to force the left-hand side of the outermost bind operator to produce unsolved goals. *)
(fun g =>
   r<- M.map (fun '(m: x,g') => open_and_apply ((faulty_exact) I) g') =<< apply conj g;
   M.ret (mconcat r)
)%MC &> (fun g : goal gs_open =>
           (is_open g >>= M.print_term);;
           M.print_term g;; reflexivity g)%MC.
Qed.
