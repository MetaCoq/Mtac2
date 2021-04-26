From Mtac2 Require Import Mtac2 Ttactics Sorts.
From Coq Require Import List.
Import M.notations.
Import M.
Import ListNotations.

(** This file shows different ways to code a simple tautology prover.
    It uses various features of Mtac2 in an example that is easy enough to understand.
*)

Module Mtac_V1.
  (** The first version of the prover will be similar to the one presented in
   the original paper of Mtac.  The prover is an [M] program that encodes in its
   type the fact that it proves the proposition provided as argument. *)


  (** The prover uses a list of [dyn]s as the context of the proof.  We define a
  [lookup] function which traverses the list, trying to unify the type of the
  term with the one provided.  We create a new exception for when it can't find
  the hypothesis. *)
  Mtac Do New Exception NotFound.

  (** Note how we code [lookup] with a standard Coq fixpoint and match. This is for
  performance reasons. *)
  Fixpoint lookup (P : Prop) (l : list dyn) : M P :=
    match l with
    | D :: l => mmatch D with | [? (p : P)] Dyn p =u> ret p | _ => lookup P l end
    |     [] => raise NotFound
    end.

  (** The tautology prover. It first tries to look for the proposition in the
  list of hypothesis, and if it fails in tries to break it down into pieces and
  recurse over each part. *)
  Mtac Do New Exception TautoFail.
  Arguments mcons _ & _ _.      (* TODO: figure out if we should have this everywhere *)
  Definition solve_tauto : forall (l : list dyn) {P : Prop}, M P :=
    mfix2 f (l : list dyn) (P : Prop) : M P :=
      mtry
        lookup P l
      with NotFound =>
        mmatch P in Prop as P' return M P' with
        | True => ret I
        | [? Q1 Q2] Q1 /\ Q2 =>
          q1 <- f l Q1;
          q2 <- f l Q2;
          ret (conj q1 q2)
        | [? Q1 Q2] Q1 \/ Q2 =>
          mtry
            q1 <- f l Q1; ret (or_introl q1)
          with TautoFail =>
            q2 <- f l Q2; ret (or_intror q2)
          end
        | [? (Q1 Q2 : Prop)] Q1 -> Q2 =>
          \nu q1,
            q2 <- f (Dyn q1 :: l) Q2;
            abs_fun q1 q2
        | [? X (Q : X -> Prop)] (exists x : X, Q x) =>
          x <- evar X;
          q <- f l (Q x);
          b <- is_evar x;
          if b then
            raise TautoFail
          else
            ret (ex_intro Q x q)
        | _ => raise TautoFail
        end
      end.

  (** For a detailed explanation, it is best to read the paper and/or look at
  the different primitives that are being used. *)

  Goal 5 = 7 -> exists x, x = 7.
  MProof.
    solve_tauto nil.
  Qed.
End Mtac_V1.


Module Mtac_V2.

  (** The prover in this module uses typed-tactics, mixing static and dynamic
  knowledge of goals to solve the problem. *)
  Import TT.
  Import TT.notations.
  Definition TautoFail : Exception. constructor. Qed.

  Import Tactics.T.notations.

  Program Definition solve_tauto : tactic :=
    mfix0 solve_tauto : gtactic _ :=
    (match_goal with
     | [[ |- True ] ] => ret I
     | [[? Q1 Q2 |- Q1 /\ Q2 ] ] =>
       TT.apply (@conj _ _)
       <**> TT.by' solve_tauto
       <**> TT.by' solve_tauto
     | [[? Q1 Q2 |- Q1 \/ Q2 ] ] =>
       mtry
         TT.apply (@or_introl _ _) <**> TT.by' solve_tauto
       with
       | TautoFail =>
         TT.apply (@or_intror _ _) <**> TT.by' solve_tauto
       end
     | [[? (Q1 Q2 : Prop) |- Q1 -> Q2 ] ] =>
       TT.by' (T.introsn 1 &> solve_tauto)
     | [[? X (Q : X -> Prop) |- (exists x : X, Q x)] ] =>
       TT.by' (T.eexists &> [m: solve_tauto | T.idtac])
     | [[? P | (p : P) |- P ] ] => TT.apply p
     | [[? G |- G ] ] => raise TautoFail
     end
    )%TT%MC.

  Ltac solve_tauto := mrun solve_tauto.

  Goal 5 = 7 -> exists x, x = 7.
  Proof.
    solve_tauto.
  Qed.
End Mtac_V2.


Module Mtac_V3.
  (** The prover in this module uses tactics similar to Ltac's (with similar
  guarantees). *)

  Import T.
  Import T.notations.
  Mtac Do New Exception TautoFail.

  Definition solve_tauto : tactic :=
    mfix0 solve_tauto : gtactic _ :=
      assumption || exact I || (split &> solve_tauto)
      || (left &> solve_tauto) || (right &> solve_tauto)
      || (introsn_cont solve_tauto 1)
      || (eexists |1> solve_tauto) || raise TautoFail.
  Ltac solve_tauto := mrun solve_tauto.

  Goal 5 = 7 -> exists x, x = 7.
  Proof.
    solve_tauto.
  Qed.

End Mtac_V3.


Module Mtac_V4.
  (** The prover in this module uses a combination of the traditional [M]
  solution from [Mtac_V1] with the typed-tactic approach of [Mtac_V2]. *)

  Import Sorts.S.
  Import TT.
  Import TT.notations.
  Definition TautoFail : Exception. constructor. Qed.

  Import M.notations.
  Import ProdNotations.

  Polymorphic Definition promote_uninst_evar {X} {A} (x : X) (a : A *m mlist (goal _)) : ttac (A) :=
    let '(m: a, gs) := a in
    mif is_evar x then ret (m: a, AnyMetavar Typeₛ _ x :m: gs) else ret (m: a, gs).

  Polymorphic Definition has_open_subgoals {A} (a : A *m mlist (goal gs_any)) : M bool :=
    ret (match msnd a with [m:] => true | _ => false end).

  Program Definition solve_tauto : forall {P:Prop}, ttac P :=
    mfix1 solve_tauto (P : Prop) : M _ :=
      mmatch P in Prop as P' return ttac P' with
      | True => apply I
      | [? Q1 Q2] Q1 /\ Q2 =>
        apply (@conj _ _)
          <**> solve_tauto Q1
          <**> solve_tauto Q2
      | [? Q1 Q2] Q1 \/ Q2 =>
        mtry
          q1 <- apply (@or_introl _ _) <**> solve_tauto Q1;
          mif has_open_subgoals q1 then raise TautoFail else ret q1
        with TautoFail =>
          apply (@or_intror _ _) <**> solve_tauto Q2
        end
      | [? (Q1 Q2 : Prop)] Q1 -> Q2 =>
        tintro (fun x:Q1=> solve_tauto Q2)
      | [? X (Q : X -> Prop)] (exists x : X, Q x) =>
        x <- M.evar X;
        q <- apply (@ex_intro _ _ _) <**> solve_tauto (Q x);
        promote_uninst_evar x q
      | _ => TT.use (T.try T.assumption) (* TODO: remove (A:=P) annotation. *)
      end.

 Ltac solve_tauto := mrun solve_tauto.
  Goal 5 = 7 -> exists x, x = 7.
  MProof.
    r <- solve_tauto; M.ret (mfst r).
  Qed.

  Goal exists x, x = 7 -> x = 7.
  MProof.
    lower (solve_tauto &** apply 1).
  Qed.

  Goal exists x : nat, x = x /\ True.
  MProof.
    lower (solve_tauto).
  Abort.

End Mtac_V4.
