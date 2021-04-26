From Mtac2 Require Import Mtac2 Ttactics.
Set Printing Universes.

Import Ttactics.TT.
Import TT.notations.

Module Test.
Polymorphic Section With.
  Monomorphic Parameter MyGoal : Prop.
  Polymorphic Parameter MyAssum1@{U1}: forall T1:Type@{U1}, Prop.
  Polymorphic Parameter MyAssum2@{U2}: forall T2:Type@{U2}, Prop.
  Polymorphic Parameter MyProof@{U1 U2+|U1 < U2+} : forall (T1 : Type) (T2 : Type),
      MyAssum1@{U1} T1 -> MyAssum2@{U2} T2 -> MyGoal.

  Set Printing Depth 1000.
  Polymorphic Definition my_tactic@{U1 U2 U1' U2'+} : tactic :=
    Eval cbv beta fix match
           delta
             [
               MatchGoalTT.match_goal_base
                 MatchGoalTT.match_goal_pattern
                 MatchGoalTT.match_goal_pattern'
                 M.mmatch''
                 M.open_branch
                 M.open_pattern
             ] in
    (match_goal with
    | [[? (T1: Type@{U1'}) (T2:Type@{U2'})
        | (H1 : MyAssum1@{U1} T1) (H2 : MyAssum2@{U2} T2) |- MyGoal ]] =>
      TT.apply (MyProof@{U1 U2 U1' U2'} T1 T2 H1 H2)
     end
    )%TT%MC.

  Polymorphic Universe poly U1 U2.

  Parameter T1 : Type@{U1}.
  Parameter T2 : Type@{U2}.

  Polymorphic Example test1 (H1 : MyAssum1@{U1} T1) (H2 : MyAssum2@{U2} T2) : MyGoal.
  Proof.
    mrun (my_tactic).
  Qed. (* <-- there used to be a Fail here :-) *)
End With.
End Test.
