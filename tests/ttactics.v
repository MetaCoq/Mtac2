From Mtac2 Require Import Mtac2 Ttactics.


From Coq Require Import String.

(* Mtac Do (do_def "tt_lt_trans" (@PeanoNat.Nat.lt_trans)). *)
(* Check tt_lt_trans. *)

(* Arguments tt_lt_trans {_ _ _}. *)

(* (** Example: transitivity *) *)
(* Definition trans {x y z: nat} : M ((x < z) * (z < y) =m> x < y) := *)
(*   tg1 <- evar _; *)
(*   tg2 <- evar _; *)
(*   ret ((tg1, tg2), PeanoNat.Nat.lt_trans _ _ _ tg1 tg2). *)
(* Import TT. *)
(* Import TT.notations. *)

(* Goal 1 < 3 -> 3 < 4 -> 1 < 4. *)
(* MProof. *)
(*   intros. *)
(*   compl tt_lt_trans [t: tassumption | tassumption ]. *)
(* Qed. *)

(* Goal 1 < 3 -> 3 < 4 -> 1 < 4. *)
(* MProof. *)
(*   intros. *)
(*   compl tt_lt_trans [t: Muse T.assumption |  assumption]. *)
(* Qed. *)

(* Goal 1 < 3 -> 3 < 4 -> 1 < 4. *)
(* MProof. *)
(*   intros. *)
(*   to_tactic tt_lt_trans &> T.try T.assumption. *)
(* Qed. *)

Import TT.notations.


(* The following test case tries to establish that the proof term of
[test_vm_compute] matches [id (_ <: _)]. It could really benefit from a
[constr_eq] primitive. The reason we test this is that we need to be careful
about [CClosure] operations accidentally removing the cast.

It also serves as a test case for typed tactics where it is often necessary to
have [vm_compute] calls. *)
Definition test_vm_compute : True.
  mrun (TT.apply id <**> TT.vm_compute <**> TT.apply I >>= TT.to_T)%tactic.
Defined.
Mtac Do (
       let t := reduce (RedOneStep [rl: RedDelta]) (test_vm_compute) in
       M.decompose_app'' t (fun A B f a =>
                              M.decompose_app'' f (fun C D g b =>
                                                    mmatch existT id C b return M unit with
                                                  | [? X (Q : X -> Prop) b] existT id (forall x, Q x) b =u>
                                                  \nu x : X, let bx := reduce (RedOneStep [rl: RedBeta]) (b x) in
                                                             k <- M.kind_of_term bx;
                                                             match k with
                                                             | tmCast => M.ret tt
                                                             | _ => M.failwith "Cast disappeared."
                                                             end
                                                   end
                                                  ) : M (unit)
                           )
                            (* M.unify_or_fail UniMatchNoRed t (id (fun a : True => a <: True) I) *)
     )%MC.


(* Testing the *type* of the goal in [match_goal] for the absence of [S.selem_of] and other unwanted wrappers. *)
Module SelemOf.
  Import TT.
  Definition test_Type := (
        match_goal with | [[?P |- P]] =>
          mmatch P return M (P *m _) with
          | unit =n> TT.idtac : M _
          | _ => mfail "[P] not forwarded as exactly [P] to [match_goal] branch"
          end
        end)%MC%TT.
  Definition test_Prop := (
        match_goal with | [[?P : Prop |- P]] =>
          mmatch P return M (P *m _) with
          | True =n> TT.idtac : M _
          | _ => mfail "[P] not forwarded as exactly [P] to [match_goal] branch"
          end
        end)%MC%TT.
  Goal unit.
    mrun test_Type.
  Abort.
  Goal True.
    mrun test_Prop.
  Abort.
End SelemOf.
