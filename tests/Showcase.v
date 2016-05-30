Require Import MetaCoq.MCTactics.
Require Import MetaCoq.ImportedTactics.

Require Import Bool.Bool.
Require Import Lists.List.

Import ListNotations.
Import MetaCoqNotations.
Import MCTacticsNotations.

(** This file contains several examples showing the different
    tactics in MetaCoq. Many are taken from SF. *)

(* Basic tactics:
 - intros, cintros (with and without definitions).
 - destruct.
 - left, right.
 - reflexivity.
 - apply.
 - fix. TODO
 - induction. TODO
 - generalize.
 - cut.
 - assert.
 - pose.
*)

Theorem surjective_pairing : forall A B (p : A * B),
  p = (fst p, snd p).
MProof.
  typed_intros Type. destructn 0. intros. reflexivity.
Qed.

Theorem tl_length_pred : forall l: list nat,
  pred (length l) = length (tl l).
MProof.
  destructn 0 ;; [idtac ; intros n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
MProof.
  intros n m p q.
  assert H : (n + m = m + n).
  - rewrite -> PeanoNat.Nat.add_comm;; reflexivity.
  rewrite -> H;; reflexivity.
Qed.