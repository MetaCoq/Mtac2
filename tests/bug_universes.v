From Mtac2 Require Import Mtac2.

Set Universe Polymorphism.

Set Printing Universes.

(* Demonstrate that id indeed has the right type *)
Definition test@{i j} : Type@{i} -> Type@{max(i,j)} := id.

(* Demonstrate that ltac gets it right *)
Lemma testL@{i j} : Type@{i} -> Type@{max(i,j)}.
Proof. exact id. Qed.

(* M.ret somehow works in 8.8 *)
Lemma testM@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
M.ret id.
Qed.

(* runTac works too *)
Lemma testMTac@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
T.exact id.
Qed.

(* apply doesn't generate a new universe index (it used to be the case) *)
Lemma testMTacApply@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
T.apply (@id).
Qed.

(* and ltac's 8.8  doesn't do that either *)
Lemma testLApply@{i j} : Type@{i} -> Type@{max(i,j)}.
Proof. apply @id. Qed.

Notation "p '=e>' b" := (pbase p%core (b%core) UniEvarconv)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=e>' [ H ] b" := (pbase p%core (b%core) UniEvarconv)
  (no associativity, at level 201, H at next level) : pattern_scope.

Definition test_match@{k m+} {A:Type@{k}} (x:A) : tactic :=
  mmatch A with
  | [? B:Type@{m}] B =c> T.exact x
  end.


Lemma testMmatch@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
test_match (fun x=>x).
Qed.

Lemma testMmatch'@{i j} : Type@{i} -> Type@{j}.
MProof.
test_match (fun x=>x).
Qed.
Print testMmatch.
Print testMmatch'.

Definition testdef : Type -> Type := fun x=>x.
Lemma testret : Type -> Type.
MProof.
M.ret (fun x=>x).
Qed. (* If this fails we likely swapped LHS & RHS of the cumulative unification in [ifM] *)
Print testret.

Lemma testexact : Type -> Type.
MProof.
T.exact (fun x=>x).
Qed.
About testexact.
