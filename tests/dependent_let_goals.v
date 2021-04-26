From Mtac2 Require Import Mtac2.
Lemma dep_test1 x y: let m := max x y in @eq (eq (max x y) m) eq_refl eq_refl.
Proof. intros m. reflexivity. Qed.
Lemma dep_test1_M x y: let m := max x y in @eq (eq (max x y) m) eq_refl eq_refl.
MProof. intros m. T.reflexivity. Qed.
