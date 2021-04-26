From Mtac2 Require Import Base Logic Datatypes List.

Import M. Import M.notations.

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Structure result A B x t := R { fu : A -> B; pf : t =m= fu x }.
Arguments R [A B x t].


Notation reduce_dyns := (reduce (RedStrong [rl:RedBeta; RedMatch; RedZeta;
           RedDeltaOnly [rl: Dyn elemr; Dyn typer;
                           Dyn case_return; Dyn case_val; Dyn case_branches;
                        Dyn case_ind]])).

Lemma abs_app
  (A : Type) (x : A) (A' : Type) r (t1 : A' -> typer r) (t2 : A') (r1 : result x t1) (r2 : result x t2):
  result x (t1 t2).
Proof.
elim r1. intros f1 p1.
elim r2. intros f2 p2.
rewrite p1, p2.
exact (R (fun y=>f1 y (f2 y)) (meq_refl _)).
Defined.



Lemma match_eq :
   forall A B : Type,
   forall x : A,
   forall (r : dynr) (b : bool) (P Q : typer r),
   result x b ->
   result x P ->
   result x Q ->
   result x (if b then P else Q).
Proof.
intros A B x r b P Q r1 r2 r3.
elim r1; intros f1 b1.
elim r2; intros f2 b2.
elim r3; intros f3 b3.
rewrite b1, b2, b3.
exact (R (fun y=>if (f1 y) then (f2 y) else f3 y) (meq_refl _)).
Defined.

Arguments match_eq [A B x r b P Q].

Definition non_dep_eq {A P Q} (x:A) (P' : result x P) (Q' : result x Q) :
  result x (P -> Q).
Proof.
  case P' as [fuP eqP]. case Q' as [fuQ eqQ].
  rewrite eqP, eqQ.
  refine (R (fun y=>fuP y -> fuQ y) meq_refl).
Defined.

Definition to_dynr (d: dyn) : M dynr := dcase d as e in ret (Dynr e).

Import ProdNotations.
Import Mtac2.lib.List.ListNotations.
Require Import Strings.String.
Definition construct_case A (x: A) (loop: forall r: dynr, M (moption (result x (elemr r)))) C :=
  let 'mkCase _ val retrn branches := C in
  nu (FreshFromStr "v") mNone (fun v=>
    new_val_opt <- loop (Dynr val);
    '(m: some_branch_depends, new_branches) <-
     M.fold_right (
       fun branch '(m: some_branch_depends, new_branches) =>
         b <- to_dynr branch;
         r <- loop b;
         match r with
         | mSome r =>
           let (fub, _) := r in
           let fub := reduce (RedWhd [rl:RedBeta]) (fub v) in
           ret (m: true, Dyn fub :m: new_branches)
         | mNone => ret (m: some_branch_depends, branch :m: new_branches)
         end
     ) (m: false, [m:]) branches;
    let new_val := match new_val_opt with mSome new_val => new_val | mNone => R (fun _ => val) meq_refl end in
    match new_val_opt, some_branch_depends with
    | mSome _, _ | _, true =>
      let (fuv, _) := new_val in
      let fuv := reduce (RedWhd [rl:RedBeta]) (fuv v) in
      let new_case := reduce_dyns {| case_val := fuv; case_return := retrn; case_branches := new_branches |} in
      d <- makecase new_case;
      dcase d as A0, cas in
      func <- abs_fun v cas;
      ret (mSome (@Dyn (A -> A0) func))
    | _,_ => ret mNone
    end
  ).


Notation reduce_all := (reduce (RedStrong [rl:RedBeta; RedMatch; RedZeta;
           RedDeltaOnly [rl: Dyn elemr; Dyn typer; Dyn (@fu);
             Dyn (@abs_app); Dyn (@meq_rect_r); Dyn (@meq_rect); Dyn (@meq_sym); Dyn (@internal_meq_rew_r);
             Dyn (@match_eq); Dyn (@non_dep_eq)]])).

Definition abstract A B (x : A) (t : B) : M (moption _) :=
   mif is_evar x
   then M.ret mNone
   else
     r <-
     (mfix1 loop (r : dynr) : M (moption (result x (elemr r))) :=
     let r := reduce_dyns r in
     let '(Dynr r') := r in
     mif is_evar (r')
     then M.ret mNone
     else
       mmatch r as r' return M (moption (result x (elemr r'))) with
       | Dynr x =c>
         ret (mSome (R (fun x=>x) (meq_refl _)))
       (* | [? b (P:type r) (Q:type r)] Dyn (match b with *)
       (*       | true => P *)
       (*       | false => Q *)
       (*       end) *)
       (*   =u> *)
       (*   b' <- loop (Dyn b); *)
       (*   P' <- loop (Dyn P); *)
       (*   Q' <- loop (Dyn Q); *)
       (*   ret (match_eq B b' P' Q') *)
       | [? P Q] Dynr (P -> Q) =n>
         P' <- loop (Dynr P);
         Q' <- loop (Dynr Q);
         match P', Q' with
         | mSome P', mSome Q' => ret (mSome (non_dep_eq P' Q'))
         | mSome P', mNone    => ret (mSome (non_dep_eq P' (R (fun _ => Q) meq_refl)))
         | mNone,    mSome Q' => ret (mSome (non_dep_eq (R (fun _ => P) meq_refl) Q'))
         | mNone,    mNone    => ret mNone
         end
       | _ as r =>
          let r' := dreduce (typer) (typer r) in
          mmatch r as r' return M (moption (result x (elemr r'))) with
          | [? A' (t1 : A' -> r') t2] Dynr (t1 t2)  =n>
            r1 <- loop (Dynr t1);
            r2 <- loop (Dynr t2);
              match r1, r2 with
              | mSome r1, mSome r2 => ret (mSome (abs_app r1 r2))
              | mSome r1, mNone    => ret (mSome (abs_app r1 (R (fun _ => t2) meq_refl)))
              | mNone,    mSome r2 => ret (mSome (abs_app (R (fun _ => t1) meq_refl) r2))
              | mNone,    mNone    => ret mNone
              end
          | [? z] z =n>
            let def := R (fun _=>elemr z) (meq_refl) : (result x (elemr z)) in
            mtry
              let '@Dynr T e := z in
              C <- destcase e;
              cas <- construct_case loop C;
              match cas with
              | mSome cas =>
                mmatch cas with
                | [? el: A -> (typer z)] Dyn el =c>
                  eq <- coerce (meq_refl (elemr z));
                  ret (mSome (R (t:=elemr z) el eq))
                | [? e] e => print "nope:";; print_term e;; ret (mNone)
                end
              | mNone => ret mNone
              end
            with NotAMatchExp =>
              ret mNone
            end
          end
       end) (Dynr t);
       let reduced := reduce_all r in
       ret reduced.

Lemma eq_fu (A : Type) (x y : A) (P : Type) (r : result x P) :
  x = y -> fu r y -> P.
Proof. elim r. intros f H1 H2. simpl. rewrite H1, H2. auto. Qed.
