Require Import Coq.Strings.String.
From Mtac2 Require Import Base Logic Datatypes List MFix MTeleMatch.
Import M.notations.
Import Mtac2.lib.List.ListNotations.

Definition funs_of (T : Prop) : mlist Prop -> Prop :=
  fix f l :=
  match l with
  | [m: ] => T
  | X :m: l => X -> f l
  end.
  (* fun T l => fold_right (fun B X => B -> X) T l.  *)

Definition args_of : mlist Prop -> Prop :=
  fix f l :=
  match l with
  | [m: ] => True
  | X :m: l => (X * f l)%type
  end.

Definition apply_args_of {T} : forall {l}, funs_of T l -> args_of l -> T :=
  fix f l :=
  match l as l return funs_of T l -> args_of l -> T with
  | [m: ] => fun t _ => t
  | X :m: l => fun F '(x, a) => f l (F x) a
  end.

(* Compute funs_of (M nat) [m: True | False]. *)

Definition funs_bind {T X : Type} : forall {l},
  (X -> funs_of (M T) l) -> (M X -> funs_of (M T) l) :=
  fix f l :=
    match l return (X -> funs_of _ l) -> (M X -> funs_of _ l) with
    | [m:] => fun g mx => M.bind mx g
    | Y :m: l => fun g mx y => f _ (fun x => g x y) mx
    end.

(* Definition unify_within {T} {X:Prop} (x : X) : *)
(*   forall l, funs_of (M T) [m: X & l] -> funs_of (M T) [m: X & l] := *)
(*   fix f l := *)
(*     match l as l return funs_of _ [m: X & l] -> funs_of _ [m: X & l] with *)
(*     | nil => fun F x' => M.unify x x' UniEvarconv;; F x' *)
(*     | [m: Y & l] => fun F x' y => f l (fun x'' => F x'' y) x' *)
(*     end. *)

(* Eval cbn in unify_within (M.ret 2) [m: ] (fun x => M.ret x). *)
(* Eval cbn in ltac:(mrun ( *)
(*                       x <- M.evar nat; *)
(*                       unify_within (M.ret x) [m: ] (fun _ => M.ret x) (M.ret 2) *)
(*                  )). *)

Record Apply_Args (P T : Type) (t : T) :=
  APPLY_ARGS {
      apply_type: Type;
      apply_func: apply_type;
    }.

Definition remove_ret {V} {B} {Q : B -> Type} {A} : forall (v : V) b (m : Q b), (Q b -> M A) -> M A :=
  fun v b m cont =>
  m' <- M.remove v (M.ret m);
  oe <- M.unify m m' UniMatchNoRed;
  match oe with
  | mNone => M.failwith "Impossible branch."
  | mSome e =>
    match meq_sym e in _ =m= m'' return _ -> M A  with
    | meq_refl =>
      fun cont =>
        cont m'
    end cont
  end
.

Definition apply_type_of (P : Type) :
  forall {T} (t : T),
                      M (sigT (funs_of (M P))) :=
  mfix f (T : _) : T -> M (sigT (funs_of (M P))) :=
     mtmmatch T as T' return T' -> M (sigT (funs_of (M P))) with
     | (M P : Type) =c> fun t => M.ret (existT (funs_of (M P)) [m:] t)
     | [? X F] (forall x : X, F x) =c>
        fun ft =>
          M.nu (FreshFrom ft) mNone (fun x_nu : X =>
          x <- M.evar X;
          let F' := reduce (RedOneStep [rl:RedBeta]) (F x) in
          let f' := reduce (RedOneStep [rl:RedBeta]) (ft x) in
          r <- f F' f';
          mif M.is_evar x then
            o <- M.unify x_nu x UniEvarconv;
            let '(existT _ rl rp) := r in
             rp' <- M.abs_fun x_nu rp;
             mtry (M.remove x_nu (
                   let r' : sigT (funs_of (M P)) := existT _ (M X :m: rl) (funs_bind rp') in
                   M.ret r'
                 )) with
          | [?s] CannotRemoveVar s =>
            let err := (String.append "A hypothesis depends on " s) in
            M.failwith err
         end
       else M.remove x_nu (M.ret r)
       )
  | _ as _catchall => fun _ =>
      M.failwith "The lemma's conclusion does not unify with the goal."
  end
.

(* Notation "'[apply_args_mtac' t 'in' P ]" := *)
(*   ( *)
(*     (* M.print "bla";; *) *)
(*     let t' := t in *)
(*     let P' := P in *)
(*     r <- apply_type_of P' t'; *)
(*     (* M.print_term r;; *) *)
(*     let '(existT _ rl rp) := r in *)
(*     M.ret (APPLY_ARGS P' _ t' _ rp) *)
(*   ). *)

(* Hint Extern 0 (Apply_Args ?P ?T ?t) => *)
(* mrun [apply_args_mtac t in P] : typeclass_instances. *)

(* Goal forall x y : nat, Apply_Args (x =m= x) _ (fun x => test_lemma True x y). *)
(*   intros. *)
(*   mrun [apply_args_mtac (fun x => test_lemma True x y) in x = x]. *)
(* Defined. *)
(* Eval vm_compute in Unnamed_thm. *)

(* Definition bla x y := Eval vm_compute in @apply_func _ _ _ (Unnamed_thm x y). *)
(* (* Notation "'[test' t ]" := (let f := ltac:(mrun t) in ltac:(let e := uconstr:(id f) in exact e)) (at level 0, t at level 11). *) *)

(* Notation "'[static_apply' t 'in' P ]" := *)
(*   ( *)
(*     let t' := t in (* WHY IS THIS NECESSARY? *) *)
(*     let F := M.eval [apply_args_mtac t' in P] in *)
(*     @apply_func _ _ _ F *)
(*   ) (at level 0, P, t at level 11). *)

(* (* Notation "'[bla' t ]" := (let F := ltac:(mrun (M.unify t 1 UniCoq)) in 0 ). *) *)
(* Notation "'[bla' t ]" := (let F := ltac:(let t := open_constr:(t) in unify t 1) in True). *)
(* Fail Goal [bla _]. *)
(* Goal 1=1. *)
(*   mrun ([static_apply (test_lemma _ _ _) in _=_] (M.ret I) (M.evar (1>0))). *)
(* Abort. *)

Notation "t '&s>' '[s' t1 ; .. ; tn ]" :=
  (
    let t' := t in
    let r := M.eval (apply_type_of _ t') in
    let args := M.eval ((* debug true [m:] *) (M.coerce (pair t1 .. (pair tn I) ..))) in
    apply_args_of (projT2 r) args
  ) (at level 41, left associativity,
     format "t  &s>  [s  t1 ;  .. ;  tn ]"
    ).


(* Definition test_lemma (T : Type) (x y : nat) : T -> y > 0 -> M (x =m= x) := *)
(*   fun t H => M.print_term (T, x, y, t, H);; M.ret meq_refl. *)

(* Goal 1=m=1. *)
(*   mrun ((test_lemma _ _ _) &s> [s M.ret I ; M.evar (1>0) ]). *)
(*   auto. *)
(* Qed. *)

(* Goal 1=m=1. *)
(*   mrun ( *)
(*       let f : M(1=1) := *)
(*           (test_lemma _ _ _) &s> [s M.ret I ; M.evar (1>0) ] in *)
(*       M.ret eq_refl). *)
(* Qed. *)
