Require Import Strings.String.
Require Import ssrmatching.ssrmatching.
From Mtac2 Require Export Base.
From Mtac2 Require Import Logic Datatypes List Utils Logic Sorts MTeleMatch.
From Mtac2.tactics Require Export TacticsBase.
Import Sorts.S.
Import M.notations.
Import Mtac2.lib.List.ListNotations.
Import T.

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module T.
Export TacticsBase.T.

(** Exceptions *)
Mtac Do New Exception IntroDifferentType.
Mtac Do New Exception NotAProduct.
Mtac Do New Exception CantFindConstructor.
Mtac Do New Exception ConstructorsStartsFrom1.
Mtac Do New Exception Not1Constructor.
Mtac Do New Exception Not2Constructor.
Mtac Do New Exception NotThatType.
Mtac Do New Exception NoProgress.
Mtac Do New Exception GoalNotExistential.

Definition SomethingNotRight {A} (t : A) : Exception. exact exception. Qed.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Import ProdNotations.

Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Metavar _ _ g => M.inst_cumul_or_fail UniCoq x g;; M.ret [m:]
  end.

Definition eexact {A} (x:A) : tactic := fun g =>
  match g with
  | Metavar _ _ g =>
    M.cumul_or_fail UniCoq x g;;
    l <- M.collect_evars g;
    M.map (fun d => '(Metavar _ _ g) <- M.dyn_to_goal d; M.ret (m: tt, AnyMetavar _ _ g)) l
  end.

(** [intro_base n t] introduces variable or definition named [n]
    in the context and executes [t n].
    Raises [NotAProduct] if the goal is not a product or a let-binding. *)
Definition intro_base {A B} (var : name) (t : A -> gtactic B) : gtactic B := fun g =>
  mmatch g return M (mlist (B *m goal gs_any)) with
  | [? s B (def: B) P e] Metavar s (let x := def in P x) e =n>
    (* normal match will not instantiate meta-variables from the scrutinee, so we do the inification here*)
    eqBA <- M.unify_or_fail UniCoq B A;
    M.nu var (mSome def) (fun x=>
      let Px := reduce (RedWhd [rl:RedBeta]) (P x) in
      e' <- M.sorted_evar _ Px;
      nG <- M.abs_let (P:=P) x def e';
      exact nG g;;
      let x := reduce (RedWhd [rl:RedMatch]) (match eqBA with meq_refl => x end) in
      t x (Metavar s _ e') >>= let_close_goals x)
  | [? (s:Sort) (P:_->s) e] Metavar s (ForAll (fun x:A => P x)) e =u>
    M.nu var mNone (fun x=>
      let Px := reduce (RedWhd [rl:RedBeta]) (P x) in
      e' <- M.sorted_evar _ Px;
      nG <- M.abs_fun (P:=P) x e';
      exact nG g;;
      t x (Metavar s Px e') >>= close_goals x)

  | [? (s:Sort) B (P:_->s) e] Metavar s (ForAll (fun x:A => P x)) e =u>
    mtry M.unify_or_fail UniCoq A B;; M.failwith "intros: impossible"
    with _ => M.raise IntroDifferentType end

  | _ => M.raise NotAProduct
  end.

Definition intro_cont {A B} (t : A -> gtactic B) : gtactic B := fun g=>
  n <- M.get_binder_name t;
  intro_base (TheName n) t g.

(** Given a name of a variable, it introduces it in the context *)
Definition intro_simpl (var : name) : tactic := fun g =>
  A <- M.evar Type;
  intro_base var (fun _ : A => idtac) g.

(** Introduces an anonymous name based on a binder *)
Definition intro_anonymous {A} (T : A) (g : goal gs_open) : M (goal gs_any) :=
  res <- intro_simpl (FreshFrom T) g >>= M.hd;
  M.ret (msnd res).

(** Introduces all hypotheses. Does not fail if there are 0. *)
Definition intros_all : tactic := fun '(Metavar _ _ g) =>
  (mfix1 f (g : goal gs_any) : M (mlist (unit *m goal gs_any)) :=
    open_and_apply (fun g : goal gs_open =>
      match g in goal gs return match gs with gs_any => True | gs_open => M (mlist (unit *m goal gs_any)) end with
      | Metavar s T g' =>
        mtry intro_anonymous T g >>= f with
        | NotAProduct => M.ret [m:(m: tt,AnyMetavar _ _ g')]
        end
      | _ => I                  (* Should not be necessary! *)
      end) g) (AnyMetavar _ _ g).

(** Introduces up to n binders. Throws [NotAProduct] if there
    aren't enough products in the goal.  *)
Definition introsn_cont (cont: tactic) : nat -> tactic := fun n '(Metavar _ _ g) =>
  (mfix2 f (n : nat) (g : goal gs_any) : M (mlist (unit *m goal gs_any)) :=
    open_and_apply (fun g =>
      match n, g with
      | 0, g => cont g
      | S n', Metavar s T _ =>
        intro_anonymous T g >>= f n'
      end) g) n (AnyMetavar _ _ g).
Definition introsn := introsn_cont idtac.

(** Overloaded binding *)
Definition copy_ctx {A} (B : A -> Type) : dyn -> M Type :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? c : A] Dyn c =>
      let Bc := reduce (RedWhd [rl:RedBeta]) (B c) in
      M.ret Bc
    | [? C (D : C -> Type) (c : forall y:C, D y)] Dyn c =>
      M.nu (FreshFrom c) mNone (fun y=>
        r <- rec (Dyn (c y));
        M.abs_prod_type y r)
    | [? C D (c : C->D)] Dyn c =>
      M.nu (FreshFrom c) mNone (fun y=>
        r <- rec (Dyn (c y));
        M.abs_prod_type y r)
    | _ => M.print_term A;; M.raise (SomethingNotRight d)
    end.

(** Generalizes a goal given a certain hypothesis [x]. It does not
    remove [x] from the goal. *)
Definition generalize {A} (x : A) : tactic := fun g =>
  match g with
  | Metavar Typeₛ P _ =>
     aP <- M.abs_prod_type x P; (* aP = (forall x:A, P) *)
     e <- M.remove x (M.evar aP);
     (mtmmatch aP as aP' return aP =m= aP' -> M _ with
     | [? Q : A -> Type] (forall z:A, Q z) =n> fun H =>
        let e' := reduce (RedWhd [rl:RedMatch]) match H in _ =m= Q return Q with meq_refl _ => e end in
        exact (e' x) g;;
        M.ret [m:(m: tt, AnyMetavar Typeₛ _ e)]
     | _ as _catchall => fun _ => M.failwith "generalize"
     end) meq_refl
  | Metavar Propₛ P _ =>
     aP <- M.abs_prod_prop x P; (* aP = (forall x:A, P) *)
     e <- M.remove x (M.evar aP);
     (mtmmatch aP as aP' return @meq Prop aP aP' -> M _ with
     | [? Q : A -> Prop] (forall z:A, Q z) =n> fun H : @meq Prop _ (forall z:A, Q z) =>
        let e' := reduce (RedWhd [rl:RedMatch]) match H in _ =m= Q return Q with meq_refl _ => e end in
        exact (e' x) g;;
        M.ret [m:(m: tt, AnyMetavar Propₛ _ e)]
     | _ as _catchall => fun (H : aP =m= _catchall) => M.failwith "generalize"
     end) meq_refl
  end.

(** Clear hypothesis [x] and continues the execution on [cont] *)
Definition cclear {A B} (x:A) (cont : gtactic B) : gtactic B := fun g=>
  match g with
  | Metavar Propₛ gT _ =>
    '(e,l) <- M.remove x (
      e <- M.evar gT;
      l <- cont (Metavar Propₛ _ e);
      M.ret (e, l));
    exact e g;;
    rem_hyp x l
  | Metavar Typeₛ gT _ =>
    '(e,l) <- M.remove x (
      e <- M.evar gT;
      l <- cont (Metavar Typeₛ _ e);
      M.ret (e, l));
    exact e g;;
    rem_hyp x l
  end.

Definition clear {A} (x : A) : tactic := cclear x idtac.

Definition apply_params_to_constructors (ind_applied : dyn) (i : Ind_dyn) : M (mlist dyn) :=
  let '(mkInd_dyn _ nparams _ l) := i in
  rev_params <-
   (mfix3 go (ind_dyn : _) (acc : _) (n : nat) : M (mlist dyn) :=
      match n with
      | 0 => M.ret acc
      | S n =>
        dcase ind_dyn as ind in
            M.decompose_app''
              (S:=fun _ _ => mlist dyn)
              ind
              (fun A B f a =>
                 go (Dyn f) (Dyn a :m: acc) n
              )
      end
   ) ind_applied mnil (N.to_nat nparams);
  let apply_rev_params := (
        mfix2 go (params : mlist dyn) (c : _) : M (dyn) :=
          match params with
          | [m:] => M.ret c
          | p :m: params =>
            dcase p as P, p in
            mmatch c with
            | [? C c] @Dyn (forall p:P, C p) c =u> go params (Dyn (c p))
            end
          end
      ) in
  M.map (apply_rev_params rev_params) l.


Definition destruct {A : Type} (n : A) : tactic := fun g =>
  let A := reduce (RedWhd [rl:RedBeta]) A in
  b <- M.is_var n;
  ctx <- if b then M.hyps_except n else M.hyps;
  match g in goal gs return match gs with gs_any => True | gs_open => M (mlist (unit *m goal gs_any)) end with
  | Metavar s gT _ =>
    P <- M.Cevar (A->s) ctx;
    let Pn := P n in
    M.unify_or_fail UniCoq Pn gT;;
    '(mkInd_dyn _ _ _ l as i) <- M.constrs A;
    l <- apply_params_to_constructors (Dyn A) i;
    l <- M.map (fun d : dyn =>
      (* a constructor c has type (forall x, ... y, A) and we return
         (forall x, ... y, P (c x .. y)) *)
      t' <- copy_ctx P d;
      e <- M.Cevar t' ctx;
      M.ret (Dyn e)) l;
    let c := {| case_ind := A;
                case_val := n;
                case_return := Dyn P;
                case_branches := l
             |} in
    case <- M.makecase c;
    dcase case as e in exact e g;;
    M.map (fun d => '(Metavar _ _ g) <- M.dyn_to_goal d; M.ret (m: tt, AnyMetavar _ _ g)) l
  | _ => I                      (* This makes no sense. It should not be necessary. *)
  end.

(** Destructs the n-th hypotheses in the goal (counting from 0) *)
Definition destructn (n : nat) : tactic :=
  bind (introsn n) (fun _ g =>
    A <- M.evar Type;
    @intro_base A _ (FreshFromStr "tmp") destruct g).

(** [apply t] applies theorem t to the current goal.
    It generates a subgoal for each hypothesis in the theorem.
    If the hypothesis is introduced by a dependent product (a forall),
    then no subgoal is generated. If it isn't dependent (a ->), then
    it is included in the list of next subgoals. *)
Definition apply {T} (c : T) : tactic := fun g=>
  match g with Metavar s t eg =>
    (mfix1 go (d : dyn) : M (mlist (unit *m goal gs_any)) :=
      dcase d as el in
      (* we don't want to see the S.selem_of term in the user's term, so we reduce it *)
      let ty := dreduce (@S.selem_of) (S.selem_of t) in
      mif @M.cumul _ ty UniCoq el eg then M.ret [m:] else
        mmatch d return M (mlist (unit *m goal gs_any)) with
        | [? (T1 T2 : Prop) f] @Dyn (T1 -> T2) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret ((m: tt, AnyMetavar Propₛ _ e) :m: r)
        | [? (T1 : Prop) (T2 : Type) f] @Dyn (T1 -> T2) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret ((m: tt, AnyMetavar Propₛ _ e) :m: r)
        | [? (T1 T2 : Type) f] @Dyn (T1 -> T2) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret ((m: tt, AnyMetavar Typeₛ _ e) :m: r)
        | [? (T1 : Type) (T2: T1 -> Prop) f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret r
        | [? (T1 : Type) (T2: T1 -> Type) f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret r
        | _ =>
          gT <- M.goal_type g;
          M.raise (CantApply T gT)
        end) (Dyn c)
  end.

Definition apply_ : tactic := fun g =>
  match g with
  | Metavar _ _ gevar =>
    G <- M.goal_type g;
    x <- M.solve_typeclass_or_fail G;
    M.cumul_or_fail UniCoq x gevar;;
    M.ret [m:]
  end.

Definition change (P : Type) : tactic := fun g =>
  gT <- M.goal_type g;
  e <- M.evar P;
  exact e g;;
  M.ret [m:(m: tt, AnyMetavar Typeₛ _ e)].

Definition destruct_all (T : Type) : tactic := fun g=>
  l <- M.filter (fun '(@ahyp Th _ _) =>
    r <- M.unify Th T UniCoq;
    M.ret (option_to_bool r)) =<< M.hyps;
  (fix f (l : mlist Hyp) : tactic :=
    match l with
    | [m:] => idtac
    | ahyp x _ :m: l => bind (destruct x) (fun _ => f l)
    end) l g.

Definition typed_intro (T : Type) : tactic := fun g =>
  U <- M.goal_type g;
  mmatch U with
  | [? P:T->Type] forall x:T, P x =>
    intro_simpl (FreshFrom U) g
  | _ => M.raise NotThatType
  end.

Definition typed_intros (T : Type) : tactic := fun g =>
  (mfix1 f (g : goal gs_open) : M _ :=
    mtry bind (typed_intro T) (fun _ => f) g with
    | NotThatType => idtac g
    end) g.

(** changes a hypothesis H with one of type Q and the same name *)
Definition change_hyp {P Q} (H : P) (newH: Q) : tactic := fun g=>
  match g with
  | Metavar sort gT _ =>
     name <- M.get_binder_name H;
     '(m: gabs, abs) <- M.remove H (M.nu (TheName name) mNone (fun nH: Q=>
       r <- M.evar gT;
       abs <- M.abs_fun nH r;
       gabs <- M.abs_fun nH (AnyMetavar sort _ r);
       M.ret (m: AHyp gabs, abs)));
     exact (abs newH) g;;
     M.ret [m:(m: tt, gabs)]
  end.

Definition cassert_with_base {A B} (name : name) (t : A)
    (cont : A -> gtactic B) : gtactic B := fun g =>
  M.nu name (mSome t) (fun x=>
    match g with
    | Metavar sort gT _ =>
      r <- M.evar gT;
      value <- M.abs_fun x r;
      exact (value t) g;;
      close_goals x =<< cont x (Metavar sort _ r)
    end).

Definition cpose_base {A B} (name : name) (t : A)
    (cont : A -> gtactic B) : gtactic B := fun g =>
  M.nu name (mSome t) (fun x=>
    match g with
    | Metavar sort gT _ =>
      r <- M.evar gT;
      value <- M.abs_let x t r;
      exact value g;;
      let_close_goals x =<< cont x (Metavar sort _ r)
    end).

Definition cpose {A} (t: A) (cont : A -> tactic) : tactic := fun g =>
  cpose_base(FreshFrom cont) t cont g.

(* FIX: seriously need to abstract these set of functions!
   Too much duplication! *)
Definition cassert_base {A} (name : name)
    (cont : A -> tactic) : tactic := fun g =>
  a <- M.evar A; (* [a] will be the goal to solve [A] *)
  M.nu name mNone (fun x =>
    match g with
    | Metavar sort gT _ =>
      gT <- M.goal_type g;
      r <- M.evar gT; (* The new goal now referring to n *)
      value <- M.abs_fun x r;
      exact (value a) g;; (* instantiate the old goal with the new one *)
      v <- cont x (Metavar Typeₛ _ r) >>= close_goals x;
      M.ret ((m: tt,AnyMetavar Typeₛ _ a) :m: v)
    end
  ). (* append the goal for a to the top of the goals *)

Definition cassert {A} (cont : A -> tactic) : tactic := fun g=>
  cassert_base (FreshFrom cont) cont g.

(** [cut U] creates two goals with types [U -> T] and [U], where
    [T] is the type of the current goal. *)
Definition cut (U : Type) : tactic := fun g =>
  match g with
  | Metavar Propₛ T _ =>
    ut <- M.evar (U -> T);
    u <- M.evar U;
    exact (ut u) g;;
    M.ret [m:(m: tt,AnyMetavar Propₛ _ ut)| (m: tt,AnyMetavar Typeₛ _ u)]
  | Metavar Typeₛ T _ =>
    ut <- M.evar (U -> T);
    u <- M.evar U;
    exact (ut u) g;;
    M.ret [m:(m: tt,AnyMetavar Typeₛ _ ut)| (m: tt,AnyMetavar Typeₛ _ u)]
  end.

(* performs simpl in each hypothesis and in the goal *)
Definition simpl_in_all : tactic := fun g =>
  l <- M.fold_right (fun (hyp : Hyp) hyps =>
    let (A, x, ot) := hyp in
    let A := rsimpl A in
    M.ret (@ahyp A x ot :m: hyps)
  ) [m:] =<< M.hyps;
  match g with
  | Metavar Propₛ T e' =>
    let T := rsimpl T in
    e <- M.Cevar T l; (* create the new goal in the new context *)
      (* we need normal unification since g might be a compound value *)
    mif M.unify e' e UniMatchNoRed then
      M.ret [m:(m: tt,AnyMetavar Propₛ _ e)]
    else M.failwith "simpl_in_all: Prop"
  | Metavar Typeₛ T e' =>
    let T := rsimpl T in
    e <- M.Cevar T l; (* create the new goal in the new context *)
      (* we need normal unification since g might be a compound value *)
    mif M.unify e' e UniMatchNoRed then
      M.ret [m:(m: tt,AnyMetavar Typeₛ _ e)]
    else M.failwith "simpl_in_all: Type"
  end.

Definition reduce_in (r : Reduction) {P} (H : P) : tactic := fun g =>
  let P' := reduce r P in
  M.replace (A:=P) (B:=P') H meq_refl (
    match g with
    | Metavar Typeₛ gT _ =>
      e <- M.evar gT;
      oeq <- M.unify (Metavar Typeₛ _ e) g UniCoq;
      match oeq with
      | mSome _ => M.ret [m:(m: tt, HypReplace (A:=P) (B:=P') H meq_refl (AnyMetavar Typeₛ _ e))]
      | _ => M.failwith "reduce_in: impossible"
      end
    | Metavar Propₛ gT _ =>
      e <- M.evar gT;
      oeq <- M.unify (Metavar Propₛ _ e) g UniCoq;
      match oeq with
      | mSome _ => M.ret [m:(m: tt, HypReplace (A:=P) (B:=P') H meq_refl (AnyMetavar Propₛ _ e))]
      | _ => M.failwith "reduce_in: impossible"
      end
    end).

Definition simpl_in {P} (H : P) : tactic :=
  reduce_in RedSimpl H.

(** exists tactic *)
Definition mexists {A} (x: A) : tactic := fun g =>
  match g with
  | Metavar Typeₛ _ _ =>
    P <- M.evar (A -> Type);
    e <- M.evar _;
    oeq <- M.unify g (Metavar Typeₛ _ (@existT _ P x e)) UniCoq;
    match oeq with
    | mSome _ => M.ret [m:(m: tt,AnyMetavar Typeₛ _ e)]
    | _ => M.raise GoalNotExistential
    end
  | Metavar Propₛ _ _ =>
    P <- M.evar (A -> Prop);
    e <- M.evar _;
    oeq <- M.unify g (Metavar Propₛ _ (@ex_intro _ P x e)) UniCoq;
    match oeq with
    | mSome _ => M.ret [m:(m: tt,AnyMetavar Propₛ _ e)]
    | _ => M.raise GoalNotExistential
    end
  end.

Definition eexists: tactic := fun g=>
  T <- M.evar Type;
  x <- M.evar T;
  l <- mexists x g;
  let res := dreduce (@mapp) (l +m+ [m:(m: tt, AnyMetavar Typeₛ _ x)]) in
  M.ret res.

(** [n_etas n f] takes a function f with type [forall x1, ..., xn, T]
    and returns its eta-expansion: [fun x1, ..., xn=>f x1 .. xn].
    Raises [NotAProduct] if there aren't that many absractions. *)
Definition n_etas (n : nat) {A} (f : A) : M A :=
  (fix loop (n : nat) (d : dynr) : M (typer d) :=
    match n with
    | 0 =>
      (* we remove the wrapper of the element in [d] *)
      M.unfold_projection (elemr d)
    | S n' =>
       mmatch d as d return M (typer d) with
       | [? B (T:B->Type) f] @Dynr (forall x:B, T x) f =>
         ty <- M.unfold_projection (typer d);
         M.nu (FreshFrom ty) mNone (fun x:B =>
           loop n' (Dynr (f x)) >>= M.abs_fun x
         )
       | _ => M.raise NotAProduct
       end
    end) n (Dynr f).

(** [fix_tac f n] is like Coq's [fix] tactic: it generates a fixpoint
    with a new goal as body, containing a variable named [f] with
    the current goal as type. The goal is expected to have at least
    [n] products. *)
Definition fix_tac (f : name) (n : N) : tactic := fun g =>
  gT <- M.goal_type g;
  '(f, new_goal) <- M.nu f mNone (fun f : gT =>
    (* We introduce the recursive definition f and create the new
       goal having it. *)
    new_goal <- M.evar gT;
    (* We need to enclose the body with n-abstractions as
     required by the fix operator. *)
    fixp <- n_etas (N.to_nat n) new_goal;
    fixp <- M.abs_fix f fixp n;
    (* fixp is now the fixpoint with the evar as body *)
    (* The new goal is enclosed with the definition of f *)
    new_goal <- M.abs_fun f (AnyMetavar Typeₛ _ new_goal);
    M.ret (fixp, AHyp new_goal)
  );
  exact f g;;
  M.ret [m:(m: tt,new_goal)].

Definition progress {A} (t : gtactic A) : gtactic A := fun '(Metavar _ _ g) =>
  r <- t (Metavar _ _ g);
  match r with
  | [m:(m: x,g')] =>
    mmatch AnyMetavar _ _ g with
    | g' => M.raise NoProgress
    | _ => M.ret [m:(m: x,g')]
    end
  | _ => M.ret r
  end.

(** [repeat t] applies tactic [t] to the goal several times
    (it should only generate at most 1 subgoal), until no
    changes or no goal is left. *)
Definition repeat (t : tactic) : tactic :=
  fix0 _ (fun rec '(Metavar _ _ g) =>
    r <- filter_goals =<< try t (Metavar _ _ g); (* if it fails, the execution will stop below *)
    match r with
    | [m:(m: _,g')] =>
      mmatch AnyMetavar _ _ g with
      | g' => M.ret [m:(m: tt,AnyMetavar _ _ g)] (* the goal is the exact same, return *)
      | _ => open_and_apply rec g'
      end
    | [m:] => M.ret r
    | l => (* got several goals, recurse on each *)
      gs <- M.map (fun '(m: _ , g) =>open_and_apply rec g) l;
      let res := dreduce (@mconcat, mapp) (mconcat gs) in
      M.ret res
    end).

Definition map_term (f : forall d:dynr, M d.(typer)) : forall d : dynr, M d.(typer) :=
  mfix1 rec (d : dynr) : M d.(typer) :=
    let (ty, el) := d in
    mmatch d as d return M d.(typer) with
    | [? B A (b: B) (a: B -> A)] Dynr (a b) =n>
      d1 <- rec (Dynr a);
      d2 <- rec (Dynr b);
      M.ret (d1 d2)
    | [? B (A: B -> Type) (a: forall x, A x)] Dynr (fun x:B=>a x) =n>
      M.nu (FreshFrom el) mNone (fun x : B =>
        d1 <- rec (Dynr (a x));
        M.abs_fun x d1)
    | [? B (A: B -> Type) a] Dynr (forall x:B, a x) =n>
      M.nu (FreshFrom el) mNone (fun x : B =>
        d1 <- rec (Dynr (a x));
        M.abs_prod_type x d1)
    | [? d'] d' =n> f d'
    end.

Definition unfold_slow {A} (x : A) : tactic := fun g =>
  let def := reduce (RedOneStep [rl:RedDelta]) x in
  match g with
  | Metavar Typeₛ gT _ =>
    gT' <- map_term (fun d =>
                      let (ty, el) := d in
                      mmatch d as d return M d.(typer) with
                      | Dynr x =n> M.ret def
                      | [? A (d': A)] Dynr d' =n> M.ret d'
                      end) (Dynr gT);
    e <- M.evar gT';
    exact e g;;
    M.ret [m:(m: tt,AnyMetavar Typeₛ _ e)]
  | Metavar Propₛ gT _ =>
    gT' <- map_term (fun d =>
                      let (ty, el) := d in
                      mmatch d as d return M d.(typer) with
                      | Dynr x =n> M.ret def
                      | [? A (d': A)] Dynr d' =n> M.ret d'
                      end) (Dynr gT);
    e <- M.evar gT';
    exact e g;;
    M.ret [m:(m: tt,AnyMetavar Propₛ _ e)]
  end.

Definition unfold {A} (x : A) : tactic := fun g =>
  match g with
  | Metavar Typeₛ gT _ =>
    let gT' := dreduce (x) gT in
    ng <- M.evar gT';
    exact ng g;;
    M.ret [m:(m: tt, AnyMetavar Typeₛ _ ng)]
  | Metavar Propₛ gT _ =>
    let gT' := dreduce (x) gT in
    ng <- M.evar gT';
    exact ng g;;
    M.ret [m:(m: tt, AnyMetavar Propₛ _ ng)]
  end.

Definition unfold_in {A B} (x : A) (h : B) : tactic :=
  reduce_in (RedStrong [rl:RedBeta; RedMatch; RedFix; RedDeltaOnly [rl:Dyn x]]) h.

Fixpoint intros_simpl (l : list string) : tactic :=
  match l with
  | nil => idtac
  | n :: l => bind (intro_simpl (TheName n)) (fun _ => intros_simpl l)
  end%list.

Fixpoint name_pattern (l : list (list string)) : mlist tactic :=
  match l with
  | nil => [m:]
  | ns :: l => intros_simpl ns :m: name_pattern l
  end%list.

Module notations.
  Export TacticsBase.T.notations.
  Open Scope tactic_scope.

  (* We need a fresh evar to be able to use intro with ;; *)
  Notation "'intro' x" :=
    (T <- M.evar Type; @intro_cont T _ (fun x=>idtac))
    (at level 40) : tactic_scope.
  Notation "'evar_intro_cont' t" :=
    (T <- M.evar Type; @intro_cont T _ t)
    (at level 40) : tactic_scope.
  Notation "'intros' x .. y" :=
    (evar_intro_cont (fun x=>.. (evar_intro_cont (fun y=>idtac)) ..))
    (at level 0, x binder, y binder, right associativity) : tactic_scope.
  Notation "'intros'" := intros_all : tactic_scope.

  Notation "'cintro' x '{-' t '-}'" :=
    (intro_cont (fun x=>t)) (at level 0, right associativity) : tactic_scope.
  Notation "'cintros' x .. y '{-' t '-}'" :=
    (intro_cont (fun x=>.. (intro_cont (fun y=>t)) ..))
    (at level 0, x binder, y binder, t at next level, right associativity) : tactic_scope.

  Notation "'simpl'" := (treduce RedSimpl) : tactic_scope.
  Notation "'hnf'" := (treduce RedHNF) : tactic_scope.
  Notation "'cbv'" := (treduce RedNF) : tactic_scope.

  Notation "'pose' ( x := t )" :=
    (cpose t (fun x=>idtac)) (at level 40, x at next level) : tactic_scope.
  Notation "'assert' ( x : T )" :=
    (cassert (fun x:T=>idtac)) (at level 40, x at next level) : tactic_scope.

  Notation "t 'asp' n" :=
    (seq_list t (name_pattern n%list)) (at level 40) : tactic_scope.

End notations.

Import notations.
Import TacticsBase.T.notations.

(* Some derived tactics *)

(** Applies reflexivity *)
Definition prim_reflexivity : tactic :=
  apply (@Coq.Init.Logic.eq_refl).

(** Fist introduces the hypotheses and then applies reflexivity *)
Definition reflexivity : tactic :=
  intros_all;; prim_reflexivity.

(** Given a list of dyn's, it applies each of them until one
succeeds. Throws NoProgress if none apply *)
Definition apply_one_of (l : mlist dyn) : tactic :=
  mfold_left (fun a d => dcase d as e in (or a (apply e))) l (T.raise NoProgress).

(** Tries to apply each constructor of the goal type *)
Definition constructor : tactic :=
  '(mkInd_dyn _ _ _ l) <- M.constrs =<< goal_type;
  apply_one_of l.

Definition apply_in {P Q} (c : P -> Q) (H : P) : tactic :=
  change_hyp H (c H).

Definition transitivity {B} (y : B) : tactic :=
  apply (fun x => @Coq.Init.Logic.eq_trans B x y).

Definition symmetry : tactic :=
  apply Coq.Init.Logic.eq_sym.

Definition symmetry_in {T} {x y: T} (H: x = y) : tactic :=
  apply_in (@Coq.Init.Logic.eq_sym _ _ _) H.

Definition exfalso : tactic :=
  apply Coq.Init.Logic.False_ind.

Definition nconstructor (n : nat) : tactic :=
  A <- goal_type;
  match n with
  | 0 => M.raise ConstructorsStartsFrom1
  | S n =>
    '(mkInd_dyn _ _ _ l) <- M.constrs A;
    match mnth_error l n with
    | mSome d => dcase d as x in apply x
    | mNone => raise CantFindConstructor
    end
  end.

Definition split : tactic :=
  A <- goal_type;
  '(mkInd_dyn _ _ _ l) <- M.constrs A;
  match l with
  | [m:_] => nconstructor 1
  | _ => raise Not1Constructor
  end.

Definition left : tactic :=
  A <- goal_type;
  '(mkInd_dyn _ _ _ l) <- M.constrs A;
  match l with
  | d :m: [m: _ ] => dcase d as x in apply x
  | _ => raise Not2Constructor
  end.

Definition right : tactic :=
  A <- goal_type;
  '(mkInd_dyn _ _ _ l) <- M.constrs A;
  match l with
  | _ :m: [m: d] => dcase d as x in apply x
  | _ => raise Not2Constructor
  end.

Definition assumption : tactic :=
  A <- goal_type;
  match_goal with [[ x : A |- A ]] => exact x end.

(** Given a type [T] it searches for a hypothesis with that type and
    executes the [cont]inuation on it.  *)
Definition select (T : Type) : gtactic T :=
  A <- goal_type;
  match_goal with [[ x : T |- A ]] => T.ret x end.

(** generalize with clear *)
Definition cmove_back {A B} (x : A) (cont : gtactic B) : gtactic B :=
  generalize x ;; cclear x cont.
Definition move_back {A} (x: A) := cmove_back x idtac.

Definition first {B} : mlist (gtactic B) -> gtactic B :=
  fix go l : gtactic B :=
    match l with
    | [m:] => T.raise NoProgress
    | x :m: xs => x || go xs
    end.


(** Auxiliar function of [act_on]. It pulls hypotheses until it reaches [x], and
    returns the names of the once used. *)
Definition move_until_aux {A} (x: A) : gtactic (mlist name) :=
  (fix move_until_aux (accu: mlist name) (hyps: mlist Hyp) := \tactic g=>
    match hyps with
    | [m: ] => M.raise NotAVar
    | (ahyp y _ :m: hyps) =>
      mif M.cumul UniMatchNoRed x y then
        ret accu g
      else
        name <- M.pretty_print y;
        cmove_back y (move_until_aux (TheName name :m: accu) hyps) g
      end) [m:] =<< M.hyps.

(** [move_until x] moves back to the goal as many variables as there are below [x] *)
Definition move_until {A} (x: A) : tactic :=
  move_until_aux x;; idtac.

(** [intros_names names] introduces as many variables as names in [names] *)
Fixpoint intros_names (names : mlist name) : tactic :=
  match names with
  | [m:] => idtac
  | name :m: names => T <- M.evar Type; intro_base name (fun x:T=>intros_names names)
  end.

Definition specialize {A B} (f: forall x: A, B x) (x: A) : tactic :=
  mif M.is_var f then
    let Bx := reduce (RedWhd [rl: RedBeta]) (B x) in
    change_hyp (Q:=Bx) f (f x)
  else
    M.raise NotAVar.

End T.
