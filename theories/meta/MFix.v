From Mtac2 Require Import Base Logic Datatypes MFixDef MTele MTeleMatch.
Import M.notations.
Import Sorts.S.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Local Definition MFA {n} (T : MTele_Ty n) := (MTele_val (MTele_C Typeₛ Propₛ M T)).

(* Less specific version of MTele_of in MTeleMatch.v *)
Definition MTele_of' :=
  (mfix1 f (T : Prop) : M { m : MTele & { mT : MTele_Ty m & T =m= MFA mT } } :=
     (mtmmatch T as T0 return T =m= T0 -> M { m : MTele & { mT : MTele_Ty m & T =m= MFA mT } } with
     | [?X : Type] M X =u> fun H =>
                        M.ret (existT (fun m => {mT : MTele_Ty m & T =m= MFA mT}) (mBase)
                                      (existT (fun mT : MTele_Ty mBase => T =m= MFA mT) _ H)
                              )
     | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =c> fun H =>
       M.nu (FreshFrom F) mNone (fun x =>
                       '(existT _ m (existT _ mT E)) <- f (F x);
                       m' <- M.abs_fun x m;
                       mT' <- (M.coerce mT >>=
                               M.abs_fun (P:=fun x => MTele_Ty (m' x)) x);
                       (* E' <- (M.abs_fun x E >>= M.coerce (B:=_ =m= MFA mT')); *)
                       E' <- M.coerce (@meq_refl _ (MFA (n:=mTele m') mT'));
                       M.ret (existT _ (mTele m') (existT _ mT' E'))
                       (* mf <- M.abs_fun (P:=fun x => {m : _ & F x =m= MFA m}) x mf; *)
                       (* let g := (fun x => projT1 (mf x)) in *)
                       (* let h := (fun x => projT2 (mf x)) in *)
                       (* e <- M.evar ((forall x, F x) =m= MFA (mTele g)); *)
                       (* er <- M.coerce (meq_refl (forall x, F x)); *)
                       (* M.unify e er UniEvarconv;; *)
                       (* M.ret (existT (fun m => (forall x:X, F x) =m= MFA m) (mTele g) e) *)
                    )
   end) meq_refl
  ).

Definition MTele_of : Prop -> M (sigT MTele_Ty) :=
  mfix1 f (T : Prop) : M (sigT MTele_Ty) :=
     mmatch T return M (sigT MTele_Ty) with
     | [?X : Type] M X =u> M.ret (existT _ mBase X)
     | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =c>
       M.nu (FreshFrom F) mNone (fun x =>
                       '(existT _ n T) <- f (F x);
                       n' <- M.abs_fun (P:=fun _ => MTele) x n;
                       T' <- M.abs_fun x T;
                       T' <- M.coerce T';
                       M.ret (existT _ (mTele n') T')
                    )
   end
.

Class MT_OF (T : Prop) :=
  {
    mt_of_tele : MTele;
    mt_of_type: MTele_Ty mt_of_tele;
    mt_of_eq : T =m= MFA mt_of_type
  }.
(* Arguments mt_of _ {_}. *)
Definition tc_helper (t : Prop)  :=
                                '(existT _ m (existT _ mT eq)) <- MTele_of' t;
                                M.ret (Build_MT_OF _ m mT eq).
Hint Extern 0 (MT_OF ?t) => mrun (tc_helper t
                              ) : typeclass_instances.

Definition mfix_tc' {A : Prop} {mt : MT_OF A} :
  forall (F : (A -> A)),
    A :=
  match meq_sym (@mt_of_eq _ mt) in _ =m= R return (R -> R ) -> (R) with
  | meq_refl => MFixDef.mfix' _
  end.

Arguments mfix_tc' {_} {_} _.

Notation "'mfix' f x .. y : T := b" :=
  (
    @mfix_tc' (forall x, .. (forall y, T) ..) _ (fun f => fun x  => .. (fun y => b)..)
  )
    (only parsing,
     no associativity,
     at level 85,
     f ident,
     x binder,
     y binder,
     format "mfix  f  x  ..  y  :  T  :=  b"
    ).

(* The above notation does not work for printing since [T] cannot be derived
   from an application of `mfix_tc'`. Thus, we define a printing notation that
   omits [T]. *)
Notation "'mfix' f x .. y := b" :=
  (
    mfix_tc' (fun f => fun x  => .. (fun y => b)..)
  )
    (only printing,
     no associativity,
     at level 85,
     f ident,
     x binder,
     y binder,
     format "mfix  f  x  ..  y  :=  b"
    ).
