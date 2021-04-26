From Mtac2 Require Import Logic List intf.Unification Sorts MTele Exceptions.
Import Sorts.S.
Import ListNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

(** Pattern matching without pain *)
(* The M will be instantiated with the M monad or the gtactic monad. In principle,
we could make it part of the B, but then higher order unification will fail. *)
Inductive pattern@{a} (A : Type@{a}) (B : A -> Prop) : Prop :=
  | pany : (forall x : A, B x) -> pattern A B
  | pbase : forall x : A, B x -> Unification -> pattern A B
  | ptele : forall {C:Type@{a}}, (forall x : C, pattern A B) -> pattern A B
  | psort : (Sort -> pattern A B) -> pattern A B.


Arguments pany  {A B}   & _.
Arguments pbase {A B}   & _ _ _.
Arguments ptele {A B C} & _.
Arguments psort {A B}   & _.

(* Set Printing Universes. *)
(* Set Printing Implicit. *)
Inductive branch@{a elem_a x+} : forall {A : Type@{a}} {B : A -> Prop}, Prop :=
| branch_pattern {A : Type@{a}} {B : A -> Prop} : pattern A B -> @branch A B
| branch_app_static {A : Type@{a}} {B : A -> Prop} :
    forall {m:MTele@{elem_a}} (uni : Unification) (C : selem_of (MTele_Const@{_ _} (s:=Typeₛ) A m)),
      MTele_sort@{elem_a _ _ a elem_a} (MTele_ConstMap (si := Typeₛ) Propₛ (fun a : A => B a) C) ->
      @branch A B
| branch_forallP {B : Prop -> Prop}:
    (forall (X : Type@{x}) (Y : X -> Prop), B (forall x : X, Y x)) ->
    @branch Prop B
| branch_forallT {B : Type@{elem_a} -> Prop}:
    (forall (X : Type@{elem_a}) (Y : X -> Type@{elem_a}), B (forall x : X, Y x)) ->
    @branch Type@{elem_a} B.
Arguments branch _ _ : clear implicits.
Arguments branch_pattern _ _ &.


(* | branch_app_dynamic {A} {B : forall A, A -> Type} {y}: *)
(*     (forall X (Y : X -> Type) (f : forall x, Y x) (x : X), M (B _ (f x))) -> *)
(*     @branch M _ B A y *)


Declare Custom Entry Mtac2_pattern.

Notation "[¿  s .. t ]  ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (in custom Mtac2_pattern at level 202, s binder, t binder, ps custom Mtac2_pattern, only parsing).
Notation "'[S?'  s .. t ] ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (in custom Mtac2_pattern at level 202, s binder, t binder, ps custom Mtac2_pattern).

Notation "[? x .. y ] ps" :=
  (ptele (fun x => .. (ptele (fun y => ps)).. ))
    (in custom Mtac2_pattern at level 202, x binder, y binder, ps custom Mtac2_pattern at next level,
     only parsing
    ).


Declare Custom Entry Mtac2_unification.
Notation "=m>" := (UniMatch) (in custom Mtac2_unification, only parsing).
Notation "=>" := (UniMatch) (in custom Mtac2_unification).
Notation "=n>" := (UniMatchNoRed) (in custom Mtac2_unification).
Notation "=c>" := (UniEvarconv) (in custom Mtac2_unification).
Notation "=u>" := (UniCoq) (in custom Mtac2_unification).

Notation "p u b" := (pbase p%core b%core u)
  (no associativity, in custom Mtac2_pattern at level 201, p constr, b constr, u custom Mtac2_unification).


(* To get perfect indentation we declare a printing only rule that incorporates
   both evars and base of the pattern *)
Notation "[? x .. y ] p u b" :=
  (ptele (fun x => .. (ptele (fun y => pbase p%core b%core u)).. ))
    (in custom Mtac2_pattern at level 202, x binder, y binder, p constr, b constr, u custom Mtac2_unification,
     only printing,
     format "'[' [?  x  ..  y ]  p  u '/' '['  b ']' ']'"
    ).


Notation "'_'  =>  b " := (pany (fun _ => b%core))
  (in custom Mtac2_pattern at level 201, b constr).
Notation "'_' 'as' catchall => b " := (pany (fun catchall => b%core))
  (in custom Mtac2_pattern at level 201, b constr, catchall binder).

Notation "'[debug_Mtac2_pattern'  p ]" := (p) (p custom Mtac2_pattern at level 1000, only parsing).
Check [debug_Mtac2_pattern [? x : nat] true =u> _].


Declare Custom Entry Mtac2_branch.

Notation "x" := (branch_pattern x) (in custom Mtac2_branch at level 201, x custom Mtac2_pattern).

(* Syntax for decomposition of applications with a known head symbol.

   The [=>] arrows are annotated with the reduction strategy used for the
   initial arguments that are part of the head symbol term [f]. The delimiter
   [|] separates the head symbol term from the arguments, which are binders that
   can be refered to in [b]
*)

Notation "'[#' ] f '|' x .. z '=n>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatchNoRed
     f
     (fun x => .. (fun z => b) ..)
  ) (in custom Mtac2_branch at level 201, f constr, x binder, z binder, b constr).

Notation "'[#' ] f '|' '=n>' b" :=
  (branch_app_static (m := mBase) UniMatchNoRed f b)
    (in custom Mtac2_branch at level 201, f constr, b constr).

Notation "'[#' ] f '|' x .. z '=m>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatch
     f
     (fun x => .. (fun z => b) ..)
  ) (in custom Mtac2_branch at level 201, f constr, x binder, z binder, b constr).

Notation "'[#' ] f '|' '=m>' b" :=
  (branch_app_static (m := mBase) UniMatch f b)
    (in custom Mtac2_branch at level 201, f constr, b constr).

Notation "'[#' ] f '|' x .. z '=u>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniCoq
     f
     (fun x => .. (fun z => b) ..)
  ) (in custom Mtac2_branch at level 201, f constr, x binder, z binder, b constr).

Notation "'[#' ] f '|' '=u>' b" :=
  (branch_app_static (m := mBase) UniCoq f b)
    (in custom Mtac2_branch at level 201, f constr, b constr).

Notation "'[#' ] f '|' x .. z '=c>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniEvarconv
     f
     (fun x => .. (fun z => b) ..)
  ) (in custom Mtac2_branch at level 201, f constr, x binder, z binder, b constr).

Notation "'[#' ] f '|' '=c>' b" :=
  (branch_app_static (m := mBase) UniEvarconv f b)
    (in custom Mtac2_branch at level 201, f constr, b constr).


(* Syntax for decomposition of [forall x : X, P x].

   We define two variants, one for [Prop] and for [Type].
   The initial tokens are [[!Prop]] and [[!Type]] and the remaining
   syntax tries to mirror an actual [forall].
 *)
Notation "'[!Prop' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallP (fun X P => b))
    (in custom Mtac2_branch at level 201, X constr, P constr, b constr).
Notation "'[!Type' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallT (fun X P => b))
    (in custom Mtac2_branch at level 201, X constr, P constr, b constr).

Structure Predicate :=
  PREDICATE {
    predicate_pred : Prop
  }.

Structure Matcher {A} :=
  MATCHER {
    matcher_pred: forall y, Predicate;
    matcher_ret: Prop;
    _ : forall (E: Exception) (ps : mlist (branch A (fun y => predicate_pred (matcher_pred y)))), matcher_ret
  }.
Arguments Matcher {_}.
Arguments MATCHER {_}.

Definition matcher_match {A} (m : Matcher) : forall (E: Exception) (ps : mlist (branch A (fun y => predicate_pred (matcher_pred m y)))), matcher_ret m :=
  ltac:(destruct m as [ ? ? x]; refine x).

Structure InDepMatcher :=
  INDEPMATCHER {
    idmatcher_return : Prop;
    _ : forall A (y : A) (E: Exception) (ps : mlist (branch A (fun _ => idmatcher_return))), idmatcher_return;
  }.

Definition idmatcher_match (m : InDepMatcher) : forall A y (E: Exception) (ps : mlist (branch A (fun _ => idmatcher_return m))), idmatcher_return m :=
  ltac:(destruct m as [ ? x]; refine x).

Definition idmatcher_match_invert (m : InDepMatcher) (A : Type) (y : A) (R : Prop) :
  R =m= idmatcher_return m ->
  forall (_ : Exception) (_ : mlist (branch A (fun _ => R))),
    (* R y =m= matcher_return y m -> *)
    R.
  intros ->. eauto using idmatcher_match. Defined.

Arguments idmatcher_match _ _ _ & _.

Definition matcher_match_invert (A : Type) (y : A) (m : Matcher) (R : A -> Prop) :
  (matcher_ret m =m= R y) ->
  (fun y => predicate_pred (matcher_pred m y)) =m= R ->
  forall (_ : Exception) (_ : mlist (branch A R)),
    (* R y =m= matcher_return y m -> *)
    R y.
  intros <- <-. eauto using matcher_match. Defined.

Arguments matcher_match_invert _ _ _ _ & _ _ _ _ .



Declare Custom Entry Mtac2_with_branch.

Notation "| p1 | .. | pn" :=
  ((@mcons (branch _ _) p1 (.. (@mcons (branch _ _) pn [m:]) ..)))
  (in custom Mtac2_with_branch at level 91,
   p1 custom Mtac2_branch at level 210,
   pn custom Mtac2_branch at level 210,
   format "|  p1 '//' |  .. '//' |  pn"
  ).
Notation "p1 | .. | pn" :=
  ((@mcons (branch _ _) p1 (.. (@mcons (branch _ _) pn [m:]) ..)))
  (in custom Mtac2_with_branch at level 91,
   p1 custom Mtac2_branch at level 210,
   pn custom Mtac2_branch at level 210,
   only parsing
  ).

Notation "'mmatch' x 'with' ls 'end'" :=
  (idmatcher_match _ _ x DoesNotMatch ls)
  (at level 200, ls custom Mtac2_with_branch at level 91,
  format "'mmatch'  x  'with'  '/' ls '/'  'end'").
Notation "'mmatch' x 'return' p 'with' ls 'end'" :=
  (idmatcher_match_invert _ _ x p meq_refl DoesNotMatch ls)
  (at level 200, ls custom Mtac2_with_branch at level 91,
  format "'mmatch'  x  'return'  p  'with'  '/' ls '/'  'end'").
Notation "'mmatch' x 'as' y 'return' p 'with' ls 'end'" :=
  (matcher_match_invert _ x _ (fun y => p%type) meq_refl meq_refl DoesNotMatch ls)
  (at level 200, ls custom Mtac2_with_branch at level 91, y binder,
  format "'mmatch'  x  'as'  y  'return'  p  'with'  '/' ls '/'  'end'").
Notation "'mmatch' x 'in' T 'as' y 'return' p 'with' ls 'end'" :=
  (matcher_match_invert T%type x _ (fun y => p%type) meq_refl meq_refl DoesNotMatch ls)
  (at level 200, ls custom Mtac2_with_branch at level 91, y binder,
  format "'mmatch'  x  'in'  T  'as'  y  'return'  p  'with'  '/' ls '/'  'end'").
