(** * Tutorial for Mtac2 *)
(** Author: Beta Ziliani *)
(** with fixes from Michael Soegtrop *)

(** * Introduction

Mtac2 is a typechecked language for proof automation. In its core, it
consists of a monadic type [M A] for a type [A], which is interpreted
via a tactic [mrun]. The best way of understanding the type [M A] is
as _maybe_ [A], so, for instance, a function of type [M nat] _may_
return a natural number. It can also fail or loop forever, but it can
never produce a value of a different type (that is, the interpreter is
sound). We call functions of type [M A] _Mtactics_, to distinguish
them from the usual tactics provided by Coq. *)

(** One of the key aspects of Mtac2 is that it subsumes Gallina, the
language of Coq, and it inherits from Coq the beta delta iota zeta
reduction rules. This makes programming tactics very pleasant, since
developers only need to learn the new features and their semantics,
since the rest is _exactly the same_. These new features are, among
others:

- Exceptions,
- Unbounded fixpoints,
- Unification,
- Fresh name generation,
- Abstraction of variables.
*)

(** In this tutorial we illustrate these features, building up from
simple examples. In order to execute the code in this file you will
need to install our plugin. For details, follow this link: #<a
href="http://www.mpi-sws.org/~beta/mtac/">Mtac2 home page</a>#
*)

(** * Simple examples *)

(** To begin working with the new language we need to import the [M]
type. *)
Require Import Mtac2.Mtac2.

(** In Mtac2 there are two major modules, in our case we are going to
use the module with basic operators, called also [M]. We import it alongside with its notations: *)
Import M.
Import M.notations.

(** In addition, we import a couple of modules from the standard
library that we are going to use in some examples. *)

Require Import Arith.Arith Arith.Div2.
Require Import Lists.List.
Require Import Strings.String.

Set Implicit Arguments.
Notation "x == y" := (beq_nat x y) (at level 60).

(** We start by showing the standard _unit_ and _bind_ operators,
which in our language are called [ret] (for return) and [bind]. The
language also defines the standard notation [x <- a; b] for
[bind]. This example computes the value [1] by passing the result of
computing [0] to the successor.
*)

Definition produces_a_value :=
  x <- ret 0;
  ret (S x).

(** We check the type of the definition. It has type [M nat]. *)

Check produces_a_value.

(** There are different ways to execute it. The first one is to call
the tactic [mrun]. *)
Definition the_value_tactic : nat.
Proof. mrun produces_a_value. Defined.

Print the_value_tactic.

(** The result should be [the_value = 1 : nat]. As you can see, [mrun
produces_a_value] solved the goal with the result of computing the
code in [produces_a_value]. *)

(** Another option is to use the [MProof] command, which implicitly
appends an [mrun] at each line. *)
Definition the_value_mproof : nat.
MProof. produces_a_value. Defined.

(** Finally, it is also possible to use the Ltac keyword [ltac:] to
execute the tactic. One advantage is that we can bake it into regular
Gallina terms. In our case, this means that we do not need to annotate
the type of the definition. *)
Definition the_value_ltac := ltac:(mrun produces_a_value).

(** Throughout the tutorial we are going to use this last one a lot,
so we better make some nice notation: *)

Notation "! t" := ltac:(mrun t) (at level 200).

(** ** Exceptions *)
(** The monad includes exceptions, like the following silly example
illustrates. [Exception]s are constructed with the constructor
[exception]. In order to make distinguishable exceptions we make them
opaque, sealing the definition with the [Qed] word. *)

Definition AnException : Exception.
  exact exception.
Qed.

(* They can be parametrized as well. *)

Definition MyException (s : string) : Exception.
  exact exception.
Qed.

(** Note how they are equal to [exception], but we can still
differentiate them. *)

Definition test_ex e :=
  mtry raise e
  with
  | AnException => ret ""%string
  | MyException "hello"%string => ret "world"%string
  | [? s] MyException s => ret s
  end.

Definition empty_string := ! test_ex AnException.
Definition world_string := ! test_ex (MyException "hello"%string).
Definition other_string := ! test_ex (MyException "other"%string).

Print empty_string.
Print world_string.
Print other_string.

(** Results should be the empty string, the string "world" and the
string "other" respectively. *)

(** If an exception is not caught, then we get a meaningful error.
The [Fail] command below will show the exception thrown by the code: *)

Fail Check (! raise (MyException "This is printed out"%string) : M nat).
(** (We need to provide a type to the expression because [ltac:]
doesn't like open terms.) *)


(** ** Unbounded fixpoints *)

(** Fixpoints in Coq should terminate to ensure soundness. Checking
termination is hard, so Coq relies on a pretty restrictive syntactic
condition to ensure termination. We allow non-termination in our
language via an unbounded fixpoint, which we call [mfix].
For instance, an endless loop can be written simply as: *)

Definition endless_loop := mfix1 f (n : nat) : M False := f n.

(** In this definition we decided to add the type annotation
[M False], since otherwise it is impossible for the type inference
mechanism to guess the type. It is important to note that the body of
[mfix] should always be of type [M]. *)

(** Uncomment the code below and execute it: it will loop forever! You
will have to interrupt the proof assistant (C-c C-c in Emacs). *)

(**[
Check (! endless_loop 0).
]*)

(** *** Endless loop... Is it still safe? *)

(** The key to understanding why it is perfectly safe to allow for
such effects is to notice that [mrun] is not a function living in the
kernel typechecker of Coq. That is, for [t] of type [M A], [mrun t]
constructs a witness for [A] only if it's safe to do so, but _it
itself is not a witness for [A]_. Take as example the definitions we
constructed so far: we used [mrun] but when we printed them we saw no
[mrun] in their proof terms.

As an exercise, we can try to break soundness of Coq by constructing an
 element of type [False] without any further hypothesis. Take the
 function [endless_loop] above, which has type [nat -> M False]. To
 get an element of type [False] we have to execute it through [mrun] as
 in the commented code. Since it will not terminate, [mrun
 (endless_loop 0)] doesn't produce an offending witness. *)

(** *** Constructing Collatz sequences *)

(** To show the use of this unbounded fixpoint we define a function
computing the #<a
href="http://en.wikipedia.org/wiki/Collatz_conjecture">Collatz
sequence</a>#, which cannot be defined in vanilla Coq since its
termination is a conjecture. *)

(* begin hide *)
Fixpoint is_even n :=
  match n with
    0 => true
  | S n' => negb (is_even n')
  end.
(* end hide *)

Definition collatz :=
  mfix1 f (n : nat) : M (list nat) :=
    let n := rcbv n in
    let rest :=
      if n == 1 then
        ret nil
      else if is_even n then
        f (div2 n)
      else
        f (3 * n + 1)
    in
      s <- rest;
      ret (n :: s).

(** We perform reduction on the natural number *)

(** We try it with the value [6]. *)
Definition the_sequence_6 := ! (collatz 6).

Print the_sequence_6.
(** Result: [(6 :: 3 :: 10 :: 5 :: 16 :: 8 :: 4 :: 2 :: 1 :: nil) : list nat] *)


(** ** Unification match *)

(** Mtac2 provides a powerful construct: the unification
match. Unlike the native Coq pattern matching, the unification match
let us specify any term as a pattern, even patterns containing
variables bound in the context.

For instance, the code below shows a function that searches for an
element in a list. *)

Mtac Do New Exception NotFound.
(** (This is just a handy way of declaring an exception without parameters.) *)

Definition inlist A (x : A) :=
  mfix1 f (s : list A) : M (In x s) :=
    mmatch s as s' return M (In x s') with
    | [? s'] (x :: s') => ret (in_eq _ _)
    | [? y s'] (y :: s') =>
      r <- f s';
      ret (in_cons y _ _ r)
    | _ => raise NotFound
    end.

Check inlist.

(** We also depart from the standard notation for patterns: since they
may now refer to variables in the context, we need to specify a list
of pattern variables, like [[? s']] in the first pattern. All the
variables not included in this list should be bound by the context,
like [x] in the same pattern, which is bound to the argument of the
definition. That is, this pattern matches a list containing the
element [x] in the head.
*)


(** So far we have constructed the proof terms directly, without using
the interactive mode of Coq. We can use any standard tactic ([apply],
[refine], [exact], [set], ...) with [run], although not all of them
are suitable if we want to avoid writing inferable arguments.  For
instance, if we have to prove a goal of the form [In x s] for some
list [s] and some element [x], then we would like to use [mrun (inlist
_ _)], that is, without specifying the arguments. This will help us
build more robust proof scripts, since tomorrow we may replace [x] by
some other element in the list and still get a valid proof script. *)

Example x_in_zyx (x y z : nat) : In x (z :: y :: x :: nil).
Proof.
  mrun (inlist _ _).
Qed.

(** One tricky thing about our nice notation [!] is that it doesn't
work for open terms: *)

Fail Example z_in_xyz (x y z : nat) : In z (x :: y :: z :: nil)
  := ! (inlist _ _).

(** We can still call it with the [ltac:] construct directly: *)
Example z_in_xyz (x y z : nat) : In z (x :: y :: z :: nil)
  := ltac:(mrun (inlist _ _)).

(** An alternative is to use [eval], which is similar to [mrun],
except that it performs the execution of the Mtactic after the type
inference mechanism of Coq has done its job: *)

Example y_in_zyx (x y z : nat) : In y (z :: y :: x :: nil)
  := eval (inlist _ _).

(** Behinds the scene, [eval] uses the typeclass mechanism. As a
drawback, it leaves the tactic code in the proof term: *)
Print y_in_zyx. (** Note the call to [inlist] showing up here. *)

(** *** Interaction with [Program] *)

(** When writing tactics, we can use [Program] to avoid having to
write the proof terms ourselves. As an example, we will extend our
[inlist] function to handle list concatenation in order to handle more
cases and get shorter proof terms. By using [Program], Coq will ask us
to provide (interactively) the proof terms for the cases where there is
a hole ([_]) and it cannot guess what to fill in that hole.
*)

Program
Definition inlist' A (x : A) :=
  mfix1 f (s : list A) : M (In x s) :=
    mmatch s as s' return M (In x s') with
    | [? l r] l ++ r =>
      mtry
        il <- f l;
        ret _
      with _ =>
        ir <- f r;
        ret _
      end
    | [? s'] (x :: s') => ret (in_eq _ _)
    | [? y s'] (y :: s') =>
      r <- f s';
      ret (in_cons y _ _ r)
    | _ => raise NotFound
    end.
Next Obligation.
intros; apply in_or_app; left; assumption.
Qed.
Next Obligation.
intros; apply in_or_app; right; assumption.
Qed.

(** If the list is a concatenation of two lists [l] and [r], we first
try to search for the element on [l] and, if it fails, on [r]. Notice
that the pattern is not a constructor, but the application of the
function [++] to two lists. As mentioned before, we can use _any_ Coq term
as a pattern!  It is important to make this case the first case of the
match, as the unification of the scrutinee with the pattern takes into
account beta delta iota zeta reductions. That is, if the concatenation case were
put third in the match, then the list [(x :: nil) ++ (z :: nil)] will
be matched against the pattern [(x :: s')], by reducing it to [(x :: z
:: nil)]. *)

(** One problem with [Program] is that it tends to generate
unnecessarily big proof terms. *)

Print inlist'.

(** Let's look at the proof terms generated in the obligations and plug
those terms into the holes. *)

Print inlist'_obligation_1.
Print inlist'_obligation_2.

(** The important bits are [in_or_app l r x (or_introl H)] and
[in_or_app l r x (or_intror H)]. We write our function again filling
in the holes with these two terms. *)

Definition inlist'' A (x : A) :=
  mfix1 f (s : list A) : M (In x s) :=
    mmatch s as s' return M (In x s') with
    | [? l r] l ++ r =>
      mtry
        il <- f l;
        ret (in_or_app l r x (or_introl il))
      with _ =>
        ir <- f r;
        ret (in_or_app l r x (or_intror ir))
      end
    | [? s'] (x :: s') => ret (in_eq _ _)
    | [? y s'] (y :: s') =>
      r <- f s';
      ret (in_cons y _ _ r)
    | _ => raise NotFound
    end.

(** Let's prove an example using the three functions just created to
compare the proof terms they generate.
*)

Example ex_inlist (x y z : nat) : In x ((y :: z :: nil)++(x :: z :: nil)).
Proof.
  mrun (inlist _ _).
Qed.

Example ex_inlist' (x y z : nat) : In x ((y :: z :: nil)++(x :: z :: nil)).
Proof.
  mrun (inlist' _ _).
Qed.

Example ex_inlist'' (x y z : nat) : In x ((y :: z :: nil)++(x :: z :: nil)).
Proof.
  mrun (inlist'' _ _).
Qed.

Print ex_inlist.
Print ex_inlist'.
Print ex_inlist''.

(** Inspect the result. The last example has the shortest proof term. *)

(** * A simple tautology prover *)

(** We show by example some useful constructs for dealing with Higher
Order Abstract Syntax (HOAS). As the driving example we will write a
rudimentary tautology prover similar to that found in VeriML [[1]] and
CPDT [[2]]. Compared to VeriML, our approach has the benefit that it
doesn't require any special context treatment, since for us a context is
nothing more than a Coq list. And unlike in the Ltac version
presented in [[2]], we have meaningful types to prevent ourselves from
shooting ourselves in the foot.
*)

(** ** Warming the engine: a simple propositional prover *)

(** We start with a very simple propositional prover. It considers
only three cases:

- The proposition is [True]. In this case, it returns the trivial proof [I].
- The proposition is a conjunction of [p1] and [p2]. In this case, it proves both propositions and returns the introduction form of the conjunction.
- The proposition is a disjunction of [p1] and [p2]. In this case, it tries to prove the proposition [p1], and if it fails it tries to prove the proposition [p2]. The corresponding introduction form of the disjunction is returned.
- In any other case, it raises an exception, since no proof could be found.
*)

Definition simpl_prop_auto :=
  mfix1 f (p : Prop) : M p :=
    mmatch p in Prop as p' return M p' with
    | True => ret I
    | [? p1 p2 ] p1 /\ p2 =>
         r1 <- f p1 ;
         r2 <- f p2 ;
         ret (conj r1 r2)
    | [? p1 p2]  p1 \/ p2 =>
         mtry
           r1 <- f p1 ;
           ret (or_introl r1)
         with _ =>
           r2 <- f p2 ;
           ret (or_intror r2)
         end
    | _ => raise NotFound
    end.

(** Given this definition we can easily discharge the following example. *)
Example ex1 : True /\ (False \/ True).
Proof.
  mrun (simpl_prop_auto _).
Qed.

Print ex1.

(** The proof term is exactly what we would have written by hand:

 [ex1 = conj I (or_intror I)] *)

(** ** Adding a context *)

(** Our previous function is very limited since it cannot prove
tautologies as simple as [P -> P]. To handle implications we need a
list of hypotheses where we can search for a proof of the atom we are
considering. We create a record type containing a proposition and a
witness for the proposition.  *)

Record dyn := Dyn { prop : Prop ; elem : prop }.

(** We will need to search a list of [dyn]s to find a witness for some
proposition. The [search] function below is similar to the [inlist] above,
but keying on the [prop] projector of the record. We have to prepend [Program]
because it calls a more agressive typechecker, otherwise it fails to notice
that the element in the body of the first case should return a [P]. *)

Definition search (P : Prop) :=
  mfix1 f (s:list dyn) : M P :=
    mmatch s with
    | [? (x:P) s'] (Dyn x) :: s' => ret x
    | [? d s'] d :: s' => f s'
    | _ => raise NotFound
    end.

(** The proposition in the [Dyn] constructor is implicit, since it can
be inferred from the element, so we write [Dyn x] instead of [Dyn A
x]. *)

(** The tautology prover takes a context [c] (e.g., a list of [dyn]s)
and a proposition. The first three cases are the same as before.  *)

Definition prop_auto' :=
  mfix2 f (c : list dyn) (p : Prop) : M p :=
    mmatch p in Prop as p' return M p' with
    | True => ret I
    | [? p1 p2 ] p1 /\ p2 =>
         r1 <- f c p1 ;
         r2 <- f c p2 ;
         ret (conj r1 r2)
    | [? p1 p2]  p1 \/ p2 =>
         mtry
           r1 <- f c p1 ;
           ret (or_introl r1)
         with _ =>
           r2 <- f c p2 ;
           ret (or_intror r2)
         end
    | [? (p1 p2 : Prop)] p1 -> p2 =>
          \nu x:p1,
          r <- f (Dyn x :: c) p2;
          abs_fun x r
    | [? p'] p' : Prop => search p' c
    end.


(** Let's look at the new case for handling the implication. We need
 to return an element of type [M (p1 -> p2)], that is, _maybe_ a
 function from [p1] to [p2]. Of course, we cannot simply write

[ret (fun x:p1 => f (Dyn x :: c) p2)]

since this code has type [M (p1 -> M p2)] which is not what we
want. Instead, we use two new operators: [nu] and [abs_fun]. The first one
is analogous to the nu operator in [[3]] and [[4]], but a bit more low-level.
Its type is the following: *)

About nu.

(* That is: [forall {A B}, name -> moption -> (A -> M B) -> M B].  [name] is a
structure to control the naming of the variable to be introduced, and
[moption] is a universe polymorphic [option] type. The effect of
computing [nu n None (fun x=>b)], where [b : T B], is the result of
executing [b], replacing any occurrence of [x] with a fresh
_parameter_ [a] named after [n]. If the execution results in a term
[ret t] for some [t] with [a] not appearing free in it, then the value
[ret t] is used as result for [nu n None (fun x => b)]. Otherwise, a
failure is raised. Intuitively, the idea is that it is safe to execute
the body of a function as long as it doesn't get stuck (i.e., it
shouldn't inspect its argument), and the returning value doesn't
return the argument (i.e., it shouldn't violate the context).

The name can be generated fresh (this is what the notation [\nu]
does); it can be named with a specific name (a string), in which case
it shouldn't have a name clash with other variable in scope; or it can
be generated fresh from a given string (for instance, with "H" it will
generate H0, H1, ...).

[abs_fun] abstracts over parameters created by [nu]. It has type [forall A
P (x : A), P x -> M (forall x, P x)] where [A] and [P] are left
implicit. If [a] is a parameter created by [nu] and [t] is a term with
[a] appearing free in it, then [abs_fun a t] is replaced by [ret (fun
x=>r)], where [r] is [t] with [a] replaced by [x]. That is, [a] is
abstracted from [t].

Coming back to the implication case, we use [nu] to create a parameter
[x] as a witness for [p1]. Then we add it to the list of hypothesis to
prove [p2] and get the result [r], which may refer to [x]. Therefore,
we use [abs_fun x r] to abstract [x] from the result. We encourage the
reader to check that the type of the whole expression returned in the
implication case indeed has type [M (p1 -> p2)].

Finally, we changed the last case of the algorithm: instead of
throwing an error, now we search for a witness for the proposition in
the list using the [search] function defined before.
*)

(** We create a definition to avoid passing the empty list *)
Definition prop_auto {P} :=
  @prop_auto' nil P.

(** We can now easily prove this tautology. *)
Example ex_with_implication (p q : Prop) : p -> q -> p /\ q.
Proof.
  mrun prop_auto.
Qed.

(** Again, the proof term generated is exactly what we would expect
for such a proof. *)

Print ex_with_implication.

(** Result:
[ex_with_implication = fun (p q : Prop) (H : p) (H0 : q) => conj H H0] *)

(** * Getting first order *)

(** We can generalize our algorithm very easily to deal with [forall] and
[exists]. Below is the code, where the first four cases and the last one
are the same as before. *)

Definition tauto' :=
  mfix2 f (c : list dyn) (p : Prop) : M p :=
    mmatch p as p' return M p' with
    | True => ret I
    | [? p1 p2] p1 /\ p2 =>
         r1 <- f c p1 ;
         r2 <- f c p2 ;
         ret (conj r1 r2)
    | [? p1 p2]  p1 \/ p2 =>
         mtry
           r1 <- f c p1 ;
           ret (or_introl r1)
         with _ =>
           r2 <- f c p2 ;
           ret (or_intror r2)
         end
    | [? (p1 p2 : Prop)] p1 -> p2 =>
          \nu x:p1,
          r <- f (Dyn x :: c) p2;
          abs_fun x r
    | [? A (q:A -> Prop)] (forall x:A, q x) =>
          \nu x:A,
          r <- f c (q x);
          abs_fun x r
    | [? A (q:A -> Prop)] (exists x:A, q x) =>
          X <- evar A;
          r <- f c (q X) ;
          b <- is_evar X;
          if b then
            raise NotFound
          else
            ret (ex_intro q X r)
    | [? p'] p':Prop => search p' c
    end.

(** The [forall] case is similar to the implication case from before but taking
into account the following:
- The type of [x] is any type [A], not just [Prop].
- The possible dependency of [x] in [q], the body of the [forall]. This dependency is marked by making [q] a function from [A] to [Prop]. The unification algorithm used to unify the pattern with the proposition [p] will take care of instantiating [q] with a function taking an element of type [A] and returning the body of the [forall].
- The context is not extended.

For the existential case, we create a fresh meta-variable [X] via the
command [evar], which takes a type (in this case [A]) and returns a
new meta-variable of that type. Then, we call the function recursively
with the body [q] of the existential, replacing the argument [x] with
[X]. Hopefully, the result will instantiate [X] and we return this as
the witness for the existential. If not, that is, if [X] is still
an uninstantiated meta-variable, then we raise an error.

As before, we create a definition to avoid passing the empty list:
*)

Definition tauto {P} :=
  @tauto' nil P.

(** Here is an example to test [tauto]: *)
Example ex_first_order (p q : nat -> Prop) :
  forall x, p x -> q x -> exists y, p y /\ q y.
Proof.
  mrun tauto.
Qed.

(** If we cannot instantiate an existential, then an error is thrown. *)
Example ex_fail (p q : nat -> Prop) :
  exists y, p y /\ q y.
Proof.
  Fail mrun tauto.
Abort.

(** Actually, we can omit the check for the existential and let the
user come up with the witness by itself. *)

(** * Delayed execution via [eval] *)

(** We mentioned brefly that with [eval] we can delay the execution of
the Mtactic in order to get arguments from the goal, and that we
must use it with care, as the proof term generated is bigger than with
[mrun]. This said, [eval] is particularly useful when rewriting
procedures returning equalities. Here is an example using boolean
equality of natural numbers. *)

Program Definition eq_nats  :=
  mfix2 f (x : nat) (y : nat) : M (x == y = true) :=
    mmatch (x, y) as xy return M (fst xy == snd xy = true)  with
    | (x, x) => ret _
    | [? x1 x2] (x1 + x2, x2 + x1) =>
      ret _
    end.
Next Obligation.
  symmetry.
  apply beq_nat_refl.
Qed.
Next Obligation.
  rewrite beq_nat_true_iff.
  apply plus_comm.
Qed.
(** Notice how we use the [[H]] notation after the right arrow in the
pattern. The name [H] will be instantiated with a proof of equality of
the scrutinee with the pattern, which we use to apply [inverstion] on
it. Of course, we could (should!) avoid [Program] and write the proof
term directly, but that's unnecessary for illustrating the use of
[eval] with [rewrite], the purpose of the section. *)

(** We call the Mtactic with [eval]: *)
Example plus_S n m : n + m == m + n = true /\ m == m = true /\ n == n = true.
Proof.
  rewrite !(eval (eq_nats _ _)). (** Notice how at each rewrite it picks the right terms. *)
  auto.
Qed.

(** * Where now? *)

(** After seeing the basics of the Mtac2 infrastructure, and until
newer documentation comes, you are invited to see the examples in the
same directory as this tutorial, and the theory files. Mtac2 comes
with a lot of different useful tools. And feel free to ask any
question in the Zulip channel! [[6]] *)


(** * References *)
(** [[1]] VeriML: Typed Computation of Logical Terms inside a Language
with Effects. Antonis Stampoulis and Zhong Shao. In Proc. 2010 ACM
SIGPLAN International Conference on Functional Programming (ICFP'10).

[[2]] http://adam.chlipala.net/cpdt/

[[3]] Aleksandar Nanevski. Meta-programming with names and
necessity. In Proceedings of the seventh ACM SIGPLAN international
conference on Functional programming, ICFP'02, pages 206-217, New
York, NY, USA, 2002. ACM.

[[4]] Carsten Schuermann, Adam Poswolsky, and Jeffrey Sarnat. The
nabla-calculus. functional programming with higher-order encodings. In
Proceedings of the 7th international conference on Typed Lambda
Calculi and Applications, TLCA'05, pages 339-353, Berlin, Heidelberg,
2005. Springer-Verlag.

[[5]] https://math-comp.github.io/mcb/

[[6]] https://coq.zulipchat.com/#narrow/stream/254619-Mtac2
*)
