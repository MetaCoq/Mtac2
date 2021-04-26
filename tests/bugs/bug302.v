Require Import Mtac2.Mtac2.
Import M.notations.
Import M.

Inductive tFalse : Set.
Definition omg_false (f:tFalse) : Exception. constructor. Qed.

Polymorphic Program Definition test : M unit :=
  a <- evar Type;
  \nu b : a,
  mtry' (
    eqp <- unify_or_fail UniCoq a tFalse;
    replace b eqp (
      (* here b : nat *)
      let b' := rcbv (internal_meq_rew _ a (fun a => a) b tFalse eqp) in
      raise (A:=unit) (omg_false b')
    )
  )
  (fun e =>
     hs <- hyps;
     match hs return M unit with
     | [m: h] =>
       mmatch h return M unit with
       | [#] @ahyp | a' b' o =n>
         mmatch a' return M unit with
         | [#] tFalse | =n>
           mif is_evar a then
             failwith "a is still an evar, but b has its type"
           else print "all good"
         | _ =>
           mif is_evar a then
             failwith (A:=unit) "a is still an evar, but b has its type"
           else
             dbg_term "a' is " a';; failwith (A:=unit) "No idea of what happened!"
         end
       end
     | _ => failwith (A:=unit) "more than one hypothesis?"
     end).

Mtac Do test.
