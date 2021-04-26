Require Import Strings.String.
From Mtac2 Require Import Base List Exhaustive.
Import M.notations.

Check (mmatch 1 with exhaustively
      | [#] S | n =n> M.print "S"
      | [#] O | =n> M.print "O"
      | _ => M.print "not in constructor normal form"
      end).

(* Test a different order *)
Check (mmatch 1 with exhaustively
      | [#] O | =n> M.print "O"
      | [#] S | n =n> M.print "S"
      | _ => M.print "not in constructor normal form"
      end).

(* Test another order. This one makes no sense but it is exhaustive in the sense
of the checker. *)
Check (mmatch 1 with exhaustively
      | _ => M.print "always triggered first"
      | [#] O | =n> M.print "O, never triggered"
      | [#] S | n =n> M.print "S, never triggered"
      end).

(* Forget a constructor *)
Fail Check (mmatch 1 with exhaustively
      | [#] S | n =n> M.print "S"
      | _ => M.print "not in constructor normal form"
      end).

(* Forget another constructor *)
Fail Check (mmatch 1 with exhaustively
      | [#] O | =n> M.print "O"
      | _ => M.print "not in constructor normal form"
      end).

(* Forget constructor, swap order. *)
Fail Check (mmatch 1 with exhaustively
      | _ => M.print "not in constructor normal form"
      | [#] O | =n> M.print "O"
      end).

(* Check inductive type with parameters. *)
Check (mmatch cons 1 nil with exhaustively
      | [#] @nil _ | =n> M.print "nil"
      | [#] @cons _ | (a : nat) l =n> M.print "cons"
      | _ => M.print "not in constructor normal form"
      end).

(* Check inductive type with parameters which we instantiate with syntactically different but convertible values. *)
Check (mmatch cons 1 nil with exhaustively
      | [#] @nil (id nat) | =n> M.print "nil"
      | [#] @cons nat | a l =n> M.print "cons"
      | _ => M.print "not in constructor normal form"
      end).
