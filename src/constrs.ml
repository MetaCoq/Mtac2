open Ltac_plugin
open EConstr
open Reductionops

let reduce_value = Tacred.compute

let decompose_appvect sigma c =
  match kind sigma c with
  | App (f,cl) -> (f, cl)
  | _ -> (c,[||])

module Constr = struct
  exception Constr_not_found of string
  exception Constr_poly of string

  let mkConstr name = lazy (
    try of_constr @@
      Universes.constr_of_global
        (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)
       | Invalid_argument _ -> raise (Constr_poly name)
  )

  let mkUConstr name sigma env =
    try fresh_global env sigma
          (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)

  let isConstr sigma = fun r c -> eq_constr sigma (Lazy.force r) c

  let isUConstr r sigma env = fun c ->
    eq_constr_nounivs sigma (snd (mkUConstr r sigma env)) c

  let eq_ind i1 i2 = Names.eq_ind (fst i1) (fst i2)
end

module ConstrBuilder = struct
  type t = string

  let from_string (s:string) : t = s

  let build s = Lazy.force (Constr.mkConstr s)
  let build_app s args = mkApp (Lazy.force (Constr.mkConstr s), args)

  let equal sigma s = Constr.isConstr sigma (Constr.mkConstr s)

  let from_coq s (_, sigma) cterm =
    let (head, args) = decompose_appvect sigma cterm in
    if equal sigma s head then Some args else None
end

module UConstrBuilder = struct
  type t = string

  let from_string (s:string) : t = s

  let build_app s sigma env args =
    let (sigma, c) = Constr.mkUConstr s sigma env in
    (sigma, mkApp (c, args))

  let equal = Constr.isUConstr

  let from_coq s (env, sigma) cterm =
    let (head, args) = decompose_appvect sigma cterm in
    if equal s sigma env head then Some args else None
end

module CoqOption = struct
  open ConstrBuilder

  let optionBuilder = from_string "Coq.Init.Datatypes.option"
  let noneBuilder = from_string "Coq.Init.Datatypes.None"
  let someBuilder = from_string "Coq.Init.Datatypes.Some"

  let mkType ty = build_app optionBuilder [|ty|]
  let mkNone ty = build_app noneBuilder [|ty|]
  let mkSome ty t = build_app someBuilder [|ty; t|]

  exception NotAnOption

  let from_coq ctx cterm =
    match from_coq noneBuilder ctx cterm with
    | None ->
        begin match from_coq someBuilder ctx cterm with
        | None -> raise NotAnOption
        | Some args -> Some args.(1)
        end
    | Some _ -> None

  let to_coq ty oterm =
    match oterm with
    | None -> mkNone ty
    | Some t -> mkSome ty t
end

module type ListParams = sig
  val nilname : string
  val consname : string
  val typename : string
end

module type LIST = sig
  val mkNil : types -> constr
  val mkCons : types -> constr -> constr -> constr
  val mkType : types -> types

  exception NotAList of constr

  val from_coq : (Environ.env * Evd.evar_map) -> constr -> constr list

  (** Allows skipping an element in the conversion *)
  exception Skip
  val from_coq_conv : (Environ.env * Evd.evar_map) -> (constr -> 'a) -> constr -> 'a list

  val to_coq : types -> ('a -> constr) -> 'a list -> constr
  val pto_coq : types -> ('a -> Evd.evar_map -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map -> Evd.evar_map * constr
end

module GenericList (LP : ListParams) = struct
  open ConstrBuilder

  let listBuilder = from_string LP.typename
  let nilBuilder  = from_string LP.nilname
  let consBuilder = from_string LP.consname

  let mkType ty = build_app listBuilder [|ty|]
  let mkNil ty = build_app nilBuilder [|ty|]
  let mkCons t x xs = build_app consBuilder [| t ; x ; xs |]

  exception Skip
  exception NotAList of constr
  (** given a list of terms and a convertion function fconv
      it creates a list of elements using the converstion function.
      if fconv raises Skip, that element is not included.
      if the list is ill-formed, an exception NotAList is raised. *)
  let from_coq_conv ctx (fconv : constr -> 'a) cterm =
    let rec fcc cterm =
      match from_coq consBuilder ctx cterm with
      | None ->
          begin match from_coq nilBuilder ctx cterm with
          | None -> raise (NotAList cterm)
          | Some _ -> []
          end
      | Some args ->
          let tail = fcc args.(2) in
          try fconv args.(1) :: tail with Skip -> tail
    in
    fcc cterm

  let from_coq (env, sigma) =
    from_coq_conv (env, sigma) (fun x->x)

  let to_coq ty f l =
    List.fold_right (fun e l -> mkCons ty (f e) l) l (mkNil ty)

  let pto_coq ty f l sigma =
    List.fold_right (fun e (sigma, l) ->
      let sigma, c = f e sigma in
      sigma, mkCons ty c l) l (sigma, mkNil ty)
end

module CoqList = GenericList (struct
    let nilname = "Mtac2.Datatypes.nil"
    let consname = "Mtac2.Datatypes.cons"
    let typename = "Mtac2.Datatypes.list"
  end)

module CoqEq = struct
  open ConstrBuilder

  let eqBuilder = from_string "Coq.Init.Logic.eq"
  let eqReflBuilder = from_string "Coq.Init.Logic.eq_refl"

  let mkType a x y = build_app eqBuilder [|a;x;y|]
  let mkEqRefl a x = build_app eqReflBuilder [|a;x|]
end

module CoqSigT = struct
  open ConstrBuilder

  let existTBuilder = from_string "Coq.Init.Specif.existT"

  let mkAppExistT a p x px = build_app existTBuilder [|a; p; x; px|]
end

module CoqSig = struct
  let rec from_coq (env, sigma) constr =
    (* NOTE: Hightly unsafe *)
    let (_, args) = decompose_appvect sigma (whd_all env sigma constr) in
    args.(1)
end

module CoqNat = struct
  let mkZero = Constr.mkConstr "Coq.Init.Datatypes.O"
  let mkSucc = Constr.mkConstr "Coq.Init.Datatypes.S"

  let isZero sigma = Constr.isConstr sigma mkZero
  let isSucc sigma = Constr.isConstr sigma mkSucc

  let rec to_coq = function
    | 0 -> Lazy.force mkZero
    | n -> mkApp (Lazy.force mkSucc, [| to_coq (pred n) |])

  let from_coq (env, evd) c =
    let rec fc c =
      if isZero evd c then
        0
      else
        let (s, n) = destApp evd c in
        begin
          if isSucc evd s then
            1 + (fc (n.(0)))
          else
            CErrors.user_err Pp.(str "Not a nat")
        end
    in
    let c' = reduce_value env evd c in
    fc c'
end

module CoqPositive = struct
  let xI = Constr.mkConstr "Coq.Numbers.BinNums.xI"
  let xO = Constr.mkConstr "Coq.Numbers.BinNums.xO"
  let xH = Constr.mkConstr "Coq.Numbers.BinNums.xH"

  let isH sigma = Constr.isConstr sigma xH
  let isI sigma = Constr.isConstr sigma xI
  let isO sigma = Constr.isConstr sigma xO

  let from_coq (env, evd) c =
    let rec fc i c =
      if isH evd c then
        1
      else
        let (s, n) = destApp evd c in
        begin
          if isI evd s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO evd s then
            (fc (i+1) (n.(0)))*2
          else
            CErrors.user_err Pp.(str "Not a positive")
        end
    in
    let c' = reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      Lazy.force xH
    else if n mod 2 = 0 then
      mkApp(Lazy.force xO, [|to_coq (n / 2)|])
    else
      mkApp(Lazy.force xI, [|to_coq ((n-1)/2)|])
end

module CoqN = struct
  let tN = Constr.mkConstr "Coq.Numbers.BinNums.N"
  let h0 = Constr.mkConstr "Coq.Numbers.BinNums.N0"
  let hP = Constr.mkConstr "Coq.Numbers.BinNums.Npos"

  let is0 sigma = Constr.isConstr sigma h0
  let isP sigma = Constr.isConstr sigma hP

  exception NotAnN

  let from_coq (env, evd) c =
    let rec fc c =
      if is0 evd c then
        0
      else
        let (s, n) = destApp evd c in
        begin
          if isP evd s then
            CoqPositive.from_coq (env, evd) (n.(0))
          else
            raise NotAnN
        end
    in
    let c' = reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      Lazy.force h0
    else
      mkApp(Lazy.force hP, [|CoqPositive.to_coq n|])
end

module CoqBool = struct
  open ConstrBuilder

  let boolBuilder = from_string "Coq.Init.Datatypes.bool"
  let trueBuilder = from_string "Coq.Init.Datatypes.true"
  let falseBuilder = from_string "Coq.Init.Datatypes.false"

  let mkType = build boolBuilder
  let mkTrue = build trueBuilder
  let mkFalse = build falseBuilder

  exception NotABool

  let to_coq b = if b then mkTrue else mkFalse
  let from_coq sigma c =
    if equal sigma trueBuilder c then true
    else if equal sigma falseBuilder c then false
    else raise NotABool
end

module CoqAscii = struct
  open ConstrBuilder

  let asciiBuilder = from_string "Coq.Strings.Ascii.Ascii"

  let from_coq (_, sigma) c =
    let (h, args) = decompose_appvect sigma c in
    let rec from_bits n =
      if n >= Array.length args then 0
      else (if CoqBool.from_coq sigma args.(n) then 1 else 0) lsl n + from_bits (n+1)
    in
    let n = from_bits 0 in
    String.make 1 (Char.chr n)

  let to_coq c =
    let c = int_of_char c in
    let a = Array.init 8 (fun i->(c lsr i) mod 2 = 1) in
    let a = Array.map CoqBool.to_coq a in
    build_app asciiBuilder a
end

module CoqString = struct
  open ConstrBuilder

  let emptyBuilder = from_string "Coq.Strings.String.EmptyString"
  let stringBuilder = from_string "Coq.Strings.String.String"

  exception NotAString

  let from_coq (env, sigma as ctx) s =
    let rec fc s =
      let (h, args) = decompose_appvect sigma s in
      if equal sigma emptyBuilder h then ""
      else if equal sigma stringBuilder h then
        CoqAscii.from_coq ctx args.(0) ^ fc args.(1)
      else
        raise NotAString
    in
    fc (reduce_value env sigma s)

  let rec to_coq s =
    if String.length s = 0 then
      build emptyBuilder
    else
      build_app stringBuilder [|
        CoqAscii.to_coq s.[0];
        to_coq (String.sub s 1 (String.length s -1))|]
end

module CoqUnit = struct
  open ConstrBuilder

  let unitBuilder = from_string "Coq.Init.Datatypes.unit"
  let ttBuilder = from_string "Coq.Init.Datatypes.tt"

  let mkType = build unitBuilder
  let mkTT = build ttBuilder
end

module MCTactics = struct
  let gTactic = "Mtac2.Tactics.gtactic"

  let mkConstr s =
    let open Nametab in let open Libnames in
    try Universes.constr_of_global (locate (qualid_of_string s))
    with _ -> raise (Constr.Constr_not_found s)

  let mkUConstr s env sigma =
    let open Nametab in let open Libnames in
    try Evd.fresh_global env sigma (locate (qualid_of_string s))
    with _ -> raise (Constr.Constr_not_found s)

  let mkGTactic = mkUConstr gTactic
end

module CoqPair = struct
  open ConstrBuilder

  let pairBuilder = from_string "Coq.Init.Datatypes.pair"

  let mkPair tya tyb a b = build_app pairBuilder [|tya;tyb;a;b|]

  exception NotAPair

  let from_coq ctx cterm =
    match from_coq pairBuilder ctx cterm with
    | None -> raise NotAPair
    | Some args -> (args.(2), args.(3))
end
