module Uint32 = Wax_utils.Uint32
module Ast = Wax_wasm.Ast
module Binary = Ast.Binary
module Text = Ast.Text
module Simd = Wax_wasm.Simd
module Atomics = Wax_wasm.Atomics
open Wax_lang.Ast
module StringMap = Map.Make (String)

(*** The conversion context ***)

type ctx = {
  globals : (string, unit) Hashtbl.t;
  functions : (string, unit) Hashtbl.t;
  memories : (string, unit) Hashtbl.t;
  tables : (string, reftype) Hashtbl.t;
  elems : (string, unit) Hashtbl.t;
  datas : (string, unit) Hashtbl.t;
  mutable locals : string StringMap.t;
  allocated_locals : (Text.name option * Text.valtype) list ref;
  namespace : Namespace.t;
  type_kinds : (string, [ `Struct | `Array | `Func ]) Hashtbl.t;
  (* The declared continuation types, whose [as]-cast is a compile-time
     ascription lowering to no instruction. *)
  cont_types : (string, unit) Hashtbl.t;
  struct_fields : (string, string list) Hashtbl.t;
  referenced_functions : (string, unit) Hashtbl.t;
  extra_types : (string, Text.name * subtype) Hashtbl.t;
  (* Structurally equal module types, keyed by definition, so an internal
     synthesized type (e.g. [<string>]) can reuse an existing declared one
     (e.g. [bytes = [mut i8]]) instead of being materialized afresh. *)
  reuse_types : (subtype, string) Hashtbl.t;
  types : Wax_lang.Typing.types;
  diagnostics : Wax_utils.Diagnostic.context;
}

(*** Types, indices, and instruction helpers ***)

(* A Text instruction. Its record carries a [hints] field beside the location;
   the hints of the Wax instruction being lowered are attached by [instruction],
   which knows which of the emitted instructions is the operation itself. *)
let with_loc loc desc : _ Text.instr =
  { desc; info = loc; hints = Wax_wasm.Hints.none }

(* Any other located node: an identifier, a module field, an instruction list. *)
let annot loc desc = { Ast.desc; info = loc }

(* Rewrites references to internal synthesized types (names starting with ['<'])
   so they reuse a structurally equal declared type; installed per module by
   [module_]. Other names pass through unchanged. *)
let type_remap : (Text.name -> Text.name) ref = ref Fun.id

let index wax_idx : Text.idx =
  let wax_idx = !type_remap wax_idx in
  annot wax_idx.Ast.info (Text.Id wax_idx.Ast.desc)

(* The spine ([heaptype]/[reftype]/[valtype]/[storagetype]) only rewrites each
   index with [index]; the index carries no extra context, so [ctx] is unit.
   [functype]/[subtype] below stay hand-written to preserve source locations and
   struct-field names. *)
module Map =
  Ast.Map_types_spine (Wax_lang.Ast) (Text)
    (struct
      type ctx = unit

      let idx () i = index i
    end)

let heaptype h = Map.heaptype () h
let valtype ty = Map.valtype () ty
let reftype r = Map.reftype () r
let unpack_type f = match f with Value v -> v | Packed _ -> I32

let is_mgmt_method m =
  match m with "size" | "grow" | "fill" | "copy" | "init" -> true | _ -> false

(* No-argument unary instruction methods written as [x.sqrt()] etc. (not
   [length], which becomes [array.len]). *)
let is_unary_op_method m =
  match m with
  | "clz" | "ctz" | "popcnt" | "extend8_s" | "extend16_s" | "abs" | "ceil"
  | "floor" | "trunc" | "nearest" | "sqrt" | "to_bits" | "from_bits" ->
      true
  | _ -> false

let functype typ : Text.functype =
  let params =
    Array.map
      (fun (p : (_ * _, _) Ast.annotated) ->
        annot p.info (fst p.desc, valtype (snd p.desc)))
      typ.params
  in
  let results = Array.map valtype typ.results in
  { params; results }

let blocktype typ : Text.blocktype option =
  match (typ.params, typ.results) with
  | [||], [||] -> None
  | [||], [| typ |] -> Some (Valtype (valtype typ))
  | _ -> Some (Typeuse (None, Some (functype typ)))

let print_instr i =
  Wax_utils.Printer.run_err (fun pp -> Wax_lang.Output.instr pp i)

(*
let print_storagetype i =
  Wax_utils.Printer.run_err (fun pp -> Wax_lang.Output.storagetype pp i)
*)
let print_valtype i =
  Wax_utils.Printer.run_err (fun pp -> Wax_lang.Output.valtype pp i)

let binop i op operand_type : _ Text.instr_desc =
  match (op, operand_type) with
  | Add, I32 -> BinOp (I32 Add)
  | Sub, I32 -> BinOp (I32 Sub)
  | Mul, I32 -> BinOp (I32 Mul)
  | Div (Some Signed), I32 -> BinOp (I32 (Div Signed))
  | Div (Some Unsigned), I32 -> BinOp (I32 (Div Unsigned))
  | Rem Signed, I32 -> BinOp (I32 (Rem Signed))
  | Rem Unsigned, I32 -> BinOp (I32 (Rem Unsigned))
  | And, I32 -> BinOp (I32 And)
  | Or, I32 -> BinOp (I32 Or)
  | Xor, I32 -> BinOp (I32 Xor)
  | Shl, I32 -> BinOp (I32 Shl)
  | Shr Signed, I32 -> BinOp (I32 (Shr Signed))
  | Shr Unsigned, I32 -> BinOp (I32 (Shr Unsigned))
  | Eq, I32 -> BinOp (I32 Eq)
  | Ne, I32 -> BinOp (I32 Ne)
  | Lt (Some Signed), I32 -> BinOp (I32 (Lt Signed))
  | Lt (Some Unsigned), I32 -> BinOp (I32 (Lt Unsigned))
  | Gt (Some Signed), I32 -> BinOp (I32 (Gt Signed))
  | Gt (Some Unsigned), I32 -> BinOp (I32 (Gt Unsigned))
  | Le (Some Signed), I32 -> BinOp (I32 (Le Signed))
  | Le (Some Unsigned), I32 -> BinOp (I32 (Le Unsigned))
  | Ge (Some Signed), I32 -> BinOp (I32 (Ge Signed))
  | Ge (Some Unsigned), I32 -> BinOp (I32 (Ge Unsigned))
  | Add, I64 -> BinOp (I64 Add)
  | Sub, I64 -> BinOp (I64 Sub)
  | Mul, I64 -> BinOp (I64 Mul)
  | Div (Some Signed), I64 -> BinOp (I64 (Div Signed))
  | Div (Some Unsigned), I64 -> BinOp (I64 (Div Unsigned))
  | Rem Signed, I64 -> BinOp (I64 (Rem Signed))
  | Rem Unsigned, I64 -> BinOp (I64 (Rem Unsigned))
  | And, I64 -> BinOp (I64 And)
  | Or, I64 -> BinOp (I64 Or)
  | Xor, I64 -> BinOp (I64 Xor)
  | Shl, I64 -> BinOp (I64 Shl)
  | Shr Signed, I64 -> BinOp (I64 (Shr Signed))
  | Shr Unsigned, I64 -> BinOp (I64 (Shr Unsigned))
  | Eq, I64 -> BinOp (I64 Eq)
  | Ne, I64 -> BinOp (I64 Ne)
  | Lt (Some Signed), I64 -> BinOp (I64 (Lt Signed))
  | Lt (Some Unsigned), I64 -> BinOp (I64 (Lt Unsigned))
  | Gt (Some Signed), I64 -> BinOp (I64 (Gt Signed))
  | Gt (Some Unsigned), I64 -> BinOp (I64 (Gt Unsigned))
  | Le (Some Signed), I64 -> BinOp (I64 (Le Signed))
  | Le (Some Unsigned), I64 -> BinOp (I64 (Le Unsigned))
  | Ge (Some Signed), I64 -> BinOp (I64 (Ge Signed))
  | Ge (Some Unsigned), I64 -> BinOp (I64 (Ge Unsigned))
  | Add, F32 -> BinOp (F32 Add)
  | Sub, F32 -> BinOp (F32 Sub)
  | Mul, F32 -> BinOp (F32 Mul)
  | Div None, F32 -> BinOp (F32 Div)
  | Eq, F32 -> BinOp (F32 Eq)
  | Ne, F32 -> BinOp (F32 Ne)
  | Lt None, F32 -> BinOp (F32 Lt)
  | Gt None, F32 -> BinOp (F32 Gt)
  | Le None, F32 -> BinOp (F32 Le)
  | Ge None, F32 -> BinOp (F32 Ge)
  | Add, F64 -> BinOp (F64 Add)
  | Sub, F64 -> BinOp (F64 Sub)
  | Mul, F64 -> BinOp (F64 Mul)
  | Div None, F64 -> BinOp (F64 Div)
  | Eq, F64 -> BinOp (F64 Eq)
  | Ne, F64 -> BinOp (F64 Ne)
  | Lt None, F64 -> BinOp (F64 Lt)
  | Gt None, F64 -> BinOp (F64 Gt)
  | Le None, F64 -> BinOp (F64 Le)
  | Ge None, F64 -> BinOp (F64 Ge)
  | _ ->
      print_instr i;
      assert false

let folded loc desc args =
  [ with_loc loc (Text.Folded (with_loc loc desc, args)) ]

let typeuse typ sign =
  let idx = Option.map index typ in
  let type_info =
    Option.map
      (fun s ->
        let params =
          Array.map
            (fun (p : (_, location) Ast.annotated) ->
              annot p.info (param_name p, valtype (param_type p)))
            s.params
        in
        let results = Array.map valtype s.results in
        { Text.params; results })
      sign
  in
  (idx, type_info)

(*** Expression and receiver helpers ***)

(* The type an instruction leaves on the stack. A missing type ([None]) would
   mean a value the type checker never pinned — after successful type checking
   that cannot happen at a site whose translation needs the type: a polymorphic
   value taken off the [Unreachable] stack of dead code is pinned to the type
   that consumes it (see {!Typing.subtype}), and a value with genuinely no
   determinable type is rejected in typing. So [None] here is an internal
   inconsistency, handled like the multi-value case below. *)
let expr_type i =
  match i.info with
  | [| Some t |], _ -> t
  | _ ->
      print_instr i;
      assert false

let expr_opt_valtype i =
  match i.info with
  | [| Some t |], _ -> Some (unpack_type t)
  | [| None |], _ -> None
  | _ ->
      print_instr i;
      assert false

let expr_valtype i = unpack_type (expr_type i)
let expr_reftype i = match expr_valtype i with Ref r -> r | _ -> assert false

(* The reference type of the LAST value [i] produces. A [br_on_cast] tests the
   top of the stack, but its decompiled operand carries all [label_arity] values
   the branch passes on (a [Sequence] when the label arity is >1), so the cast
   value is the last of them — taking the whole expression's [reftype] would
   instead see a multi-value type and assert. [None] if there is no determinable
   trailing reference type (the caller falls back to the cast's target type). *)
let expr_last_opt_reftype i =
  let tys, _ = i.info in
  if Array.length tys = 0 then None
  else
    match tys.(Array.length tys - 1) with
    | Some t -> (
        match unpack_type t with
        (* A bottom heap type ([none]/[nofunc]/… — the type wax gives a polymorphic
           operand, e.g. a hole in dead code after a terminator) is a subtype of
           every reference but a supertype of none, so it cannot serve as the
           [br_on_cast] source type: the emitted [rt2 <: rt1] well-formedness check
           would fail whenever the target [rt2] is in a different hierarchy. Report
           "no determinable source" so the caller falls back to the cast target,
           which is always a valid source ([rt2 <: rt2]). *)
        | Ref { typ = None_ | NoFunc | NoExtern | NoExn | NoCont; _ } -> None
        | Ref r -> Some r
        | _ -> None)
    | None -> None

(* The source reftype [rt1] to emit for a branching cast whose Wax form dropped
   it (the typer recovers it from the operand): the operand's own reftype when
   determinable, else the cast target [rt2]. A bottom-heap operand ([none] /
   [nofunc] / … — a hole in dead code, or a literal [ref.null none]) has no
   usable heap type of its own, so [expr_last_opt_reftype] yields [None] and the
   target stands in; but a *nullable* such operand is not a subtype of the
   non-null target, so carry its nullability over — otherwise the emitted
   [operand <: rt1] check rejects the module. *)
let br_on_cast_source expr target =
  match expr_last_opt_reftype expr with
  | Some r -> r
  | None ->
      let nullable =
        let tys, _ = expr.info in
        Array.length tys > 0
        &&
        match Option.map unpack_type tys.(Array.length tys - 1) with
        | Some (Ref { nullable; _ }) -> nullable
        | _ -> false
      in
      { target with nullable = target.nullable || nullable }

let expr_type_name i =
  match expr_reftype i with
  | { typ = Type idx | Exact idx; _ } -> idx
  | _ ->
      print_valtype (Ref (expr_reftype i));
      print_instr i;
      assert false

(* The target reftype [(ref nullable (exact_1 X))] of a descriptor cast/branch,
   recovered from the descriptor operand [d : (ref null? (exact_1 Y))] with
   [Y describes X]: the described type [X] and the exactness [exact_1] come from
   [d]; only the result [nullable] bit is written in the source. *)
let descriptor_cast_target ctx ~nullable d : reftype =
  let exact = match (expr_reftype d).typ with Exact _ -> true | _ -> false in
  let x =
    match
      Wax_lang.Typing.get_type_definition ctx.diagnostics ctx.types
        (expr_type_name d)
    with
    | Some { describes = Some x; _ } -> x
    | _ -> assert false
  in
  { nullable; typ = (if exact then Exact x else Type x) }

(* Whether the receiver of an [obj.meth(..)] call is an array — the case that
   makes a [fill]/[copy]/[init] method an array operation, as opposed to a
   struct-field/indirect call. Mirrors the type checker and [check_hole_order],
   which also key these on the receiver being an array, so a struct field that
   happens to be named [fill]/[copy]/[init] is lowered as an indirect call. *)
let receiver_is_array ctx i =
  match expr_valtype i with
  (* The abstract array heap type [(ref array)] and the bottom reference
     [(ref none)] (a subtype of [array]) are valid [array.len] receivers.
     [fill]/[copy]/[init] need a concrete element type, so the type checker
     already rejects those on such a receiver — only [length] reaches here. *)
  | Ref { typ = Array | None_; _ } -> true
  (* A named type, resolved through [ctx.types] so synthesized array types (a
     string's [<string>] byte array, used by [s.length()]/[s.copy(..)]) are
     recognized too, not only module-declared ones. *)
  | Ref { typ = Type idx | Exact idx; _ } -> (
      match
        Wax_lang.Typing.get_type_definition ctx.diagnostics ctx.types idx
      with
      | Some { typ = Array _; _ } -> true
      | _ -> false)
  | _ -> false

(* Whether the receiver of a scalar or SIMD intrinsic method ([x.max(y)],
   [x.sqrt()], [x.add_i32x4(b)]) is a value (not a reference): a same-named field
   on a struct has a reference receiver and lowers as an indirect call instead. *)
let receiver_is_value i = match expr_valtype i with Ref _ -> false | _ -> true

(* Whether [s] names a memory (resp. table) usable as a method/index receiver: a
   local of the same name shadows it (Wax resolves a bare name to a local first),
   so the receiver form must defer to the local — mirroring the type checker. *)
let memory_receiver ctx s =
  Hashtbl.mem ctx.memories s && not (StringMap.mem s ctx.locals)

let table_receiver ctx s =
  Hashtbl.mem ctx.tables s && not (StringMap.mem s ctx.locals)

let segment_receiver ctx s =
  (Hashtbl.mem ctx.datas s || Hashtbl.mem ctx.elems s)
  && not (StringMap.mem s ctx.locals)

(* Whether a cast target is a continuation type. [as &k]/[as &?k] is then a
   compile-time ascription — typing accepted it only as a provable no-op, and
   a [ref.cast] to a continuation type is invalid Wasm — so it lowers to the
   operand alone. *)
let cont_cast_target ctx (t : casttype) =
  match t with
  | Valtype (Ref { typ = Cont | NoCont; _ }) -> true
  | Valtype (Ref { typ = Type t | Exact t; _ }) ->
      Hashtbl.mem ctx.cont_types t.desc
  | _ -> false

(*** Labels, control, and memory helpers ***)

(* The branch context threaded down a function body. [return] is the function's
   result label with its current de Bruijn depth, so a branch to it is emitted
   numerically; [labels] is every enclosing label name (innermost first),
   used to pick a fresh readable label for a label-less [while]/[do]-[while]. *)
type ret = { return : (string * int) option; labels : string list }

let no_ret = { return = None; labels = [] }

let label ret (lab : ident) =
  match ret.return with
  | Some (lab', depth) when lab.desc = lab' ->
      { lab with desc = Text.Num (Uint32.of_int depth) }
  | _ -> { lab with desc = Text.Id lab.desc }

let on_clause ret (c : on_clause) : Text.on_clause =
  match c with
  | OnLabel (tag, labl) -> OnLabel (index tag, label ret labl)
  | OnSwitch tag -> OnSwitch (index tag)

let push ret label =
  let return =
    match (ret.return, label) with
    | Some (l, _), Some l' when l = l'.Annot.desc -> None
    | Some (l, i), _ -> Some (l, i + 1)
    | None, _ -> None
  in
  let labels =
    match label with Some l -> l.desc :: ret.labels | None -> ret.labels
  in
  { return; labels }

(* Every block label defined anywhere within [l]. A synthesised loop label must
   avoid these as well as the enclosing labels, so a label-less [while] lowered
   to a [loop] does not shadow a labelled construct nested in its body — e.g. a
   recovered trailing-test [loop] that kept its name (see {!fresh_loop_label}). *)
let labels_in_list l =
  let acc = ref [] in
  let add = function
    | Some (lb : label) -> acc := lb.desc :: !acc
    | None -> ()
  in
  let rec instr (i : _ instr) =
    let opt = Option.iter instr in
    let lst = List.iter instr in
    match i.desc with
    | Block { label; block; _ } | Loop { label; block; _ } ->
        add label;
        lst block.desc
    | While { label; cond; step; block } ->
        add label;
        instr cond;
        opt step;
        lst block.desc
    | If { label; cond; if_block; else_block; _ } ->
        add label;
        instr cond;
        lst if_block.desc;
        Option.iter (fun b -> lst b.Annot.desc) else_block
    | TryTable { label; block; _ } ->
        add label;
        lst block.desc
    | Try { label; block; catches; catch_all; _ } ->
        add label;
        lst block.desc;
        List.iter (fun (_, b) -> lst b.Annot.desc) catches;
        Option.iter (fun b -> lst b.Annot.desc) catch_all
    | TryCatch { label; block; arms; _ } ->
        add label;
        lst block.desc;
        List.iter (fun a -> lst a.arm_body.desc) arms
    | Dispatch { index; arms; _ } ->
        (* Each arm is a labelled block in the lowering, so its label is a
           definition to avoid — [cases]/[default] are branch-target references
           to enclosing labels, not defined here. *)
        instr index;
        List.iter
          (fun (lb, b) ->
            add (Some lb);
            lst b.Annot.desc)
          arms
    | Match { scrutinee; arms; default } ->
        instr scrutinee;
        List.iter (fun (_, b) -> lst b.Annot.desc) arms;
        lst default.desc
    | If_annotation { then_body; else_body; _ } ->
        lst then_body.desc;
        Option.iter (fun b -> lst b.Annot.desc) else_body
    | Call (a, l) | TailCall (a, l) ->
        instr a;
        lst l
    | Struct (_, fs) -> List.iter (fun (_, e) -> opt e) fs
    | StructDesc (d, fs) ->
        List.iter (fun (_, e) -> opt e) fs;
        instr d
    | Set (_, _, e)
    | Tee (_, e)
    | Labelled (_, e)
    | Cast (e, _)
    | Test (e, _)
    | NonNull e
    | StructGet (e, _)
    | GetDescriptor e
    | StructDefaultDesc e
    | ArrayDefault (_, e)
    | UnOp (_, e)
    | ThrowRef e
    | ContNew (_, e) ->
        instr e
    | CastDesc (a, _, b)
    | Br_on_cast_desc_eq (_, _, a, b)
    | Br_on_cast_desc_eq_fail (_, _, a, b)
    | StructSet (a, _, b)
    | Array (_, a, b)
    | ArraySegment (_, _, a, b)
    | ArrayGet (a, b)
    | BinOp (_, a, b) ->
        instr a;
        instr b
    | ArraySet (a, b, c) | Select (a, b, c) ->
        instr a;
        instr b;
        instr c
    | ArrayFixed (_, l)
    | ContBind (_, _, l)
    | Suspend (_, l)
    | Resume (_, _, l)
    | ResumeThrow (_, _, _, l)
    | ResumeThrowRef (_, _, l)
    | Switch (_, _, l)
    | Throw (_, l)
    | Sequence l ->
        lst l
    | Let (_, e) | Return e | Br (_, e) -> opt e
    | Br_if (_, e)
    | On (e, _)
    | Br_table (_, e)
    | Br_on_null (_, e)
    | Br_on_non_null (_, e)
    | Br_on_cast (_, _, e)
    | Br_on_cast_fail (_, _, e) ->
        instr e
    | Unreachable | Nop | Hole | Null | Get _ | Path _ | Char _ | String _
    | Int _ | Float _ | StructDefault _ ->
        ()
  in
  List.iter instr l;
  !acc

(* A readable label for the [loop] a label-less [while] lowers to: [loop], or
   [loop2], [loop3], … when an enclosing label ([avoid] / the function's result
   label included — see {!push}) or a label nested in the body already takes the
   name. *)
let fresh_loop_label ret avoid =
  let rec pick i =
    let n = if i = 1 then "loop" else "loop" ^ string_of_int i in
    if List.mem n ret.labels || List.mem n avoid then pick (i + 1) else n
  in
  pick 1

(* Readable labels for a [match] lowering (see [Ast_utils.lower_match]): one
   [arm]/[arm_1]/[arm_2]/… per arm, in order, then [default] for the escape
   block. Each is bumped with a numeric suffix when an enclosing label, a label
   defined in an arm body ([avoid]), or an already-chosen match label takes the
   name, so neither an arm body's branch to an outer label nor its own labelled
   block is captured. *)
let fresh_match_labels ret ~avoid n =
  let fresh used base =
    let rec pick i =
      let name = if i = 0 then base else base ^ string_of_int i in
      if List.mem name used then pick (i + 1) else name
    in
    pick 0
  in
  let rec arms used i =
    if i >= n then ([], used)
    else
      let base = if i = 0 then "arm" else Printf.sprintf "arm_%d" i in
      let name = fresh used base in
      let rest, used = arms (name :: used) (i + 1) in
      (name :: rest, used)
  in
  let arm_names, used = arms (avoid @ ret.labels) 0 in
  arm_names @ [ fresh used "default" ]

(* Readable labels for a structured-[try] lowering (see
   [Ast_utils.lower_trycatch]): one [catch]/[catch_1]/… per arm, then [join]
   for the outer block when the try has no label of its own. Bumped against
   the enclosing labels (and each other), as for {!fresh_match_labels}. *)
let fresh_trycatch_labels ret ~avoid n =
  let fresh used base =
    let rec pick i =
      let name = if i = 0 then base else base ^ string_of_int i in
      if List.mem name used then pick (i + 1) else name
    in
    pick 0
  in
  let rec arms used i =
    if i >= n then ([], used)
    else
      let base = if i = 0 then "catch" else Printf.sprintf "catch_%d" i in
      let name = fresh used base in
      let rest, used = arms (name :: used) (i + 1) in
      (name :: rest, used)
  in
  let arm_names, used = arms (avoid @ ret.labels) 0 in
  (arm_names, fresh used "join")

(* The per-module [type_remap] (see [index]). A reference to an internal,
   synthesized type (its name starts with ['<']) is rewritten to a structurally
   equal declared type if one is in scope, so a redundant type is not emitted —
   e.g. [<string>] reuses an existing [bytes = [mut i8]]. Otherwise the
   synthesized type is materialized as an extra definition. The synthesized name
   is kept through typing (for error messages) and only switched here.

   [ctx.reuse_types] is scoped — a conditional branch pushes its declared types
   while it is being converted (see [convert_fields]) — so the decision is taken
   afresh at each reference rather than cached: the same synthesized type may
   reuse a conditional type where it is in scope and be materialized elsewhere. *)
let make_type_remap ctx : Text.name -> Text.name =
 fun nm ->
  if nm.desc = "" || nm.desc.[0] <> '<' then nm
  else
    match Wax_lang.Typing.get_type_definition ctx.diagnostics ctx.types nm with
    | None -> nm
    | Some subtype -> (
        match Hashtbl.find_opt ctx.reuse_types subtype with
        | Some existing -> { nm with desc = existing }
        | None ->
            if not (Hashtbl.mem ctx.extra_types nm.desc) then
              Hashtbl.add ctx.extra_types nm.desc (nm, subtype);
            nm)

let mem_store_method = function
  | "store8" | "store16" | "store32" | "store64" | "storef32" | "storef64" ->
      true
  | _ -> false

let mem_load_method = function
  | "load8" | "load16" | "load32" | "load64" | "loadf32" | "loadf64" -> true
  | _ -> false

let is_mem_method m = mem_store_method m || mem_load_method m

let mem_natural_align = function
  | "load8" | "store8" -> 1
  | "load16" | "store16" -> 2
  | "load32" | "store32" | "loadf32" | "storef32" -> 4
  | _ -> 8

(* Split a memory-access call's arguments into the positional stack operands
   and the labelled immediates ([offset]/[align]/[lane]); typing guarantees
   every [Labelled] argument is one of those, with an integer-literal
   payload. *)
let split_labelled args =
  List.partition_map
    (fun a ->
      match a.desc with
      | Labelled (l, e) -> Either.Right (l.desc, e)
      | _ -> Either.Left a)
    args

let int_lit a =
  match a.desc with
  (* [Uint64.of_string] handles the full unsigned 64-bit range; a memory64
     offset/align may exceed [Int64.max_int]. *)
  | Int s -> Wax_utils.Uint64.of_string s
  | _ -> assert false

(* Build a [memarg] from the labelled [align]/[offset] immediates, defaulting
   [align] to the natural alignment. *)
let memarg_of_labels ~natural labels : Ast.memarg =
  {
    align =
      (match List.assoc_opt "align" labels with
      | Some a -> int_lit a
      | None -> Wax_utils.Uint64.of_int natural);
    offset =
      (match List.assoc_opt "offset" labels with
      | Some o -> int_lit o
      | None -> Wax_utils.Uint64.zero);
  }

(* [memarg_of_labels] for a scalar load/store, whose natural (default)
   alignment follows from the method name. *)
let mem_memarg meth args : Ast.memarg =
  memarg_of_labels ~natural:(mem_natural_align meth) (snd (split_labelled args))

(* Resolve the concrete atomic op of a method family: the name carries the
   access width, and a store/RMW picks the i32/i64 op by its (first) value
   operand's type — unknown (unreachable code) defaults to i32, as for the
   plain narrow stores. A narrow load with no resolving cast defaults to the
   zero-extended i32 form, like a bare [load8]; its fused i64 forms are
   produced by the [Cast] case. *)
let atomic_op (family : Atomics.family) stack_args : Ast.atomicop =
  let narrow w t : [ `I32 | `I64 ] * [ `I8 | `I16 | `I32 ] option =
    match w with
    | `W8 -> (t, Some `I8)
    | `W16 -> (t, Some `I16)
    | `W32 -> ( match t with `I64 -> (`I64, Some `I32) | `I32 -> (`I32, None))
    | `W64 -> (`I64, None)
  in
  let value_type () =
    match stack_args with
    | _addr :: v :: _ -> (
        match expr_opt_valtype v with Some I64 -> `I64 | _ -> `I32)
    | _ -> `I32
  in
  match family with
  | Atomics.Notify -> Ast.AtomicNotify
  | Atomics.Wait t -> Ast.AtomicWait t
  | Atomics.Load `W32 -> Ast.AtomicLoad (`I32, None)
  | Atomics.Load `W64 -> Ast.AtomicLoad (`I64, None)
  | Atomics.Load `W8 -> Ast.AtomicLoad (`I32, Some `I8)
  | Atomics.Load `W16 -> Ast.AtomicLoad (`I32, Some `I16)
  | Atomics.Store w ->
      let t, pw = narrow w (value_type ()) in
      Ast.AtomicStore (t, pw)
  | Atomics.Rmw (op, w) ->
      let t, pw = narrow w (value_type ()) in
      Ast.AtomicRmw (op, t, pw)

(* Literal value of a [v128::<shape>] lane argument, as a string for
   [Wax_utils.V128.t]; a negative literal is [UnOp (Neg, _)]. *)
let rec literal_string a =
  match a.desc with
  | Int s | Float s -> s
  | UnOp ({ desc = Neg; _ }, b) -> "-" ^ literal_string b
  | _ -> assert false

(* Read a constant integer immediate (lane index). *)
let lane_imm a =
  match a.desc with Int s -> int_of_string s | _ -> assert false

(* Whether negating the unsigned magnitude [s] yields a value representable as a
   signed [bits]-bit constant, i.e. [s <= 2^(bits-1)]. When it does not (e.g.
   [-18446744073709551615] as i64: the magnitude is a valid *unsigned* const but
   its negation is below the signed minimum), folding [-s] into a single [Const]
   would emit an out-of-range literal that crashes the encoder; the caller must
   instead lower it as [0 - s]. *)
let neg_int_const_fits bits s =
  match
    if String.starts_with ~prefix:"0x" s then Int64.of_string_opt s
    else Int64.of_string_opt ("0u" ^ s)
  with
  | None -> false (* magnitude exceeds u64 *)
  | Some v -> Int64.unsigned_compare v (Int64.shift_left 1L (bits - 1)) <= 0

(*** The instruction converter ***)

(* Lower a struct literal's field values in the type's declared field order.
   [fields] maps names to values; a punned field ([None], written [{x}]) lowers
   as [Get x] of the like-named local/global/function. *)
let rec struct_field_args ret ctx field_names fields =
  let field_map =
    List.fold_left
      (fun acc (name, instr) -> StringMap.add name.Annot.desc (name, instr) acc)
      StringMap.empty fields
  in
  List.concat_map
    (fun fname ->
      match StringMap.find fname field_map with
      | _, Some e -> instruction ret ctx e
      | name, None ->
          instruction ret ctx
            {
              desc = Get name;
              info = ([||], name.Ast.info);
              hints = Wax_wasm.Hints.none;
              expected = Unset;
            })
    field_names

(* Branch-hinting / compilation-hints proposals: carry a Wax instruction's hints
   onto the Wasm instruction it lowers to. A Wax instruction generally lowers to a
   whole stack sequence; the hint belongs on the one instruction that is the
   operation itself — the head of a folded node, or the single instruction — which
   is where the encoder takes its byte offset. Anything else (a multi-instruction
   lowering) has no single carrier, so the hint is dropped: it is advisory. *)
and instruction ret ctx (i : _ Wax_lang.Ast.instr) : location Text.instr list =
  let code = instruction_desc ret ctx i in
  if Wax_wasm.Hints.is_empty i.hints then code
  else
    let hints = Wax_wasm.Hints.map_targets index i.hints in
    match code with
    | [ ({ desc = Text.Folded (d, args); _ } as i') ] ->
        [ { i' with desc = Text.Folded ({ d with hints }, args) } ]
    | [ single ] -> [ { single with Text.hints } ]
    | code -> code

and instruction_desc ret ctx (i : _ Wax_lang.Ast.instr) :
    location Text.instr list =
  let _, loc = i.info in
  match i.desc with
  | Block { label; typ; block = body } ->
      let inner_ctx = { ctx with locals = ctx.locals } in
      let block =
        {
          body with
          Ast.desc =
            List.concat_map (instruction (push ret label) inner_ctx) body.desc;
        }
      in
      folded loc (Block { label; typ = blocktype typ; block }) []
  | Loop { label; typ; block = body } ->
      let inner_ctx = { ctx with locals = ctx.locals } in
      let block =
        {
          body with
          Ast.desc =
            List.concat_map (instruction (push ret label) inner_ctx) body.desc;
        }
      in
      folded loc (Loop { label; typ = blocktype typ; block }) []
  | If { label; typ; cond; if_block; else_block } ->
      let cond_code = instruction ret ctx cond in
      let then_ctx = { ctx with locals = ctx.locals } in
      let if_block =
        {
          if_block with
          Ast.desc =
            List.concat_map
              (instruction (push ret label) then_ctx)
              if_block.desc;
        }
      in
      let else_block =
        match else_block with
        | Some e ->
            let else_ctx = { ctx with locals = ctx.locals } in
            {
              e with
              Ast.desc =
                List.concat_map (instruction (push ret label) else_ctx) e.desc;
            }
        | None -> Ast.no_loc []
      in
      folded loc
        (If { label; typ = blocktype typ; if_block; else_block })
        cond_code
  | TryTable { label = labl; typ; block; catches } ->
      let inner_ctx = { ctx with locals = ctx.locals } in
      let block =
        {
          block with
          Ast.desc =
            List.concat_map (instruction (push ret labl) inner_ctx) block.desc;
        }
      in
      let catches =
        List.map
          (fun catch : Text.catch ->
            match catch with
            | Catch (tag, labl) -> Catch (index tag, label ret labl)
            | CatchRef (tag, labl) -> CatchRef (index tag, label ret labl)
            | CatchAll labl -> CatchAll (label ret labl)
            | CatchAllRef labl -> CatchAllRef (label ret labl))
          catches
      in
      folded loc
        (TryTable { label = labl; typ = blocktype typ; block; catches })
        []
  | Try { label; typ; block; catches; catch_all } ->
      let inner_ctx = { ctx with locals = ctx.locals } in
      let block =
        {
          block with
          Ast.desc =
            List.concat_map (instruction (push ret label) inner_ctx) block.desc;
        }
      in
      let catches =
        List.map
          (fun (tag, block) ->
            let inner_ctx = { ctx with locals = ctx.locals } in
            ( index tag,
              {
                block with
                Ast.desc =
                  List.concat_map
                    (instruction (push ret label) inner_ctx)
                    block.Annot.desc;
              } ))
          catches
      in
      let catch_all =
        Option.map
          (fun block ->
            let inner_ctx = { ctx with locals = ctx.locals } in
            {
              block with
              Ast.desc =
                List.concat_map
                  (instruction (push ret label) inner_ctx)
                  block.Annot.desc;
            })
          catch_all
      in
      folded loc
        (Try { label; typ = blocktype typ; block; catches; catch_all })
        []
  | TryCatch { label; typ; block; arms } ->
      (* Lower to [try_table] plus the block ladder (see
         [Ast_utils.lower_trycatch]) and convert. Fresh readable [catch]/[join]
         labels avoid the enclosing labels, any label nested in the bodies, and
         the try's own label; [join] is the try's label when it has one, so a
         [br] to it exits the join block carrying the value. The synthesised
         wrappers need no type annotation ([([||], loc)]): the blocks carry
         their blocktypes and the [br]'s operand is the [try_table] itself. *)
      let avoid =
        (match label with Some l -> [ l.desc ] | None -> [])
        @ labels_in_list
            (block.desc @ List.concat_map (fun a -> a.arm_body.desc) arms)
      in
      let arm_names, join_name =
        fresh_trycatch_labels ret ~avoid (List.length arms)
      in
      let join =
        match label with Some l -> l | None -> Ast.no_loc join_name
      in
      let arm_labels = List.map Ast.no_loc arm_names in
      instruction ret ctx
        (Wax_lang.Ast_utils.lower_trycatch ~block_info:([||], loc) ~join
           ~arm_labels ~typ ~block ~arms)
  | Unreachable -> folded loc Unreachable []
  | Nop -> folded loc Nop []
  | Hole -> []
  | Null -> folded loc (RefNull (heaptype (expr_reftype i).typ)) []
  | Get idx ->
      if StringMap.mem idx.desc ctx.locals then
        let wasm_name = StringMap.find idx.desc ctx.locals in
        folded loc (Text.LocalGet (annot idx.Ast.info (Text.Id wasm_name))) []
      else if Hashtbl.mem ctx.functions idx.desc then
        (Hashtbl.replace ctx.referenced_functions idx.desc ();
         folded loc (Text.RefFunc (index idx)))
          []
      else folded loc (Text.GlobalGet (index idx)) []
  | Path _ ->
      (* A qualified path is only valid as a call callee (handled in the [Call]
         case); typing rejects a bare one, so it never reaches lowering. *)
      assert false
  | Set (idx, op, expr) ->
      (* A compound assignment [x op= e] reads [x], evaluates [e], applies the
         operator, then stores back into [x]; a plain [x = e] just stores. *)
      let store, load =
        if StringMap.mem idx.desc ctx.locals then
          let id =
            annot idx.Ast.info
              (Text.Id (StringMap.find idx.Ast.desc ctx.locals))
          in
          (Text.LocalSet id, Text.LocalGet id)
        else (Text.GlobalSet (index idx), Text.GlobalGet (index idx))
      in
      let code = instruction ret ctx expr in
      let code =
        match op with
        | None -> code
        | Some op ->
            folded loc
              (binop i op.desc (expr_valtype expr))
              (folded loc load [] @ code)
      in
      folded loc store code
  | Tee (idx, expr) ->
      let code = instruction ret ctx expr in
      let wasm_name = StringMap.find idx.desc ctx.locals in
      folded loc (LocalTee (annot idx.Ast.info (Text.Id wasm_name))) code
  | Call (f, args) -> (
      (* Shared lowering of the positional operands, forced only by the arms that
         actually use it. It is [lazy] because several arms (memory/table
         accesses, array ops) rebuild their own operand code and never force it;
         lowering has side effects (local allocation, name reservation), so an
         eager computation would lower those operands a second time — and since a
         nested call re-enters this arm, that doubling compounds to exponential
         work in the nesting depth. The labels are dropped here because only a
         memory access carries [Labelled] immediates, and those arms rebuild. *)
      let arg_code =
        lazy (List.concat_map (instruction ret ctx) (fst (split_labelled args)))
      in
      match f.desc with
      (* Qualified-path intrinsics. [v128::<shape>(..)] / [v128::bitselect]
         are the SIMD free functions; [i64::add128(..)] etc. are wide arithmetic
         (operands already on the stack in call order, low/high of each input). *)
      | Path ({ desc = "v128"; _ }, name) -> (
          match Simd.const_shape_of_name (Simd.free_full name.desc) with
          | Some shape ->
              let components = List.map literal_string args in
              folded loc (VecConst { Wax_utils.V128.shape; components }) []
          | None -> folded loc VecBitselect (Lazy.force arg_code))
      | Path ({ desc = "atomic"; _ }, { desc = "fence"; _ }) ->
          folded loc AtomicFence []
      | Path (ns, name) ->
          let desc : _ Text.instr_desc =
            match (ns.desc, name.desc) with
            | "i64", "add128" -> Add128
            | "i64", "sub128" -> Sub128
            | "i64", "mul_wide_s" -> MulWide Signed
            | "i64", "mul_wide_u" -> MulWide Unsigned
            | _ -> assert false (* typing rejects any other path *)
          in
          folded loc desc (Lazy.force arg_code)
      | Get idx ->
          if
            Hashtbl.mem ctx.functions idx.desc
            && not (StringMap.mem idx.desc ctx.locals)
          then folded loc (Call (index idx)) (Lazy.force arg_code)
          else
            let code = instruction ret ctx f in
            folded loc
              (CallRef (index (expr_type_name f)))
              (Lazy.force arg_code @ code)
      (* Atomic access: mem.atomic_*(addr [, val…] [, offset: N]). The method
         name carries the access width (also the natural alignment); the value
         operand's type picks the i32/i64 op. A narrow load's resolving [as
         iN_u] cast is fused in the Cast case; bare, it defaults to the
         zero-extended i32 form. *)
      | StructGet ({ desc = Get memname; _ }, meth)
        when memory_receiver ctx memname.desc
             && Atomics.of_method_name meth.desc <> None ->
          let family = Option.get (Atomics.of_method_name meth.desc) in
          let memidx = index memname in
          let stack_args, labels = split_labelled args in
          let memarg =
            memarg_of_labels ~natural:(Atomics.family_bytes family) labels
          in
          let code = List.concat_map (instruction ret ctx) stack_args in
          folded loc (Atomic (memidx, atomic_op family stack_args, memarg)) code
      (* Memory access: mem.loadN/storeN(addr [, offset: N] [, align: N]).
         Signed narrow loads are handled (under an [as iN_s] cast) in the Cast
         case. *)
      | StructGet ({ desc = Get memname; _ }, meth)
        when memory_receiver ctx memname.desc && is_mem_method meth.desc ->
          let memidx = index memname in
          let memarg = mem_memarg meth.desc args in
          if mem_store_method meth.desc then
            let addr_code = instruction ret ctx (List.nth args 0) in
            let value = List.nth args 1 in
            let value_code = instruction ret ctx value in
            let desc =
              (* The value type is unknown ([None]) in unreachable code; the
                 width is what matters there, so default to the i32 form. *)
              match (meth.desc, expr_opt_valtype value) with
              | "store8", Some I64 -> Text.StoreS (memidx, memarg, `I64, `I8)
              | "store8", _ -> Text.StoreS (memidx, memarg, `I32, `I8)
              | "store16", Some I64 -> Text.StoreS (memidx, memarg, `I64, `I16)
              | "store16", _ -> Text.StoreS (memidx, memarg, `I32, `I16)
              | "store32", Some I64 -> Text.StoreS (memidx, memarg, `I64, `I32)
              | "store32", _ -> Text.Store (memidx, memarg, NumI32)
              | "store64", _ -> Text.Store (memidx, memarg, NumI64)
              | "storef32", _ -> Text.Store (memidx, memarg, NumF32)
              | _ -> Text.Store (memidx, memarg, NumF64)
            in
            folded loc desc (addr_code @ value_code)
          else
            let addr_code = instruction ret ctx (List.nth args 0) in
            let desc =
              match meth.desc with
              | "load8" -> Text.LoadS (memidx, memarg, `I32, `I8, Unsigned)
              | "load16" -> Text.LoadS (memidx, memarg, `I32, `I16, Unsigned)
              | "load32" -> Text.Load (memidx, memarg, NumI32)
              | "load64" -> Text.Load (memidx, memarg, NumI64)
              | "loadf32" -> Text.Load (memidx, memarg, NumF32)
              | _ -> Text.Load (memidx, memarg, NumF64)
            in
            folded loc desc addr_code
      (* SIMD memory accesses: mem.loadv128(addr [, offset: N] [, align: N]),
         mem.storev128(addr, v, ...), mem.load8_lane(addr, v, lane: N,
         ...). The stack operands are positional; the lane (mandatory on lane
         accesses) and align/offset immediates are labelled. *)
      | StructGet ({ desc = Get memname; _ }, meth)
        when memory_receiver ctx memname.desc && Simd.is_mem_method meth.desc ->
          let mop = Option.get (Simd.mem_method meth.desc) in
          let memidx = index memname in
          let stack_args, labels = split_labelled args in
          let lane =
            if mop.m_lane then lane_imm (List.assoc "lane" labels) else 0
          in
          let memarg = memarg_of_labels ~natural:mop.m_nat_align labels in
          let operand_code = List.concat_map (instruction ret ctx) stack_args in
          folded loc (mop.m_make memidx memarg lane) operand_code
      (* Binary intrinsics, written with the dot notation *)
      (* These binary intrinsics all yield their receiver's type, so read it from
         the receiver ([obj]), not from [i]: as a tail call ([become x.rotl(1)])
         [i] is the [TailCall] node, which leaves no value on the stack, so its
         result-type info is empty and [expr_valtype i] would assert. The unary
         intrinsics below already consult [obj] for the same reason. *)
      | StructGet (obj, { desc = "rotl"; _ }) when receiver_is_value obj -> (
          let obj_code = instruction ret ctx obj in
          match expr_valtype obj with
          | I32 -> folded loc (BinOp (I32 Rotl)) (obj_code @ Lazy.force arg_code)
          | I64 -> folded loc (BinOp (I64 Rotl)) (obj_code @ Lazy.force arg_code)
          | _ -> assert false)
      | StructGet (obj, { desc = "rotr"; _ }) when receiver_is_value obj -> (
          let obj_code = instruction ret ctx obj in
          match expr_valtype obj with
          | I32 -> folded loc (BinOp (I32 Rotr)) (obj_code @ Lazy.force arg_code)
          | I64 -> folded loc (BinOp (I64 Rotr)) (obj_code @ Lazy.force arg_code)
          | _ -> assert false)
      | StructGet (obj, { desc = "min"; _ }) when receiver_is_value obj -> (
          let obj_code = instruction ret ctx obj in
          match expr_valtype obj with
          | F32 -> folded loc (BinOp (F32 Min)) (obj_code @ Lazy.force arg_code)
          | F64 -> folded loc (BinOp (F64 Min)) (obj_code @ Lazy.force arg_code)
          | _ -> assert false)
      | StructGet (obj, { desc = "max"; _ }) when receiver_is_value obj -> (
          let obj_code = instruction ret ctx obj in
          match expr_valtype obj with
          | F32 -> folded loc (BinOp (F32 Max)) (obj_code @ Lazy.force arg_code)
          | F64 -> folded loc (BinOp (F64 Max)) (obj_code @ Lazy.force arg_code)
          | _ -> assert false)
      | StructGet (obj, { desc = "copysign"; _ }) when receiver_is_value obj
        -> (
          let obj_code = instruction ret ctx obj in
          match expr_valtype obj with
          | F32 ->
              folded loc (BinOp (F32 CopySign)) (obj_code @ Lazy.force arg_code)
          | F64 ->
              folded loc (BinOp (F64 CopySign)) (obj_code @ Lazy.force arg_code)
          | _ -> assert false)
      (* No-argument instruction methods written with dot notation:
         [arr.length()], and the unary operators / reinterpret casts below. *)
      | StructGet (obj, { desc = "length"; _ }) when receiver_is_array ctx obj
        ->
          folded loc ArrayLen (instruction ret ctx obj)
      | StructGet (obj, meth)
        when is_unary_op_method meth.desc && receiver_is_value obj -> (
          let obj_code = instruction ret ctx obj in
          match (meth.desc, expr_valtype obj) with
          (* Int Unary *)
          | "clz", I32 -> folded loc (UnOp (I32 Clz)) obj_code
          | "ctz", I32 -> folded loc (UnOp (I32 Ctz)) obj_code
          | "popcnt", I32 -> folded loc (UnOp (I32 Popcnt)) obj_code
          | "clz", I64 -> folded loc (UnOp (I64 Clz)) obj_code
          | "ctz", I64 -> folded loc (UnOp (I64 Ctz)) obj_code
          | "popcnt", I64 -> folded loc (UnOp (I64 Popcnt)) obj_code
          | "extend8_s", I32 -> folded loc (UnOp (I32 (ExtendS `_8))) obj_code
          | "extend16_s", I32 -> folded loc (UnOp (I32 (ExtendS `_16))) obj_code
          | "extend8_s", I64 -> folded loc (UnOp (I64 (ExtendS `_8))) obj_code
          | "extend16_s", I64 -> folded loc (UnOp (I64 (ExtendS `_16))) obj_code
          (* Float Unary *)
          | "abs", F32 -> folded loc (UnOp (F32 Abs)) obj_code
          | "ceil", F32 -> folded loc (UnOp (F32 Ceil)) obj_code
          | "floor", F32 -> folded loc (UnOp (F32 Floor)) obj_code
          | "trunc", F32 -> folded loc (UnOp (F32 Trunc)) obj_code
          | "nearest", F32 -> folded loc (UnOp (F32 Nearest)) obj_code
          | "sqrt", F32 -> folded loc (UnOp (F32 Sqrt)) obj_code
          | "abs", F64 -> folded loc (UnOp (F64 Abs)) obj_code
          | "ceil", F64 -> folded loc (UnOp (F64 Ceil)) obj_code
          | "floor", F64 -> folded loc (UnOp (F64 Floor)) obj_code
          | "trunc", F64 -> folded loc (UnOp (F64 Trunc)) obj_code
          | "nearest", F64 -> folded loc (UnOp (F64 Nearest)) obj_code
          | "sqrt", F64 -> folded loc (UnOp (F64 Sqrt)) obj_code
          (* Reinterpret *)
          | "to_bits", F32 -> folded loc (UnOp (I32 Reinterpret)) obj_code
          | "from_bits", I32 -> folded loc (UnOp (F32 Reinterpret)) obj_code
          | "to_bits", F64 -> folded loc (UnOp (I64 Reinterpret)) obj_code
          | "from_bits", I64 -> folded loc (UnOp (F64 Reinterpret)) obj_code
          | _ -> assert false)
      (* SIMD vector op written as a method intrinsic, [recv.add_i32x4(b)]. The
         lane shape comes from the method name; arguments are the lane immediates
         (if any) followed by the remaining stack operands. *)
      | StructGet (obj, meth)
        when Simd.classify meth.desc <> None && receiver_is_value obj ->
          let op = Option.get (Simd.classify meth.desc) in
          let nimm =
            match op.imm with No_imm -> 0 | Lane _ -> 1 | Shuffle -> 16
          in
          let lanes =
            List.filteri (fun k _ -> k < nimm) args |> List.map lane_imm
          in
          let stack_args = List.filteri (fun k _ -> k >= nimm) args in
          let obj_code = instruction ret ctx obj in
          let stack_code = List.concat_map (instruction ret ctx) stack_args in
          folded loc (op.build lanes) (obj_code @ stack_code)
      (* Memory management: mem.size/grow/fill/copy/init *)
      | StructGet ({ desc = Get name; _ }, meth)
        when memory_receiver ctx name.desc && is_mgmt_method meth.desc -> (
          let m = index name in
          match meth.desc with
          | "size" -> folded loc (MemorySize m) []
          | "grow" -> folded loc (MemoryGrow m) (Lazy.force arg_code)
          | "fill" -> folded loc (MemoryFill m) (Lazy.force arg_code)
          | "copy" -> (
              (* Cross-memory copy names the source memory as the first arg. *)
              match args with
              | { desc = Get src; _ } :: rest when memory_receiver ctx src.desc
                ->
                  let rest_code = List.concat_map (instruction ret ctx) rest in
                  folded loc (MemoryCopy (m, index src)) rest_code
              | _ -> folded loc (MemoryCopy (m, m)) (Lazy.force arg_code))
          | _ (* init *) ->
              let seg =
                match args with
                | { desc = Get s; _ } :: _ -> s
                | _ -> assert false
              in
              let rest_code =
                List.concat_map (instruction ret ctx) (List.tl args)
              in
              folded loc (MemoryInit (m, index seg)) rest_code)
      (* Table management: tab.size/grow/fill/copy/init *)
      | StructGet ({ desc = Get name; _ }, meth)
        when table_receiver ctx name.desc && is_mgmt_method meth.desc -> (
          let t = index name in
          match meth.desc with
          | "size" -> folded loc (TableSize t) []
          | "grow" -> folded loc (TableGrow t) (Lazy.force arg_code)
          | "fill" -> folded loc (TableFill t) (Lazy.force arg_code)
          | "copy" -> (
              (* Cross-table copy names the source table as the first arg. *)
              match args with
              | { desc = Get src; _ } :: rest when table_receiver ctx src.desc
                ->
                  let rest_code = List.concat_map (instruction ret ctx) rest in
                  folded loc (TableCopy (t, index src)) rest_code
              | _ -> folded loc (TableCopy (t, t)) (Lazy.force arg_code))
          | _ (* init *) ->
              let seg =
                match args with
                | { desc = Get s; _ } :: _ -> s
                | _ -> assert false
              in
              let rest_code =
                List.concat_map (instruction ret ctx) (List.tl args)
              in
              folded loc (TableInit (t, index seg)) rest_code)
      (* data.drop / elem.drop — only on an actual segment name, not shadowed by
         a local (a same-named field call is an indirect call, below). *)
      | StructGet ({ desc = Get name; _ }, { desc = "drop"; _ })
        when segment_receiver ctx name.desc ->
          if Hashtbl.mem ctx.elems name.desc then
            folded loc (ElemDrop (index name)) []
          else folded loc (DataDrop (index name)) []
      | StructGet (obj, { desc = "fill"; _ }) when receiver_is_array ctx obj ->
          let array_code = instruction ret ctx obj in
          let type_name_idx = expr_type_name obj in
          folded loc
            (ArrayFill (index type_name_idx))
            (array_code @ Lazy.force arg_code)
      | StructGet (obj, { desc = "copy"; _ }) when receiver_is_array ctx obj ->
          let a1_code = instruction ret ctx obj in
          let type_a1 = expr_type_name obj in
          let a2_code = List.nth args 1 in
          let type_a2 = expr_type_name a2_code in
          folded loc
            (ArrayCopy (index type_a1, index type_a2))
            (a1_code @ Lazy.force arg_code)
      (* array.init_data / array.init_elem: arr.init(seg, dest, src, len) *)
      | StructGet (obj, { desc = "init"; _ }) when receiver_is_array ctx obj ->
          let seg =
            match args with { desc = Get s; _ } :: _ -> s | _ -> assert false
          in
          let obj_code = instruction ret ctx obj in
          let rest_code =
            List.concat_map (instruction ret ctx) (List.tl args)
          in
          let arrty = expr_type_name obj in
          let desc : _ Text.instr_desc =
            if Hashtbl.mem ctx.elems seg.desc then
              ArrayInitElem (index arrty, index seg)
            else ArrayInitData (index arrty, index seg)
          in
          folded loc desc (obj_code @ rest_code)
      (* Indirect call: re-fuse [(tab[i] as &$ft)(args)] (and the cast-free
         [tab[i](args)] when the table element is already a concrete &$ft) back
         to [call_indirect]. *)
      | Cast
          ( { desc = ArrayGet ({ desc = Get tab; _ }, idx_expr); _ },
            Valtype (Ref { typ = Type ft; _ }) )
        when table_receiver ctx tab.desc ->
          let index_code = instruction ret ctx idx_expr in
          folded loc
            (CallIndirect (index tab, (Some (index ft), None)))
            (Lazy.force arg_code @ index_code)
      | Cast
          ( { desc = ArrayGet ({ desc = Get tab; _ }, idx_expr); _ },
            Functype { sign; _ } )
        when table_receiver ctx tab.desc ->
          (* Inline function type: emit an inline typeuse [(result ..)]. *)
          let index_code = instruction ret ctx idx_expr in
          folded loc
            (CallIndirect (index tab, (None, Some (functype sign))))
            (Lazy.force arg_code @ index_code)
      | ArrayGet ({ desc = Get tab; _ }, idx_expr)
        when table_receiver ctx tab.desc
             &&
             match Hashtbl.find ctx.tables tab.desc with
             | { typ = Type _; _ } -> true
             | _ -> false ->
          let ft =
            match Hashtbl.find ctx.tables tab.desc with
            | { typ = Type ft; _ } -> ft
            | _ -> assert false
          in
          let index_code = instruction ret ctx idx_expr in
          folded loc
            (CallIndirect (index tab, (Some (index ft), None)))
            (Lazy.force arg_code @ index_code)
      | _ ->
          let code = instruction ret ctx f in
          folded loc
            (CallRef (index (expr_type_name f)))
            (Lazy.force arg_code @ code))
  | TailCall (f, args) -> (
      (* A tail call lowers like the corresponding call (reusing the whole
         intrinsic-and-call dispatch of the [Call] case), then the trailing call
         instruction becomes its [return_call*] form. An intrinsic operation
         cannot be a tail call, so it is instead evaluated and its result
         returned. *)
      let code = instruction ret ctx { i with desc = Call (f, args) } in
      match code with
      | [ ({ desc = Text.Folded (inner, ops); _ } as node) ] -> (
          let return_desc : _ Text.instr_desc option =
            match inner.desc with
            | Call idx -> Some (ReturnCall idx)
            | CallIndirect (tab, tu) -> Some (ReturnCallIndirect (tab, tu))
            | CallRef t -> Some (ReturnCallRef t)
            | _ -> None
          in
          match return_desc with
          | Some d ->
              [
                { node with desc = Text.Folded ({ inner with desc = d }, ops) };
              ]
          | None -> folded loc Return code)
      | _ -> folded loc Return code)
  | Int s -> (
      match expr_valtype i with
      | I32 -> folded loc (Const (I32 s)) []
      | I64 -> folded loc (Const (I64 s)) []
      | F32 -> folded loc (Const (F32 s)) []
      | F64 -> folded loc (Const (F64 s)) []
      | _ -> assert false)
  | Float s -> (
      match expr_valtype i with
      | F32 -> folded loc (Const (F32 s)) []
      | F64 -> folded loc (Const (F64 s)) []
      | _ -> assert false)
  | Cast (expr, cast_ty) when cont_cast_target ctx cast_ty ->
      instruction ret ctx expr
  | Cast (expr, cast_ty) -> (
      let default_cast () =
        let code = instruction ret ctx expr in
        match expr_opt_valtype expr with
        (* A POISONED cast — its own cell resolved to no type. Only the
           conditional-annotation tree pass can hand one to the lowering (its
           per-configuration checks own the diagnostics — see
           [Typing.f_infer]; every other path exits on the error): the cast's
           hole positionally captured a value an [(@if)] branch consumes in its
           own configuration, so the pair has no instruction. Emit the operand
           alone — the mis-attributed value was never this cast's runtime
           operand (its own residual statement emits its opcodes), so the
           instruction stream stays source-shaped. *)
        | _ when expr_opt_valtype i = None -> code
        | None -> code
        | Some in_ty -> (
            (* Several casts widen or convert through a forced intermediate
               type; emit it here (and update [in_ty]) so the single Wax cast
               lowers to the same instructions the double cast would. The
               match below then finishes the cast on the intermediate value. *)
            let code, in_ty =
              match (in_ty, cast_ty) with
              (* [ref as i32_s/u]: cast a non-[i31] reference to [(ref i31)]
                 first; [i31.get] follows in the match below. *)
              | Ref { typ = I31; _ }, Signedtype { typ = `I32; _ } ->
                  (code, in_ty)
              | Ref _, Signedtype { typ = `I32; _ } ->
                  ( folded loc
                      (RefCast (reftype { nullable = false; typ = I31 }))
                      code,
                    in_ty )
              (* [ref as i64_s/u]: [ref.cast]+[i31.get] as above, then the match
                 below widens the [i32] with [i64.extend_i32_X]. *)
              | Ref { typ = I31; _ }, Signedtype { typ = `I64; signage; _ } ->
                  (folded loc (I31Get signage) code, I32)
              | Ref _, Signedtype { typ = `I64; signage; _ } ->
                  ( folded loc (I31Get signage)
                      (folded loc
                         (RefCast (reftype { nullable = false; typ = I31 }))
                         code),
                    I32 )
              (* [i64 as &i31]: [ref.i31] takes an [i32], so wrap first. *)
              | I64, Valtype (Ref { typ = I31; _ }) ->
                  (folded loc I32WrapI64 code, I32)
              (* [i32 as &extern]: box as [i31] first ([extern.convert_any]
                 follows in the match below). *)
              | I32, Valtype (Ref { typ = Extern; _ }) ->
                  (folded loc RefI31 code, Ref { nullable = false; typ = I31 })
              (* [i64 as &extern]: wrap to [i32] (as [i64 as &i31]), box as
                 [i31]; [extern.convert_any] follows in the match below. *)
              | I64, Valtype (Ref { typ = Extern; _ }) ->
                  ( folded loc RefI31 (folded loc I32WrapI64 code),
                    Ref { nullable = false; typ = I31 } )
              (* [extern as &T] for an [any]-hierarchy [T]: convert to [any]
                 first, then the match below does the [ref.cast] to [T]. A
                 non-null [&any] target from a *nullable* operand needs that
                 [ref.cast] too, to null-check the [any.convert_extern] result;
                 a non-null operand already yields a non-null [any] (the convert
                 preserves non-nullness), and a nullable [&?any] target is just
                 the convert (both handled by the [Any] arm of the match below). *)
              | ( Ref { typ = Extern | NoExtern; _ },
                  Valtype
                    (Ref
                       {
                         typ =
                           Eq | I31 | Struct | Array | Type _ | Exact _ | None_;
                         _;
                       }) )
              | ( Ref { typ = Extern | NoExtern; nullable = true },
                  Valtype (Ref { typ = Any; nullable = false }) ) ->
                  ( folded loc AnyConvertExtern code,
                    Ref { nullable = true; typ = Any } )
              | _ -> (code, in_ty)
            in
            let instr : _ Text.instr_desc =
              match (in_ty, cast_ty) with
              (* I31 *)
              | I32, Valtype (Ref { typ = I31; _ }) -> RefI31
              | Ref _, Signedtype { typ = `I32; signage; _ } -> I31Get signage
              (* Extern / Any *)
              | ( Ref
                    {
                      typ =
                        ( Any | Eq | I31 | Struct | Array | Type _ | Exact _
                        | None_ );
                      _;
                    },
                  Valtype (Ref { typ = Extern; _ }) ) ->
                  ExternConvertAny
              | ( Ref { typ = Extern | NoExtern; _ },
                  Valtype (Ref { typ = Any; _ }) ) ->
                  AnyConvertExtern
              (* The claim-free bottom pin under a same-hierarchy type pin
                 ([((_ as &?nofunc) as &?t)], the [call_ref] callee shape): the
                 whole chain is a compile-time ascription of the polymorphic
                 bottom, so there is no [ref.cast] to emit — the general arm
                 below would materialise an opcode the source never had. The
                 cross-hierarchy converts (matched above) still fire. *)
              | ( Ref { typ = None_ | NoFunc | NoExtern | NoExn | NoCont; _ },
                  Valtype (Ref _) )
                when match expr.desc with
                     | Cast
                         ( { desc = Hole; _ },
                           Valtype
                             (Ref
                                {
                                  typ =
                                    None_ | NoFunc | NoExtern | NoExn | NoCont;
                                  _;
                                }) ) ->
                         true
                     | _ -> false ->
                  Nop
              (* RefCast *)
              | Ref _, Valtype (Ref r) -> RefCast (reftype r)
              (* Numeric conversions *)
              | I64, Valtype I32 -> I32WrapI64
              | F64, Valtype F32 -> F32DemoteF64
              | F32, Valtype F64 -> F64PromoteF32
              | I32, Signedtype { typ = `I64; signage; _ } ->
                  I64ExtendI32 signage
              (* Trunc *)
              | F32, Signedtype { typ = `I32; signage = s; strict } ->
                  UnOp
                    (I32
                       (if strict then Trunc (`F32, s) else TruncSat (`F32, s)))
              | F64, Signedtype { typ = `I32; signage = s; strict } ->
                  UnOp
                    (I32
                       (if strict then Trunc (`F64, s) else TruncSat (`F64, s)))
              | F32, Signedtype { typ = `I64; signage = s; strict } ->
                  UnOp
                    (I64
                       (if strict then Trunc (`F32, s) else TruncSat (`F32, s)))
              | F64, Signedtype { typ = `I64; signage = s; strict } ->
                  UnOp
                    (I64
                       (if strict then Trunc (`F64, s) else TruncSat (`F64, s)))
              (* Convert *)
              | I32, Signedtype { typ = `F32; signage; _ } ->
                  UnOp (F32 (Convert (`I32, signage)))
              | I64, Signedtype { typ = `F32; signage; _ } ->
                  UnOp (F32 (Convert (`I64, signage)))
              | I32, Signedtype { typ = `F64; signage; _ } ->
                  UnOp (F64 (Convert (`I32, signage)))
              | I64, Signedtype { typ = `F64; signage; _ } ->
                  UnOp (F64 (Convert (`I64, signage)))
              (* Identity: no instruction needed; [Nop] is a sentinel elided
                 below. *)
              | I32, Valtype I32
              | I64, Valtype I64
              | F32, Valtype F32
              | F64, Valtype F64
              | V128, Valtype V128 ->
                  Nop
              (* Cast to an inline function type: ref.cast to the anonymous
                 function type minted for the cast's result. *)
              | _, Functype _ -> RefCast (reftype (expr_reftype i))
              | _ ->
                  print_valtype in_ty;
                  print_instr i;
                  assert false
            in
            match instr with Nop -> code | _ -> folded loc instr code)
      in
      match expr.desc with
      (* A bare hole under a BOTTOM reference ascription ([_ as &?none] and
         kin) is the decompiler's claim-free dead-code pin (see [Typing]'s
         [count_holes]): it stands for a value off the polymorphic stack
         bottom, so the ascription is compile-time only — nothing to emit
         (lowering it as the general ref-to-ref case's [ref.cast] would
         materialise an opcode the source never had). *)
      | Hole
        when match cast_ty with
             | Valtype
                 (Ref { typ = None_ | NoFunc | NoExtern | NoExn | NoCont; _ })
               ->
                 true
             | _ -> false ->
          []
      (* (i64 as i32) as i64_s  ->  i64.extend32_s. There is no dedicated Wax
         spelling for [i64.extend32_s], so the decompiler renders it as this
         wrap-then-sign-extend pair; re-fuse it back into the single instruction
         (as [default_cast] would otherwise emit the pair verbatim). Only a
         *signed* widening of a genuinely *wrapped* [i64] is [extend32_s]: an
         unsigned widen, or an [i32] source (where the inner cast is the
         identity), is a different operation and falls through. *)
      | Cast (inner, Valtype I32)
        when expr_opt_valtype inner = Some I64
             &&
             match cast_ty with
             | Signedtype { typ = `I64; signage = Signed; _ } -> true
             | _ -> false ->
          folded loc (UnOp (I64 (ExtendS `_32))) (instruction ret ctx inner)
      (* A *double*-cast narrow load ([(mem.load8(p) as i32_s) as i64_s]) is
         deliberately NOT fused: it is a distinct AST from the idiomatic
         single-cast [mem.load8(p) as i64_s] (kept below), and conflating the two
         hid that the honest lowering of the double cast is the pair
         [i32.load8_s; i64.extend_i32_s]. It now falls through to [default_cast],
         which emits exactly that pair. The default decompile path is unaffected:
         the Wax typer's [simplify] coalesces a narrow-load-then-widen to the
         single-cast spelling, so the double cast only ever comes from
         hand-written Wax. (The atomic analogue is likewise left unfused.)
         mem.load8/16(p) as i32_S -> i32.load8/16_S ; mem.load32(p) as i64_S ->
         i64.load32_S *)
      | Call ({ desc = StructGet ({ desc = Get memname; _ }, meth); _ }, args)
        when memory_receiver ctx memname.desc
             && (meth.desc = "load8" || meth.desc = "load16"
               || meth.desc = "load32") -> (
          let emit result_ty size signage =
            let memidx = index memname in
            let memarg = mem_memarg meth.desc args in
            let addr_code = instruction ret ctx (List.nth args 0) in
            folded (snd expr.info)
              (LoadS (memidx, memarg, result_ty, size, signage))
              addr_code
          in
          match (meth.desc, cast_ty) with
          | "load8", Signedtype { typ = `I32; signage; _ } ->
              emit `I32 `I8 signage
          | "load16", Signedtype { typ = `I32; signage; _ } ->
              emit `I32 `I16 signage
          | "load8", Signedtype { typ = `I64; signage; _ } ->
              emit `I64 `I8 signage
          | "load16", Signedtype { typ = `I64; signage; _ } ->
              emit `I64 `I16 signage
          | "load32", Signedtype { typ = `I64; signage; _ } ->
              emit `I64 `I32 signage
          | _ -> default_cast ())
      (* (The double-cast atomic narrow load [(mem.atomic_load8(p) as i32_u) as
         i64_u] is left unfused for the same reason as the plain double cast
         above: it falls through to the honest [i32.atomic.load8_u;
         i64.extend_i32_u] pair, while the decompiler emits the single-cast
         spelling handled next.)
         mem.atomic_load8/16(p) as iN_u -> iN.atomic.load8/16_u ;
         mem.atomic_load32(p) as i64_u -> i64.atomic.load32_u. Only the
         zero-extending forms exist: [atomic_load32(p) as i64_s] falls through
         to the plain i32 atomic load followed by [i64.extend_i32_s] (and
         typing rejects [as iN_s] on the 8/16-bit loads). *)
      | Call ({ desc = StructGet ({ desc = Get memname; _ }, meth); _ }, args)
        when memory_receiver ctx memname.desc
             &&
             match Atomics.of_method_name meth.desc with
             | Some (Atomics.Load (`W8 | `W16 | `W32)) -> true
             | _ -> false -> (
          let w =
            match Atomics.of_method_name meth.desc with
            | Some (Atomics.Load w) -> w
            | _ -> assert false
          in
          let emit t pw =
            let stack_args, labels = split_labelled args in
            let memarg =
              memarg_of_labels ~natural:(Atomics.width_bytes w) labels
            in
            let addr_code = List.concat_map (instruction ret ctx) stack_args in
            folded (snd expr.info)
              (Atomic (index memname, Ast.AtomicLoad (t, Some pw), memarg))
              addr_code
          in
          match (w, cast_ty) with
          | `W8, Signedtype { typ = (`I32 | `I64) as t; signage = Unsigned; _ }
            ->
              emit t `I8
          | `W16, Signedtype { typ = (`I32 | `I64) as t; signage = Unsigned; _ }
            ->
              emit t `I16
          | `W32, Signedtype { typ = `I64; signage = Unsigned; _ } ->
              emit `I64 `I32
          | _ -> default_cast ())
      | StructGet (instr_val, field_idx) -> (
          match (expr_type expr, cast_ty) with
          | Packed _, Signedtype { typ = `I32; signage; _ } ->
              let type_name_idx = expr_type_name instr_val in
              folded (snd expr.info)
                (StructGet (Some signage, index type_name_idx, index field_idx))
                (instruction ret ctx instr_val)
          | Packed _, Signedtype { typ = `I64; signage; _ } ->
              (* No packed [struct.get] yields [i64]; read as [i32] then widen. *)
              let type_name_idx = expr_type_name instr_val in
              folded loc (I64ExtendI32 signage)
                (folded (snd expr.info)
                   (StructGet
                      (Some signage, index type_name_idx, index field_idx))
                   (instruction ret ctx instr_val))
          | _ -> default_cast ())
      | ArrayGet (arr_instr, idx_instr) -> (
          match (expr_type expr, cast_ty) with
          | Packed _, Signedtype { typ = `I32; signage; _ } ->
              let type_name_idx = expr_type_name arr_instr in
              folded (snd expr.info)
                (ArrayGet (Some signage, index type_name_idx))
                (instruction ret ctx arr_instr @ instruction ret ctx idx_instr)
          | Packed _, Signedtype { typ = `I64; signage; _ } ->
              (* No packed [array.get] yields [i64]; read as [i32] then widen. *)
              let type_name_idx = expr_type_name arr_instr in
              folded loc (I64ExtendI32 signage)
                (folded (snd expr.info)
                   (ArrayGet (Some signage, index type_name_idx))
                   (instruction ret ctx arr_instr
                   @ instruction ret ctx idx_instr))
          | _ -> default_cast ())
      | Null -> (
          match cast_ty with
          | Valtype (Ref r) ->
              let null = folded (snd expr.info) (RefNull (heaptype r.typ)) [] in
              if r.nullable then null else folded loc (RefCast (reftype r)) null
          | _ -> default_cast ())
      | _ -> default_cast ())
  | Test (expr, typ) ->
      folded loc (RefTest (reftype typ)) (instruction ret ctx expr)
  | NonNull expr -> folded loc RefAsNonNull (instruction ret ctx expr)
  | Struct (opt_idx, fields) ->
      let idx =
        match opt_idx with Some idx -> idx | None -> expr_type_name i
      in
      let field_names = Hashtbl.find ctx.struct_fields idx.desc in
      let args_code = struct_field_args ret ctx field_names fields in
      folded loc (StructNew (index idx)) args_code
  | StructDefault opt_idx ->
      (* Compute the fallback type only when no index was written: [expr_type_name]
         asserts on an abstract [&struct] receiver, and [Option.value ~default:]
         would evaluate it even for the [Some] case. *)
      let idx =
        match opt_idx with Some idx -> idx | None -> expr_type_name i
      in
      folded loc (StructNewDefault (index idx)) []
  | StructDesc (d, fields) ->
      (* The struct type is the (exact) result type. *)
      let idx = expr_type_name i in
      let field_names = Hashtbl.find ctx.struct_fields idx.desc in
      let args_code = struct_field_args ret ctx field_names fields in
      (* The descriptor operand is pushed last, above the field values. *)
      folded loc (StructNewDesc (index idx)) (args_code @ instruction ret ctx d)
  | StructDefaultDesc d ->
      folded loc
        (StructNewDefaultDesc (index (expr_type_name i)))
        (instruction ret ctx d)
  | StructGet (instr_val, field) ->
      (* Plain struct field access; the instruction methods that used to share
         this syntax now take parentheses and are handled in the [Call] case. *)
      folded loc
        (StructGet (None, index (expr_type_name instr_val), index field))
        (instruction ret ctx instr_val)
  | GetDescriptor instr_val ->
      folded loc
        (RefGetDesc (index (expr_type_name instr_val)))
        (instruction ret ctx instr_val)
  | CastDesc (value, _, d) ->
      (* The target reftype is the cast's (exact) result type; the descriptor
         operand is pushed last, above the value. *)
      folded loc
        (RefCastDescEq (reftype (expr_reftype i)))
        (instruction ret ctx value @ instruction ret ctx d)
  | StructSet (instr_val, field_idx, new_val) ->
      let code_val = instruction ret ctx instr_val in
      let code_new = instruction ret ctx new_val in
      folded loc
        (StructSet (index (expr_type_name instr_val), index field_idx))
        (code_val @ code_new)
  | Array (opt_idx, val_instr, len_instr) ->
      let idx =
        match opt_idx with Some idx -> idx | None -> expr_type_name i
      in
      folded loc
        (ArrayNew (index idx))
        (instruction ret ctx val_instr @ instruction ret ctx len_instr)
  | ArrayDefault (opt_idx, len_instr) ->
      let idx =
        match opt_idx with Some idx -> idx | None -> expr_type_name i
      in
      folded loc (ArrayNewDefault (index idx)) (instruction ret ctx len_instr)
  | ArrayFixed (opt_idx, instrs) ->
      let idx =
        match opt_idx with Some idx -> idx | None -> expr_type_name i
      in
      let args_code = List.concat_map (instruction ret ctx) instrs in
      let len = Uint32.of_int (List.length instrs) in
      folded loc (ArrayNewFixed (index idx, len)) args_code
  | ArraySegment (opt_idx, seg, off_instr, len_instr) ->
      let idx =
        match opt_idx with Some idx -> idx | None -> expr_type_name i
      in
      (* An element segment means [array.new_elem]; otherwise a data segment. *)
      let desc : _ Text.instr_desc =
        if Hashtbl.mem ctx.elems seg.desc then
          ArrayNewElem (index idx, index seg)
        else ArrayNewData (index idx, index seg)
      in
      folded loc desc
        (instruction ret ctx off_instr @ instruction ret ctx len_instr)
  (* [tab[i]] on a table name is [table.get]. *)
  | ArrayGet ({ desc = Get name; _ }, idx_instr)
    when table_receiver ctx name.desc ->
      folded loc (TableGet (index name)) (instruction ret ctx idx_instr)
  | ArrayGet (arr_instr, idx_instr) ->
      (* Signed accesses are under a cast *)
      folded loc
        (ArrayGet (None, index (expr_type_name arr_instr)))
        (instruction ret ctx arr_instr @ instruction ret ctx idx_instr)
  (* [tab[i] = v] on a table name is [table.set]. *)
  | ArraySet ({ desc = Get name; _ }, idx_instr, val_instr)
    when table_receiver ctx name.desc ->
      folded loc
        (TableSet (index name))
        (instruction ret ctx idx_instr @ instruction ret ctx val_instr)
  | ArraySet (arr_instr, idx_instr, val_instr) ->
      folded loc
        (ArraySet (index (expr_type_name arr_instr)))
        (instruction ret ctx arr_instr
        @ instruction ret ctx idx_instr
        @ instruction ret ctx val_instr)
  | BinOp ({ desc = op; _ }, a, b) -> (
      let code_a = instruction ret ctx a in
      let code_b = instruction ret ctx b in
      let operand_type = expr_valtype a in
      match (op, operand_type) with
      | Eq, Ref _ -> folded loc RefEq (code_a @ code_b)
      | Ne, Ref _ ->
          (* There is no [ref.ne]; [a != b] on references is [!(a == b)]. *)
          folded loc (Text.UnOp (I32 Eqz)) (folded loc RefEq (code_a @ code_b))
      | _ ->
          let opcode = binop i op operand_type in
          folded loc opcode (code_a @ code_b))
  (* Fold [-literal] into a single signed constant, but only when the negation
     is representable; an out-of-range magnitude (e.g. a u64-valued i64 literal)
     falls through to the general [0 - a] lowering below. Floats never overflow
     on negation. *)
  | UnOp ({ desc = Neg; _ }, ({ desc = Int n | Float n; _ } as a))
    when match expr_opt_valtype a with
         | Some I32 | None -> neg_int_const_fits 32 n
         | Some I64 -> neg_int_const_fits 64 n
         | _ -> true ->
      let n = "-" ^ n in
      folded loc
        (Const
           (match expr_opt_valtype a with
           | Some I32 | None -> I32 n
           | Some I64 -> I64 n
           | Some F32 -> F32 n
           | Some F64 -> F64 n
           | _ -> assert false))
        []
  | UnOp ({ desc = op; _ }, a) -> (
      let operand_type = expr_opt_valtype a in
      match (op, operand_type) with
      | Neg, (Some I32 | None) ->
          (* 0 - a *)
          let zero = folded loc (Const (I32 "0")) [] in
          let sub = Text.BinOp (I32 Sub) in
          folded loc sub (zero @ instruction ret ctx a)
      | Neg, Some I64 ->
          let zero = folded loc (Const (I64 "0")) [] in
          let sub = Text.BinOp (I64 Sub) in
          folded loc sub (zero @ instruction ret ctx a)
      | Neg, Some F32 -> folded loc (UnOp (F32 Neg)) (instruction ret ctx a)
      | Neg, Some F64 -> folded loc (UnOp (F64 Neg)) (instruction ret ctx a)
      | Not, (Some I32 | None) ->
          folded loc (UnOp (I32 Eqz)) (instruction ret ctx a)
      | Not, Some I64 -> folded loc (UnOp (I64 Eqz)) (instruction ret ctx a)
      (* Ref IsNull *)
      | Not, Some (Ref _) -> folded loc RefIsNull (instruction ret ctx a)
      | Pos, _ -> instruction ret ctx a
      | _, Some _ -> assert false)
  | Let (decls, None) ->
      let binding (id, ty) =
        match id with
        | Some name ->
            let ty = Option.get ty in
            let wasm_name = Namespace.add ctx.namespace name.Annot.desc in
            ctx.locals <- StringMap.add name.desc wasm_name ctx.locals;
            ctx.allocated_locals :=
              (Some { name with desc = wasm_name }, valtype ty)
              :: !(ctx.allocated_locals)
        | None -> assert false
      in
      List.iter binding (List.rev decls);
      []
  | Let ([ (id, ty) ], Some body) -> (
      (* Single binding: fold the initializer into the [local.set]. *)
      match id with
      | Some name ->
          (* Derive the local's type from the initializer when unannotated. In
             unreachable code the initializer's type is unknown; the local is
             then dead, so its declared type is irrelevant — fall back to [i32]
             (without raising) so the local is still registered and later reads
             of it resolve. *)
          let ty =
            match ty with
            | Some ty -> ty
            | None -> (
                match expr_opt_valtype body with Some t -> t | None -> I32)
          in
          (* Reserve the (possibly renamed) local and declare it now, keeping the
             declaration order unchanged, but bring the name into scope only
             *after* the initializer is lowered: a reference to [name] inside the
             initializer must still resolve to the outer binding it shadows (as
             the type checker scopes it), not to this new local. *)
          let wasm_name = Namespace.add ctx.namespace name.desc in
          ctx.allocated_locals :=
            (Some { name with desc = wasm_name }, valtype ty)
            :: !(ctx.allocated_locals);
          let code = instruction ret ctx body in
          ctx.locals <- StringMap.add name.desc wasm_name ctx.locals;
          folded loc
            (Text.LocalSet (annot name.Ast.info (Text.Id wasm_name)))
            code
      | None -> folded loc Text.Drop (instruction ret ctx body))
  | Let (decls, Some body) ->
      (* Multi-value initializer: evaluate it once, leaving one value per name
         on the stack, then store each into its local. The last value is on top,
         so the stores run in reverse declaration order. Allocate the locals in
         that same order, so a tuple [let] recovered from Wasm reproduces the
         original local declaration order on the way back. *)
      (* Anchor the [Let]'s location (and any leading comment) on the
         initializer, which is the first instruction emitted, rather than on the
         stores that follow it. Recovery ([merge_let_tuple]) rebuilds the tuple
         [let] at the initializer's location, so keeping the comment there makes
         it round-trip in place instead of drifting past the initializer. *)
      let code =
        match instruction ret ctx body with
        | head :: rest -> { head with info = loc } :: rest
        | [] -> []
      in
      let result_types = fst body.info in
      let store (idx, (id, ty)) =
        match id with
        | Some name ->
            let ty =
              match ty with
              | Some ty -> ty
              | None -> (
                  (* Unknown in unreachable code; the local is dead, so [i32]
                     keeps it valid (see the single-binding case). *)
                  match result_types.(idx) with
                  | Some t -> unpack_type t
                  | None -> I32)
            in
            let wasm_name = Namespace.add ctx.namespace name.Annot.desc in
            ctx.locals <- StringMap.add name.desc wasm_name ctx.locals;
            ctx.allocated_locals :=
              (Some { name with desc = wasm_name }, valtype ty)
              :: !(ctx.allocated_locals);
            folded name.info
              (Text.LocalSet (annot name.Ast.info (Text.Id wasm_name)))
              []
        | None -> folded loc Text.Drop []
      in
      code
      @ List.concat_map store
          (List.rev (List.mapi (fun idx decl -> (idx, decl)) decls))
  | Br (l, None) ->
      (*ZZZ label should be located*)
      folded loc (Br (label ret l)) []
  | Br (l, Some expr) ->
      folded loc (Br (label ret l)) (instruction ret ctx expr)
  | Br_if (l, expr) ->
      folded loc (Br_if (label ret l)) (instruction ret ctx expr)
  | Br_table (labels, expr) -> (
      let code = instruction ret ctx expr in
      match List.rev labels with
      | default_label_name :: other_labels_rev ->
          let default_idx = label ret default_label_name in
          let other_idx =
            List.rev_map (fun l -> label ret l) other_labels_rev
          in
          folded loc (Br_table (other_idx, default_idx)) code
      | _ -> assert false)
  | Dispatch { index; cases; default; arms } ->
      (* Lower to the conventional nested-block switch (a list: the outermost
         block then the first arm's trailing body) and convert each; the
         synthesised labels thread into [ret] via the recursive calls. *)
      List.concat_map (instruction ret ctx)
        (Wax_lang.Ast_utils.lower_dispatch ~block_info:i.info ~index ~cases
           ~default ~arms)
  | While { label; cond; step; block } ->
      (* Lower to the equivalent ['L: loop { if C { B; br 'L; } }] (with a
         continue-expression, an inner block runs the step on every iteration;
         see [Ast_utils.lower_while]) and convert. The synthesised loop label is
         a fresh readable [loop]/[loopN] avoiding the enclosing labels (threaded
         into [ret]), any label nested in the body, and the user's own label. *)
      let avoid =
        (match label with Some l -> [ l.desc ] | None -> [])
        @ labels_in_list ((cond :: Option.to_list step) @ block.desc)
      in
      let fresh_loop = Ast.no_loc (fresh_loop_label ret avoid) in
      List.concat_map (instruction ret ctx)
        (Wax_lang.Ast_utils.lower_while ~block_info:i.info ~fresh_loop ~label
           ~cond ~step ~block:block.desc)
  | Match { scrutinee; arms; default } ->
      (* Lower to the nested type-test ladder (see [Ast_utils.lower_match]) and
         convert each statement. Readable [arm]/[default] labels (one per arm,
         then the outer escape block) are picked fresh against the enclosing
         labels — see {!fresh_match_labels}.

         The synthesised wrapper instructions carry [block_info] holding the
         scrutinee's type: each threaded [br_on_cast] derives its source type
         from its operand's annotation, and every fall-through value in the chain
         stays a subtype of the scrutinee, so the scrutinee type is a valid
         source for them all. *)
      let block_info = ([| Some (expr_type scrutinee) |], loc) in
      let avoid =
        labels_in_list
          (default.desc @ List.concat_map (fun (_, b) -> b.Annot.desc) arms)
      in
      let labels =
        List.map
          (fun name -> { desc = name; info = loc })
          (fresh_match_labels ret ~avoid (List.length arms))
      in
      List.concat_map (instruction ret ctx)
        (Wax_lang.Ast_utils.lower_match ~block_info ~labels ~scrutinee ~arms
           ~default)
  | Br_on_null (l, expr) ->
      folded loc (Br_on_null (label ret l)) (instruction ret ctx expr)
  | Br_on_non_null (l, expr) ->
      folded loc (Br_on_non_null (label ret l)) (instruction ret ctx expr)
  | Br_on_cast (l, target_reftype, expr) ->
      folded loc
        (Br_on_cast
           ( label ret l,
             reftype (br_on_cast_source expr target_reftype),
             reftype target_reftype ))
        (instruction ret ctx expr)
  | Br_on_cast_fail (l, target_reftype, expr) ->
      folded loc
        (Br_on_cast_fail
           ( label ret l,
             reftype (br_on_cast_source expr target_reftype),
             reftype target_reftype ))
        (instruction ret ctx expr)
  | Br_on_cast_desc_eq (l, nullable, expr, d) ->
      let target_reftype = descriptor_cast_target ctx ~nullable d in
      folded loc
        (Br_on_cast_desc_eq
           ( label ret l,
             reftype (br_on_cast_source expr target_reftype),
             reftype target_reftype ))
        (instruction ret ctx expr @ instruction ret ctx d)
  | Br_on_cast_desc_eq_fail (l, nullable, expr, d) ->
      let target_reftype = descriptor_cast_target ctx ~nullable d in
      folded loc
        (Br_on_cast_desc_eq_fail
           ( label ret l,
             reftype (br_on_cast_source expr target_reftype),
             reftype target_reftype ))
        (instruction ret ctx expr @ instruction ret ctx d)
  | Throw (tag_idx, args) ->
      folded loc
        (Throw (index tag_idx))
        (List.concat_map (instruction ret ctx) args)
  | ThrowRef expr -> folded loc ThrowRef (instruction ret ctx expr)
  | ContNew (ct, f) -> folded loc (ContNew (index ct)) (instruction ret ctx f)
  | ContBind (src, dst, l) ->
      folded loc
        (ContBind (index src, index dst))
        (List.concat_map (instruction ret ctx) l)
  | Suspend (tag, l) ->
      folded loc (Suspend (index tag)) (List.concat_map (instruction ret ctx) l)
  | Resume (ct, handlers, l) ->
      folded loc
        (Resume (index ct, List.map (on_clause ret) handlers))
        (List.concat_map (instruction ret ctx) l)
  | ResumeThrow (ct, tag, handlers, l) ->
      folded loc
        (ResumeThrow (index ct, index tag, List.map (on_clause ret) handlers))
        (List.concat_map (instruction ret ctx) l)
  | ResumeThrowRef (ct, handlers, l) ->
      folded loc
        (ResumeThrowRef (index ct, List.map (on_clause ret) handlers))
        (List.concat_map (instruction ret ctx) l)
  | Switch (ct, tag, l) ->
      folded loc
        (Switch (index ct, index tag))
        (List.concat_map (instruction ret ctx) l)
  (* A parsed [on] clause is folded into the [Resume]/[ResumeThrow]/
     [ResumeThrowRef] it wraps by the typer, so it never reaches lowering. *)
  | On _ -> assert false
  | Return None -> folded loc Return []
  | Return (Some expr) -> folded loc Return (instruction ret ctx expr)
  | Sequence body -> List.concat_map (instruction ret ctx) body
  | Select (cond, then_, else_) ->
      let code_then = instruction ret ctx then_ in
      let code_else = instruction ret ctx else_ in
      let code_cond = instruction ret ctx cond in
      let typ =
        match expr_opt_valtype i with
        | None | Some (I32 | I64 | F32 | F64 | V128) -> None
        | Some typ -> Some [ valtype typ ]
      in
      folded loc (Select typ) (code_then @ code_else @ code_cond)
  | Char c -> folded loc (Char c) []
  | String (ty, s) ->
      (* When the type name was inferred from the context (so [ty] is omitted),
         recover it from the expression's type. A synthesized [<string>] type is
         the [mut i8] default that a bare [(@string "..")] already lowers to, so
         it stays omitted; a concrete inferred type (e.g. an immutable [chars])
         is pinned explicitly. *)
      let idx = match ty with Some idx -> idx | None -> expr_type_name i in
      let idx =
        if idx.desc <> "" && idx.desc.[0] = '<' then None else Some idx
      in
      folded loc
        (String (Option.map index idx, [ { desc = s; info = loc } ]))
        []
  | If_annotation { cond; then_body; else_body } ->
      let conv body = List.concat_map (instruction ret ctx) body in
      [
        with_loc loc
          (Text.If_annotation
             {
               cond;
               then_body = { then_body with Ast.desc = conv then_body.desc };
               else_body =
                 Option.map
                   (fun b -> { b with Ast.desc = conv b.Annot.desc })
                   else_body;
             });
      ]
  | Labelled _ ->
      (* Typing only accepts a labelled argument as a memory-access immediate,
         and the memory-access cases above consume the labels before lowering
         their operands, so one never reaches here. *)
      assert false

(*** Module-field conversion ***)

(* The export name carried by an [#[export]] attribute: the explicit
   [#[export = "nm"]] string, or the field's own Wax name ([~name]) for the bare
   form. *)
let export_name ~name v =
  match v with
  | Some ({ desc = String (_, n); _ } as v) -> annot v.info n
  | _ -> name

(* [#[export = "nm"]] exports under the given name; the bare [#[export]] reuses
   the field's own Wax name ([~name]). Only the unguarded exports become inline
   exports on the field; a guarded [#[export = "nm", if <cond>]] is emitted
   separately by [guarded_export_fields] as a conditional standalone export. *)
let exports ~name attributes =
  List.filter_map
    (fun ({ attr_name = k; attr_value = v; attr_guard = guard; _ } :
           Wax_lang.Ast.attribute) ->
      match (k, guard) with
      | "export", None -> Some (export_name ~name v)
      | _ -> None)
    attributes

(* Compilation-hints proposal: the function's [metadata.code.compilation_priority]
   entry, gathered from its attributes. [#[priority = n]] is what makes the entry
   exist at all — the section has no way to state an optimization priority without
   a compilation one — so an [#[optimization]]/[#[run_once]] without it is rejected
   by the typer, and dropped here rather than invented. *)
let compilation_priority attributes =
  let num v =
    match v with
    | Some { Wax_lang.Ast.desc = Wax_lang.Ast.Int n; _ } ->
        Some (int_of_string n)
    | _ -> None
  in
  let find k =
    List.find_opt
      (fun (a : Wax_lang.Ast.attribute) ->
        a.attr_name = k && a.attr_guard = None)
      attributes
  in
  match find "priority" with
  | None -> None
  | Some a ->
      let compilation = Option.value ~default:0 (num a.attr_value) in
      let optimization =
        match find "optimization" with
        | Some a -> num a.attr_value
        | None ->
            if find "run_once" <> None then Some Wax_wasm.Hints.run_once
            else None
      in
      Some { Wax_wasm.Hints.compilation; optimization }

(* The sibling module fields for the guarded exports of a field: each becomes a
   standalone [(export …)] wrapped in the conditional [(@if <cond> …)], so the
   export is present only when its guard holds -- independent of the field's own
   reachability. [field_name] indexes the exported entity, [kind] is its export
   sort. *)
let guarded_export_fields ~loc ~kind ~field_name attributes =
  List.filter_map
    (fun ({ attr_name = k; attr_value = v; attr_guard = guard; _ } :
           Wax_lang.Ast.attribute) ->
      match (k, guard) with
      | "export", Some cond ->
          let export : _ Text.modulefield =
            Text.Export
              {
                name = export_name ~name:field_name v;
                kind;
                index = index field_name;
              }
          in
          Some
            (annot loc
               (Text.Module_if_annotation
                  {
                    cond = cond.Ast.desc;
                    then_fields = annot loc [ annot loc export ];
                    else_fields = None;
                  }))
      | _ -> None)
    attributes

(* The standalone [(export …)] fields for a field's unguarded exports. A field
   normally carries these inline (in its [exports] list); a compact import group
   has no inline-export slot, so its items' unguarded exports are emitted as
   sibling fields instead, exactly as [guarded_export_fields] does for guarded
   ones. [field_name] indexes the exported entity, [kind] its export sort. *)
let inline_export_fields ~loc ~kind ~field_name attributes =
  List.map
    (fun name ->
      annot loc (Text.Export { name; kind; index = index field_name }))
    (exports ~name:field_name attributes)

(* The [(start $f)] field for a function's [#[start]] attribute: inline when
   unguarded, wrapped in [(@if <cond> …)] when guarded, like a guarded export. *)
let start_fields ~loc ~field_name attributes =
  List.filter_map
    (fun ({ attr_name = k; attr_guard = guard; _ } : Wax_lang.Ast.attribute) ->
      match (k, guard) with
      | "start", None -> Some (annot loc (Text.Start (index field_name)))
      | "start", Some cond ->
          Some
            (annot loc
               (Text.Module_if_annotation
                  {
                    cond = cond.Ast.desc;
                    then_fields =
                      annot loc [ annot loc (Text.Start (index field_name)) ];
                    else_fields = None;
                  }))
      | _ -> None)
    attributes

(* The module name carried by a [#![module = "name"]] inner attribute, if any.
   Lowered into the binary's module-name subsection (the WAT [(module $name)]),
   not into a module field. *)
let module_name attributes =
  List.find_map
    (fun (a : Wax_lang.Ast.attribute) ->
      match (a.attr_name, a.attr_value) with
      | "module", Some { desc = String (_, n); info; _ } ->
          Some { Ast.desc = n; info }
      | _ -> None)
    attributes

(* The features declared by [#![feature = "name"]] inner attributes, as
   [(@feature "name")] module fields (only top-level attributes count, matching
   the typer's [apply_declared_features]). *)
let feature_annotations fields =
  List.concat_map
    (fun (field : (_ modulefield, _) Ast.annotated) ->
      match field.desc with
      | Module_annotation attrs ->
          List.filter_map
            (fun (a : Wax_lang.Ast.attribute) ->
              match (a.attr_name, a.attr_value) with
              | "feature", Some { desc = String (_, n); info; _ } ->
                  Some
                    {
                      Ast.desc = Text.Feature_annotation { desc = n; info };
                      info;
                    }
              | _ -> None)
            attrs
      | _ -> [])
    fields

let globaltype mut t : Text.globaltype = { mut; typ = valtype t }

(* Smallest memory size (in 64KiB pages) that holds the declared active data
   segments, used when a memory omits explicit limits. Only literal offsets
   contribute; others are ignored. *)
(* Lower one Wax data-segment element to its WAT form: a string stays a string, a
   scalar run becomes a typed numlist, and a [v128] run a list of v128 constants.
   Every value is already a raw literal string. *)
let lower_data_elem (e : Wax_lang.Ast.data_elem) : Text.datavalelem =
  match e with
  | Data_string s -> Text.Str s
  | Data_run (st, values) ->
      Text.Numlist (Map.storagetype () st, List.map (fun v -> v.Ast.desc) values)
  | Data_v128 vs -> Text.V128list (List.map (fun v -> v.Ast.desc) vs)

let lower_data_init loc (init : Wax_lang.Ast.data_elem list) : Text.dataval =
  List.map (fun e -> { desc = lower_data_elem e; info = loc }) init

let derive_min_pages ~page_size_log2 (data : _ Wax_lang.Ast.memdata list) =
  (* The page size is [2^page_size_log2] bytes (default exponent 16, i.e. 64KiB);
     the custom-page-sizes proposal also allows exponent 0, a 1-byte page. The
     minimum must cover the highest active-data extent divided by *that* page
     size, or a small custom-page memory is derived too small and traps on every
     instantiation. Byte offsets and counts are unsigned 64-bit (memory64), so
     use unsigned compare/div and unsigned parsing throughout — a signed
     [max]/[div] would drop or misplace an offset at or above 2^63. *)
  let page_size =
    Int64.shift_left 1L (Option.value page_size_log2 ~default:16)
  in
  let extent =
    List.fold_left
      (fun acc (d : _ Wax_lang.Ast.memdata) ->
        match d.offset.desc with
        | Wax_lang.Ast.Int s -> (
            (* A memory64 offset can exceed the signed Int64 range; the [0u]
               prefix parses it as unsigned when the plain read overflows (hex
               already reads as the bit pattern, so it succeeds on the first
               try). *)
            let off =
              match Int64.of_string_opt s with
              | Some _ as v -> v
              | None -> Int64.of_string_opt ("0u" ^ s)
            in
            match off with
            | Some off ->
                let len =
                  Int64.of_int
                    (Wax_wasm.Misc.dataval_byte_length
                       (lower_data_init Wax_utils.Ast.dummy_loc d.init))
                in
                let e = Int64.add off len in
                (* [off + len] overflowing 2^64 means the segment runs past the
                   whole address space; treat it as maximal rather than letting
                   the wrap underestimate the minimum. *)
                let e = if Int64.unsigned_compare e off < 0 then -1L else e in
                if Int64.unsigned_compare e acc > 0 then e else acc
            | None -> acc)
        | _ -> acc)
      0L data
  in
  (* ceil(extent / page_size), computed without the [+ page_size - 1] that would
     overflow when extent is within a page of 2^64. *)
  let q = Int64.unsigned_div extent page_size in
  let pages =
    if Int64.equal (Int64.unsigned_rem extent page_size) 0L then q
    else Int64.add q 1L
  in
  Wax_utils.Uint64.of_int64
    (if Int64.unsigned_compare pages 1L < 0 then 1L else pages)

let storagetype ty = Map.storagetype () ty

let subtype s : Text.subtype =
  let typ : Text.comptype =
    match s.typ with
    | Func typ -> Func (functype typ)
    | Struct fields ->
        Struct
          (Array.map
             (fun field ->
               let name, { mut; typ } = field.Annot.desc in
               {
                 Ast.desc =
                   (Some name, { Text.Types.mut; typ = storagetype typ });
                 info = field.info;
               })
             fields)
    | Array { mut; typ } -> Array { mut; typ = storagetype typ }
    | Cont idx -> Cont (index idx)
  in
  {
    typ;
    supertype = Option.map index s.supertype;
    final = s.final;
    descriptor = Option.map index s.descriptor;
    describes = Option.map index s.describes;
  }

let module_has_conditional fields =
  let exception Found in
  try
    Wax_lang.Ast_utils.iter_fields
      (fun field ->
        match field.desc with Conditional _ -> raise Found | _ -> ())
      fields;
    false
  with Found -> true

(* Whether a leaf field introduces an index-consuming definition that imports
   must precede. Types, exports, [start] and elem/data segments do not.
   [Module_if_annotation] nodes are dissolved during flattening, so they never
   reach this classifier. *)
let reorder_defines (f : (_ Ast.Text.modulefield, _) Ast.annotated) =
  match f.desc with
  | Func _ | Memory _ | Table _ | Tag _ | Global _ | String_global _ -> true
  | Import _ | Import_group1 _ | Import_group2 _ | Types _ | Export _ | Start _
  | Elem _ | Data _ | Feature_annotation _ | Module_if_annotation _ ->
      false

let reorder_is_import (f : (_ Ast.Text.modulefield, _) Ast.annotated) =
  match f.desc with
  | Ast.Text.Import _ | Import_group1 _ | Import_group2 _ -> true
  | _ -> false

(* Hoist imports before definitions so the output validates ([import_after_
   definition] in [Validation]). This is guard-aware: nested
   [#[if]]/[Module_if_annotation] blocks are flattened into a sequence of
   [(guard, leaf)] pairs, where a guard is the path of frames — each a
   condition, the branch taken, and the source locations — accumulated while
   descending. Import-like leaves are stably moved to the front carrying their
   guards; every other leaf keeps its relative order. The sequence is then
   rebuilt, merging consecutive entries with an identical guard path back into
   (nested) blocks. For every assignment of the condition variables this yields
   the same module as hoisting the specialized fields directly. *)
let reorder_imports lst =
  let flatten fields =
    let rec go guard acc
        (fields : (_ Ast.Text.modulefield, _) Ast.annotated list) =
      List.fold_left
        (fun acc (f : (_ Ast.Text.modulefield, _) Ast.annotated) ->
          match f.desc with
          | Ast.Text.Module_if_annotation { cond; then_fields; else_fields } ->
              let acc =
                go
                  (guard @ [ (cond, `Then, f.info, then_fields.Ast.info) ])
                  acc then_fields.Ast.desc
              in
              Option.fold ~none:acc
                ~some:(fun e ->
                  go
                    (guard @ [ (cond, `Else, f.info, e.Ast.info) ])
                    acc e.Ast.desc)
                else_fields
          | _ -> (guard, f) :: acc)
        acc fields
    in
    List.rev (go [] [] fields)
  in
  let flat = flatten lst in
  (* Two guard paths are mutually exclusive when they enter a shared branch
     point on opposite branches: comparing frames in lockstep from the root, if
     the conditions are structurally equal but the branches differ the leaves
     never coexist. (Once the conditions differ the leaves are in unrelated
     subtrees, so no deeper frame can be shared.) This is not condition-value
     satisfiability — [debug] and [not(debug)] are treated as independent — but
     it does keep a then-branch definition from counting as preceding an
     else-branch import of the same [#[if]]. *)
  let rec mutually_exclusive g1 g2 =
    match (g1, g2) with
    | (c1, b1, _, _) :: r1, (c2, b2, _, _) :: r2 ->
        if c1 = c2 then if b1 <> b2 then true else mutually_exclusive r1 r2
        else false
    | _ -> false
  in
  (* No-op unless some import-like leaf follows a non-mutually-exclusive
     defining leaf; this keeps currently-working modules byte-identical. *)
  let rec needs_reorder def_guards = function
    | [] -> false
    | (g, f) :: rem ->
        if reorder_is_import f then
          List.exists (fun dg -> not (mutually_exclusive dg g)) def_guards
          || needs_reorder def_guards rem
        else
          let def_guards =
            if reorder_defines f then g :: def_guards else def_guards
          in
          needs_reorder def_guards rem
  in
  if not (needs_reorder [] flat) then lst
  else
    let imports, others =
      List.partition (fun (_, f) -> reorder_is_import f) flat
    in
    let partitioned = imports @ others in
    (* Wrap [fields] in the nested [Module_if_annotation] blocks named by
       [guard], reusing the original locations. *)
    let rec wrap guard fields =
      match guard with
      | [] -> fields
      | (cond, branch, node_loc, branch_loc) :: rest ->
          let inner = { Ast.desc = wrap rest fields; info = branch_loc } in
          let desc =
            match branch with
            | `Then ->
                Ast.Text.Module_if_annotation
                  { cond; then_fields = inner; else_fields = None }
            | `Else ->
                Ast.Text.Module_if_annotation
                  {
                    cond;
                    then_fields = { Ast.desc = []; info = Ast.dummy_loc };
                    else_fields = Some inner;
                  }
          in
          [ { Ast.desc; info = node_loc } ]
    in
    let rec span guard = function
      | (g, f) :: rem when g = guard ->
          let same, rest = span guard rem in
          (f :: same, rest)
      | l -> ([], l)
    in
    let rec rebuild = function
      | [] -> []
      | (guard, _) :: _ as l ->
          let same, rest = span guard l in
          wrap guard same @ rebuild rest
    in
    rebuild partitioned

let module_ ?(features = Wax_utils.Feature.default ()) diagnostics types fields
    =
  Wax_utils.Debug.timed "convert" @@ fun () ->
  let func_refs_in_func = Hashtbl.create 16 in
  let func_refs_outside_func = Hashtbl.create 16 in
  let ctx =
    {
      globals = Hashtbl.create 16;
      functions = Hashtbl.create 16;
      memories = Hashtbl.create 16;
      tables = Hashtbl.create 16;
      elems = Hashtbl.create 16;
      datas = Hashtbl.create 16;
      locals = StringMap.empty;
      allocated_locals = ref [];
      namespace = Namespace.make ();
      type_kinds = Hashtbl.create 16;
      cont_types = Hashtbl.create 16;
      struct_fields = Hashtbl.create 16;
      referenced_functions = Hashtbl.create 16;
      extra_types = Hashtbl.create 16;
      reuse_types = Hashtbl.create 16;
      types;
      diagnostics;
    }
  in
  (* A [..] splice keeps its sentinel in the module AST; the full fields live in
     the (expanded) type table. Resolve the expanded subtype for a spliced struct
     so lowering sees the inherited fields; every other type is already complete
     in the AST and passes through untouched. *)
  let resolve_subtype idx (s : subtype) =
    match s.typ with
    | Struct fields
      when Array.length fields > 0 && Wax_lang.Ast.is_splice_field fields.(0)
      -> (
        match
          Wax_lang.Typing.get_type_definition ctx.diagnostics ctx.types idx
        with
        | Some s' -> s'
        | None -> s)
    | _ -> s
  in
  let register_import (decl : Wax_lang.Ast.import_decl) =
    match decl.kind with
    | Import_func _ -> Hashtbl.replace ctx.functions decl.id.desc ()
    | Import_global _ -> Hashtbl.replace ctx.globals decl.id.desc ()
    | Import_memory _ -> Hashtbl.replace ctx.memories decl.id.desc ()
    | Import_table { reftype = rt; _ } ->
        Hashtbl.replace ctx.tables decl.id.desc rt
    | Import_tag _ -> ()
  in
  Wax_lang.Ast_utils.iter_fields
    (fun field ->
      match field.desc with
      | Type rectype ->
          Array.iter
            (fun rt ->
              let idx, subtype = rt.Annot.desc in
              let subtype = resolve_subtype idx subtype in
              let kind =
                match subtype.typ with
                | Func _ -> `Func
                | Cont _ ->
                    Hashtbl.replace ctx.cont_types idx.desc ();
                    `Func
                | Array _ -> `Array
                | Struct fields ->
                    let field_names =
                      Array.to_list
                        (Array.map
                           (fun field -> (field_name field).desc)
                           fields)
                    in
                    Hashtbl.add ctx.struct_fields idx.desc field_names;
                    `Struct
              in
              Hashtbl.add ctx.type_kinds idx.desc kind)
            rectype
      | Func { name; _ } -> Hashtbl.replace ctx.functions name.desc ()
      | Global { name; _ } -> Hashtbl.replace ctx.globals name.desc ()
      | Import { decl; _ } -> register_import decl.desc
      | Import_group { decls; _ } ->
          List.iter (fun d -> register_import d.Annot.desc) decls
      | Memory { name; _ } -> Hashtbl.replace ctx.memories name.desc ()
      | Table { name; reftype = rt; _ } ->
          Hashtbl.replace ctx.tables name.desc rt
      | Elem { name; _ } -> Hashtbl.replace ctx.elems name.desc ()
      | Data { name; _ } ->
          Option.iter (fun n -> Hashtbl.replace ctx.datas n.Annot.desc ()) name
      | Tag _ | Conditional _ | Module_annotation _ -> ())
    fields;
  (* Record unconditionally-declared types as reuse targets for synthesized
     types. Descend into [Group] (always present) but not [Conditional]: a type
     guarded by [#[if]] is not available everywhere a synthesized type like
     [<string>] is referenced, so reusing it could leave a dangling reference. *)
  let collect_reuse_types fields =
    let aux acc fields =
      List.fold_left
        (fun acc (field : (_ modulefield, _) Ast.Annot.annotated) ->
          match field.desc with
          | Type rectype ->
              Array.fold_left
                (fun acc rt ->
                  let idx, subtype = rt.Annot.desc in
                  let subtype = resolve_subtype idx subtype in
                  if idx.desc <> "" && idx.desc.[0] <> '<' then
                    (subtype, idx.desc) :: acc
                  else acc)
                acc rectype
          | _ -> acc)
        acc fields
    in
    aux [] fields
  in
  (* Top-level types are available everywhere, so record them once and keep the
     first declaration of each shape. *)
  List.iter
    (fun (subtype, name) ->
      if not (Hashtbl.mem ctx.reuse_types subtype) then
        Hashtbl.add ctx.reuse_types subtype name)
    (collect_reuse_types fields);
  (* Convert [flds] with that scope's declared types added as reuse targets
     (innermost wins via [Hashtbl.add]/[remove]), then restore the scope. *)
  let scoped flds f =
    let entries = collect_reuse_types flds in
    List.iter (fun (s, n) -> Hashtbl.add ctx.reuse_types s n) entries;
    Fun.protect
      ~finally:(fun () ->
        List.iter (fun (s, _) -> Hashtbl.remove ctx.reuse_types s) entries)
      f
  in
  (* Now that the top-level types are recorded, install the synthesized-type
     remapping used by [index] while converting. *)
  type_remap := make_type_remap ctx;
  (* With compact-import-section enabled, an [import "m" { … }] block of ≥2 items
     lowers to one compact group entry; otherwise (and always without the
     feature) each item lowers to an individual [Text.Import]. *)
  let compact_imports =
    Wax_utils.Feature.is_enabled features
      Wax_utils.Feature.Compact_import_section
  in
  (* The lowered [Text.importdesc] and export sort of one import declaration. *)
  let import_desc_and_kind (decl : import_decl) :
      Text.importdesc * Text.exportable =
    let import_limits limits address_type ~shared ~page_size_log2 : Ast.limits =
      let mi, ma =
        match limits with
        | Some (mi, ma) -> (mi, ma)
        | None -> (Wax_utils.Uint64.of_int 0, None)
      in
      { mi; ma; address_type; page_size_log2; shared }
    in
    let desc : Text.importdesc =
      match decl.kind with
      | Import_func { typ; sign; exact } ->
          Func { exact; typ = typeuse typ sign }
      | Import_global { mut; typ } -> Global (globaltype mut typ)
      | Import_tag { typ; sign } -> Tag (typeuse typ sign)
      | Import_memory { address_type; limits; page_size_log2; shared } ->
          Memory
            (Ast.no_loc
               (import_limits limits address_type ~shared ~page_size_log2))
      | Import_table { address_type; reftype = rt; limits } ->
          Table
            {
              limits =
                Ast.no_loc
                  (import_limits limits address_type ~shared:false
                     ~page_size_log2:None);
              reftype = reftype rt;
            }
    in
    let export_kind : Text.exportable =
      match decl.kind with
      | Import_func _ -> Func
      | Import_global _ -> Global
      | Import_tag _ -> Tag
      | Import_memory _ -> Memory
      | Import_table _ -> Table
    in
    (desc, export_kind)
  in
  (* The sibling fields an import's attributes require, emitted after the import
     itself: its [#[start]] (function imports only) and its guarded exports. *)
  let import_sibling_fields ~loc ~kind ~field_name attributes =
    start_fields ~loc ~field_name attributes
    @ guarded_export_fields ~loc ~kind ~field_name attributes
  in
  (* Lower one entry of an [import "module" { ... }] block to a [Text.Import]
     (carrying its inline unguarded exports) plus its sibling fields. *)
  let lower_import module_ (d : (import_decl, location) annotated) =
    let decl = d.desc in
    let name = decl.id in
    let import_name = Wax_lang.Ast_utils.import_name decl in
    let exports = exports ~name decl.attributes in
    let desc, export_kind = import_desc_and_kind decl in
    ( {
        desc =
          Text.Import
            { module_; name = import_name; id = Some name; desc; exports };
        info = d.info;
      },
      import_sibling_fields ~loc:d.info ~kind:export_kind ~field_name:name
        decl.attributes )
  in
  (* Lower an [import "m" { … }] block (≥2 items) to one compact group entry.
     A group carries no inline [exports] slot, so an item's unguarded exports
     become standalone [(export …)] fields (by the item's id) alongside its other
     sibling fields, all emitted after the group so it stays one entry. Every
     item binds its wax name as an id and the shared-type [Import_group2] text
     form is strictly name-only, so the group is always a per-item
     [Import_group1]; the binary encoder still uses the shared-type encoding
     when every item's type agrees. *)
  let lower_import_group module_ loc decls =
    let items =
      List.map
        (fun (d : (import_decl, location) annotated) ->
          let decl = d.desc in
          let name = decl.id in
          let import_name = Wax_lang.Ast_utils.import_name decl in
          let desc, export_kind = import_desc_and_kind decl in
          let siblings =
            inline_export_fields ~loc:d.info ~kind:export_kind ~field_name:name
              decl.attributes
            @ import_sibling_fields ~loc:d.info ~kind:export_kind
                ~field_name:name decl.attributes
          in
          (import_name, Some name, desc, siblings))
        decls
    in
    let group : _ Text.modulefield =
      Import_group1
        { module_; items = List.map (fun (n, id, d, _) -> (n, id, d)) items }
    in
    annot loc group :: List.concat_map (fun (_, _, _, s) -> s) items
  in
  let rec convert_fields fields =
    List.concat_map
      (fun (field : (_ modulefield, _) Ast.Annot.annotated) ->
        match field.desc with
        | Import { module_; decl } ->
            let import, guarded = lower_import module_ decl in
            import :: guarded
        | Import_group { module_; decls } ->
            if compact_imports && List.length decls >= 2 then
              lower_import_group module_ field.info decls
            else
              (* Feature off, or a singleton block (which cannot round-trip as a
                 compact group — [group_imports] only forms blocks from ≥2):
                 flatten to individual imports. Emit every import before any
                 sibling field so the run stays contiguous and re-groups back. *)
              let imports = List.map (lower_import module_) decls in
              List.map fst imports @ List.concat_map snd imports
        (* The module name is lowered separately into the name section; the
           annotation itself produces no module field. *)
        | Module_annotation _ -> []
        | Memory
            {
              name;
              address_type;
              limits;
              page_size_log2;
              shared;
              data;
              attributes;
            } ->
            let exports = exports ~name attributes in
            let limits_value : Ast.limits =
              match limits with
              | Some (mi, ma) ->
                  { mi; ma; address_type; page_size_log2; shared }
              | None ->
                  {
                    mi = derive_min_pages ~page_size_log2 data;
                    ma = None;
                    address_type;
                    page_size_log2;
                    shared;
                  }
            in
            let memory_field =
              Text.Memory
                {
                  id = Some name;
                  limits = Ast.no_loc limits_value;
                  init = None;
                  exports;
                }
            in
            let ictx =
              { ctx with referenced_functions = func_refs_outside_func }
            in
            let data_fields =
              List.map
                (fun (d : _ Wax_lang.Ast.memdata) ->
                  {
                    field with
                    desc =
                      Text.Data
                        {
                          id = d.data_name;
                          init = lower_data_init field.info d.init;
                          mode =
                            Active (index name, instruction no_ret ictx d.offset);
                        };
                  })
                data
            in
            let guarded =
              guarded_export_fields ~loc:field.info ~kind:Text.Memory
                ~field_name:name attributes
            in
            ({ field with desc = memory_field } :: guarded) @ data_fields
        | Data { name; mode; init; _ } ->
            let mode : _ Text.datamode =
              match mode with
              | Passive -> Passive
              | Active (mem, off) ->
                  let ictx =
                    { ctx with referenced_functions = func_refs_outside_func }
                  in
                  Active (index mem, instruction no_ret ictx off)
            in
            [
              {
                field with
                desc =
                  Text.Data
                    { id = name; init = lower_data_init field.info init; mode };
              };
            ]
        | Table { name; address_type; reftype = rt; limits; init; attributes }
          ->
            let exports = exports ~name attributes in
            let mi, ma =
              match limits with
              | Some (mi, ma) -> (mi, ma)
              | None -> (Wax_utils.Uint64.of_int 0, None)
            in
            let typ : Text.tabletype =
              {
                limits =
                  Ast.no_loc
                    {
                      Ast.mi;
                      ma;
                      address_type;
                      page_size_log2 = None;
                      shared = false;
                    };
                reftype = reftype rt;
              }
            in
            let init_value : _ Text.tableinit =
              match init with
              | None -> Init_default
              | Some e ->
                  let ictx =
                    { ctx with referenced_functions = func_refs_outside_func }
                  in
                  Init_expr (instruction no_ret ictx e)
            in
            let table_field =
              Text.Table { id = Some name; typ; init = init_value; exports }
            in
            { field with desc = table_field }
            :: guarded_export_fields ~loc:field.info ~kind:Text.Table
                 ~field_name:name attributes
        | Elem { name; reftype = rt; mode; init; _ } ->
            let ictx =
              { ctx with referenced_functions = func_refs_outside_func }
            in
            let mode : _ Text.elemmode =
              match mode with
              | EPassive -> Passive
              | EActive (tab, off) ->
                  Active (index tab, instruction no_ret ictx off)
            in
            let init = List.map (fun e -> instruction no_ret ictx e) init in
            [
              {
                field with
                desc =
                  Text.Elem { id = Some name; typ = reftype rt; init; mode };
              };
            ]
        | Conditional { cond; then_fields; else_fields } ->
            (* A branch's declared types are in scope only within it, so add
               them while converting it (see [scoped]); a synthesized type
               referenced there can then reuse a conditionally-declared one. *)
            let conv_branch flds =
              scoped flds (fun () -> convert_fields flds)
            in
            [
              {
                field with
                desc =
                  Text.Module_if_annotation
                    {
                      cond;
                      then_fields =
                        {
                          then_fields with
                          Ast.desc = conv_branch then_fields.desc;
                        };
                      else_fields =
                        Option.map
                          (fun b ->
                            { b with Ast.desc = conv_branch b.Annot.desc })
                          else_fields;
                    };
              };
            ]
        | _ ->
            let desc =
              match field.desc with
              | Type rectype ->
                  Text.Types
                    (Array.map
                       (fun rt ->
                         let idx, s = rt.Annot.desc in
                         Ast.no_loc (Some idx, subtype (resolve_subtype idx s)))
                       rectype)
              | Global { name; mut; typ; def; attributes } ->
                  let typ =
                    match typ with
                    | Some typ -> typ
                    | None ->
                        (*ZZZ *)
                        expr_valtype def
                  in
                  let init =
                    let ctx =
                      { ctx with referenced_functions = func_refs_outside_func }
                    in
                    instruction no_ret ctx def
                  in
                  Text.Global
                    {
                      id = Some name;
                      typ = globaltype mut typ;
                      init;
                      exports = exports ~name attributes;
                    }
              | Tag { name; typ; sign; attributes } ->
                  let exports = exports ~name attributes in
                  Text.Tag { id = Some name; typ = typeuse typ sign; exports }
              | Func { name; sign; typ; body = label, instrs; attributes } ->
                  let namespace = Namespace.make () in
                  let allocated_locals = ref [] in
                  let locals =
                    Array.fold_left
                      (fun locals p ->
                        match param_name p with
                        | Some id ->
                            let wasm_name = Namespace.add namespace id.desc in
                            StringMap.add id.desc wasm_name locals
                        | None -> locals)
                      StringMap.empty
                      (match sign with
                      | Some sign -> sign.params
                      | None -> [||])
                  in
                  let ctx =
                    {
                      ctx with
                      namespace;
                      allocated_locals;
                      locals;
                      referenced_functions = func_refs_in_func;
                    }
                  in
                  let instrs =
                    List.concat_map
                      (instruction
                         {
                           return =
                             Option.map
                               (fun (l : Wax_lang.Ast.ident) -> (l.desc, 0))
                               label;
                           labels =
                             (match label with
                             | Some l -> [ l.desc ]
                             | None -> []);
                         }
                         ctx)
                      instrs
                  in
                  let func_locals = List.rev !allocated_locals in
                  Text.Func
                    {
                      id = Some name;
                      typ = typeuse typ sign;
                      locals = List.map Ast.no_loc func_locals;
                      instrs;
                      exports = exports ~name attributes;
                      priority = compilation_priority attributes;
                    }
              | Import _ | Import_group _ | Conditional _ | Memory _ | Data _
              | Table _ | Elem _ | Module_annotation _ ->
                  assert false
            in
            let field' = { field with desc } in
            (* Guarded exports become standalone conditional exports after the
               field (see [guarded_export_fields]). *)
            let guarded =
              match field.desc with
              | Func { name; attributes; _ } ->
                  guarded_export_fields ~loc:field.info ~kind:Text.Func
                    ~field_name:name attributes
              | Global { name; attributes; _ } ->
                  guarded_export_fields ~loc:field.info ~kind:Text.Global
                    ~field_name:name attributes
              | Tag { name; attributes; _ } ->
                  guarded_export_fields ~loc:field.info ~kind:Text.Tag
                    ~field_name:name attributes
              | _ -> []
            in
            (* A [#[start]] function also emits a [(start $f)] field, guarded the
               same way as a conditional export. *)
            let start =
              match field.desc with
              | Func { name; attributes; _ } ->
                  start_fields ~loc:field.info ~field_name:name attributes
              | _ -> []
            in
            (field' :: start) @ guarded)
      fields
  in
  let wasm_fields = convert_fields fields in
  let extra_types =
    Hashtbl.fold
      (fun _ (idx, s) rem ->
        Ast.no_loc (Text.Types [| Ast.no_loc (Some idx, subtype s) |]) :: rem)
      ctx.extra_types []
  in
  (* The declarative element segment that makes funcrefs valid is emitted once,
     unconditionally, at module level. When the module has [#[if]] fields a
     referenced function may itself be conditionally defined, so the segment
     would reference an index that is absent under some configuration. Until the
     segment can be gated per condition, skip it entirely for conditional
     modules: the conditional WAT this produces is Wax-only text, and to obtain
     spec-consumable plain WAT from such a module, resolve the conditionals with
     [-D] and emit with [--desugar], which synthesises the segment over the
     specialised output (see [Wax_wasm.Desugar] / [Wax_wasm.Declare_refs]). *)
  let has_conditional = module_has_conditional fields in
  let elem_declare : (_ Text.modulefield, _) Ast.annotated list =
    let funcs =
      Hashtbl.fold
        (fun k _ acc ->
          if Hashtbl.mem func_refs_outside_func k then acc else k :: acc)
        func_refs_in_func []
    in
    if has_conditional || funcs = [] then []
    else
      let init =
        List.map
          (fun name ->
            [ Text.no_loc (Text.RefFunc (Ast.no_loc (Text.Id name))) ])
          funcs
      in
      [
        Ast.no_loc
          (Text.Elem
             {
               id = None;
               typ = { nullable = false; typ = Func };
               init;
               mode = Declare;
             });
      ]
  in
  let wasm_fields = wasm_fields @ extra_types @ elem_declare in
  let wasm_fields = reorder_imports wasm_fields in
  (* Each [#![feature = "name"]] inner attribute becomes a leading
     [(@feature "name")] annotation, so the emitted module stays
     self-describing. *)
  let wasm_fields = feature_annotations fields @ wasm_fields in
  (* A [#![module = "name"]] inner attribute names the module; carry it into the
     text module's name slot (typing has already ensured at most one). *)
  let mod_name =
    let found = ref None in
    Wax_lang.Ast_utils.iter_fields
      (fun field ->
        match field.desc with
        | Module_annotation attrs ->
            if !found = None then found := module_name attrs
        | _ -> ())
      fields;
    !found
  in
  (mod_name, wasm_fields)
