open Wax_lang
module Src = Wax_wasm.Ast.Text
module Simd = Wax_wasm.Simd
module Atomics = Wax_wasm.Atomics
module Uint32 = Wax_utils.Uint32
module Cond = Wax_wasm.Cond_solver

(* Raised by [Sequence.get] for a numeric field reference in a module with
   conditional annotations: the field's index depends on which branch is taken,
   so it cannot be resolved to a single Wax name. Caught in [module_] and
   reported as a located diagnostic. *)
exception Numeric_ref_in_conditional of Wax_wasm.Ast.location

(* Raised when an index or label reference resolves to nothing — it is out of
   range, or names an undeclared entity. This only happens on a module that
   validation would reject (with an "unknown ..." error), so conversion gives up
   rather than inventing a target. *)
exception Unresolved_reference of Wax_wasm.Ast.location

(*** Symbol tables and stacks ***)

module Sequence = struct
  type t = {
    index_mapping : (Uint32.t, string) Hashtbl.t;
    label_mapping : (string, string) Hashtbl.t;
    export_mapping : (string, string) Hashtbl.t;
    mutable last_index : int;
    mutable current_index : int;
    namespace : Namespace.t;
    default : string;
    forbid_numeric : bool;
        (* When set (module-level sequences of a module containing conditional
           annotations), numeric references are refused: a field's index depends
           on which branch is taken, so it cannot be resolved to one name. *)
    is_conditional : bool;
    diagnostics : Wax_utils.Diagnostic.context option;
        (* Where to report a [naming-conflict] / [reserved-word-rename] warning
           when a source name has to be renamed; [None] silences them (for
           internal namespaces without a source identifier to point at). *)
  }

  let make ?(forbid_numeric = false) ?is_conditional ?diagnostics namespace
      default =
    let is_conditional = Option.value ~default:forbid_numeric is_conditional in
    {
      index_mapping = Hashtbl.create 16;
      label_mapping = Hashtbl.create 16;
      export_mapping = Hashtbl.create 16;
      last_index = 0;
      current_index = 0;
      namespace;
      default;
      forbid_numeric;
      is_conditional;
      diagnostics;
    }

  (* Report that the source name [original] had to be renamed to [renamed]
     (because it is a reserved word, or collides with another name), pointing at
     the source identifier. For a collision, [previous] (when known) points the
     related label at the occurrence that first claimed the name. *)
  let report_rename diagnostics ~location ~previous ~reserved ~original ~renamed
      =
    let warning, message =
      if reserved then
        ( Wax_utils.Warning.Reserved_word_rename,
          Wax_utils.Message.text
            (Printf.sprintf
               "'%s' is a reserved word; renaming this identifier to '%s'."
               original renamed) )
      else
        ( Wax_utils.Warning.Naming_conflict,
          Wax_utils.Message.text
            (Printf.sprintf
               "The name '%s' is already in use; renaming this occurrence to \
                '%s'."
               original renamed) )
    in
    let related =
      match previous with
      | Some location ->
          [
            {
              Wax_utils.Diagnostic.location;
              message =
                Wax_utils.Message.text
                  (Printf.sprintf "'%s' first claimed here" original);
            };
          ]
      | None -> []
    in
    Wax_utils.Diagnostic.report diagnostics ~location ~severity:Warning ~warning
      ~related ~message ()

  let register' ?hint ?claimed seq export_tbl (kind : Src.exportable option)
      (id : Src.name option) exports =
    let idx = Uint32.of_int seq.last_index in
    (* The same entity may already have been registered in another branch of a
       conditional. Its identity is the [$id] or, lacking one, a shared export
       name (export names are unique per resolved module, so a collision can
       only mean mutually-exclusive branches). Reuse the Wax name so references
       stay coherent, but still consume an index slot below so positional naming
       via [get_current] stays aligned with the conversion order. This only
       applies to module-level sequences of a conditional module
       ([forbid_numeric]); locals reuse a single sequence across functions,
       where a repeated [$id] is a distinct variable, not the same entity. *)
    let reused =
      if seq.is_conditional then
        match id with
        | Some nm ->
            (* An explicit [$id] is authoritative: it is reused only when the
               same id was already bound in another branch. Do not fall back to
               export-name matching, which would conflate this entity with a
               different one that merely shares an export name in a
               mutually-exclusive branch (e.g. [$unix_isatty] versus the
               imported [$isatty], both exporting [unix_isatty]). *)
            Hashtbl.find_opt seq.label_mapping nm.Ast.desc
        | None ->
            let found =
              List.find_map
                (fun nm ->
                  Hashtbl.find_opt seq.export_mapping nm.Wax_utils.Ast.desc)
                exports
            in
            if Option.is_none found && not seq.forbid_numeric then
              Hashtbl.find_opt seq.index_mapping Uint32.zero
            else found
      else None
    in
    (* A source name already claimed by the caller's priority pass (see the
       local sequence's pre-pass): it is reserved in the namespace under this
       name and any rename was already reported, so take it as-is. This lets a
       real source name win the plain name over a generated default. *)
    let pre_claimed =
      match (claimed, id) with
      | Some tbl, Some nm -> Hashtbl.find_opt tbl nm.Ast.desc
      | _ -> None
    in
    let name =
      match (reused, pre_claimed) with
      | Some name, _ | _, Some name -> name
      | None, None ->
          (* [src] is the source identifier the name was taken from (with its
             location), or [None] for a synthesized default; only a renamed
             source identifier is worth a warning. *)
          (* An inferred name -- an export name, or the import-name / parent-field
             [hint] -- is usable only when it is a valid Wax identifier that is
             not a keyword: borrowing a keyword would force a suffixed rename
             (e.g. [memory_2]) that reads worse than the generated default. An
             explicit [$id] is authoritative and kept as-is even when it is a
             keyword (it is renamed with a warning, as before). *)
          let usable_inferred nm =
            Lexer.is_valid_identifier nm.Wax_utils.Ast.desc
            && not (Namespace.is_reserved seq.namespace nm.Ast.desc)
          in
          let default_or_hint () =
            match hint with
            | Some h when not (Namespace.is_reserved seq.namespace h) ->
                (h, None)
            | _ -> (seq.default, None)
          in
          let candidate, src =
            match (id, exports) with
            | Some nm, _ when Lexer.is_valid_identifier nm.Ast.desc ->
                (nm.Ast.desc, Some nm)
            | None, nm :: _ when usable_inferred nm -> (nm.Ast.desc, Some nm)
            | _ -> (
                match kind with
                | None -> default_or_hint ()
                | Some kind -> (
                    match Hashtbl.find_opt export_tbl (kind, Src.Num idx) with
                    | Some (nm :: _) when usable_inferred nm ->
                        (nm.Ast.desc, Some nm)
                    | _ -> default_or_hint ()))
          in
          let name, outcome =
            match src with
            | Some nm -> Namespace.add' ~loc:nm.Ast.info seq.namespace candidate
            | None -> Namespace.add' seq.namespace candidate
          in
          (match (src, outcome, seq.diagnostics) with
          | Some nm, Namespace.Renamed { reserved; previous }, Some diagnostics
            ->
              report_rename diagnostics ~location:nm.Ast.info ~previous
                ~reserved ~original:candidate ~renamed:name
          | _ -> ());
          name
    in
    seq.last_index <- seq.last_index + 1;
    Hashtbl.add seq.index_mapping idx name;
    Option.iter
      (fun id -> Hashtbl.replace seq.label_mapping id.Wax_utils.Ast.desc name)
      id;
    (* Record only the head export as this entity's cross-branch identity, not
       every export: a single multi-export function in one branch may correspond
       to several distinct single-export functions in another (e.g. one wasi
       function exporting [unix_getuid]/[unix_geteuid]/… versus one function per
       id elsewhere). Recording all of them would let each sibling match and
       reuse this one name, binding the same Wax name twice in that branch. *)
    (match exports with
    | nm :: _ -> Hashtbl.replace seq.export_mapping nm.Ast.desc name
    | [] -> ());
    name

  let register ?hint ?claimed seq export_tbl kind id exports =
    ignore (register' ?hint ?claimed seq export_tbl kind id exports)

  (* Claim source name [candidate] in the namespace ahead of positional
     registration, reporting a rename (reserved word, or a collision with an
     already-claimed name) exactly as [register'] would. Returns the final,
     possibly-renamed name. Used to give real source names priority over the
     generated default before any unnamed entity is registered. *)
  let claim_name seq ~loc candidate =
    let name, outcome = Namespace.add' ~loc seq.namespace candidate in
    (match (outcome, seq.diagnostics) with
    | Namespace.Renamed { reserved; previous }, Some diagnostics ->
        report_rename diagnostics ~location:loc ~previous ~reserved
          ~original:candidate ~renamed:name
    | _ -> ());
    name

  let get seq (idx : Src.idx) =
    {
      idx with
      desc =
        (match idx.desc with
        | Num n -> (
            if seq.forbid_numeric then
              raise (Numeric_ref_in_conditional idx.Ast.info);
            match Hashtbl.find_opt seq.index_mapping n with
            | Some name -> name
            | None -> raise (Unresolved_reference idx.Ast.info))
        | Id id -> (
            match Hashtbl.find_opt seq.label_mapping id with
            | Some name -> name
            | None -> raise (Unresolved_reference idx.Ast.info)));
    }

  let get_current seq =
    let i = seq.current_index in
    seq.current_index <- i + 1;
    Ast.no_loc (Hashtbl.find seq.index_mapping (Uint32.of_int i))

  (* A fresh, unique name in this sequence's namespace, for an entity not in the
     source (e.g. an element segment synthesised from an inline table init). *)
  let fresh_name seq = Ast.no_loc (Namespace.add seq.namespace seq.default)

  (* Bind [name] at a specific [idx], for an entity materialised on demand
     outside the normal registration order — an implicit (inline-signature) type
     first referenced from a ref-type position (see [type_ref_name]). *)
  let find_bound seq idx = Hashtbl.find_opt seq.index_mapping idx
  let bind_at seq idx name = Hashtbl.replace seq.index_mapping idx name
  let mint_name seq = Namespace.add seq.namespace seq.default
  let consume_currents seq = seq.current_index <- seq.last_index

  (* Consume an index slot without binding a name, for an entity rendered
     anonymously (a [_] parameter). Later positional references stay aligned. *)
  let skip seq = seq.last_index <- seq.last_index + 1
end

(* Turn a Wasm identifier into a valid Wax identifier. Wasm identifiers are
   ASCII (see the Wasm lexer's [idchar]), so every character Wax does not accept
   in an identifier is mapped to an underscore ([$label$n] -> [label_n]), then
   one more is prefixed when the result still cannot start an identifier (it
   begins with a digit or a ['], as in [$0_bytes] -> [_0_bytes]). We give up
   (returning [None], so the caller falls back to a generated name) when two
   rejected characters sit side by side: a lone separator reads fine, but a run
   of them ([$!!!]) collapses to a [__] blob that no longer resembles a name. *)
let sanitize_identifier s =
  if Lexer.is_valid_identifier s then Some s
  else if s = "" then None
  else
    let is_idchar c =
      (c >= 'a' && c <= 'z')
      || (c >= 'A' && c <= 'Z')
      || (c >= '0' && c <= '9')
      || c = '_' || c = '\''
    in
    let rec adjacent_rejects i =
      i + 1 < String.length s
      && (((not (is_idchar s.[i])) && not (is_idchar s.[i + 1]))
         || adjacent_rejects (i + 1))
    in
    if adjacent_rejects 0 then None
    else
      let mapped = String.map (fun c -> if is_idchar c then c else '_') s in
      let candidate =
        match mapped.[0] with '0' .. '9' | '\'' -> "_" ^ mapped | _ -> mapped
      in
      if Lexer.is_valid_identifier candidate then Some candidate else None

module LabelStack = struct
  type t = {
    ns : Namespace.t;
    stack : (string option * (string * bool ref)) list;
  }

  let push ?diagnostics ?(targeted = true) st (label : Src.name option) =
    let ns = Namespace.dup st.ns in
    let used = ref false in
    (* The source label name made into a valid Wax identifier (sanitizing e.g. a
       leading digit, [$0_bytes] -> ['_0_bytes]); [None] when the source had no
       name or it cannot be sanitized, in which case we fall back to the
       generated "l". *)
    let src =
      match label with
      | Some label -> (
          match sanitize_identifier label.Ast.desc with
          | Some desc -> Some { label with Ast.desc }
          | None -> None)
      | None -> None
    in
    let candidate = match src with Some l -> l.Ast.desc | None -> "l" in
    (* Only claim a name for a label that will actually render: a source-named
       block always renders (see below), and an anonymous block renders only
       when a branch targets it ([targeted]). Reserving a name for an anonymous,
       untargeted block would waste the fallback "l" and needlessly bump a real
       inner label of the same name — the block renders label-free, so it needs
       no name. When not reserved, [name] is a bare candidate that is never
       emitted (its [used] stays false); it would only leak if [targeted]
       under-approximated, which the round-trip corpus would flag. *)
    let name, outcome =
      if Option.is_some src || targeted then
        match src with
        | Some l -> Namespace.add' ~loc:l.Ast.info ns candidate
        | None -> Namespace.add' ns candidate
      else (candidate, Namespace.Available)
    in
    ( (fun () ->
        (* Render the label when a branch targets it, or when the source named
           the block with a name we could keep — a named block keeps its label
           even if no branch targets it, so the name survives the round-trip. An
           anonymous (or unsalvageably-named) unbranched block stays
           label-free. *)
        if !used || Option.is_some src then (
          (* A label namespace reserves no words, so a rename is always a
             collision with an enclosing label of the same name. *)
          (match (src, outcome, diagnostics) with
          | Some l, Namespace.Renamed { reserved; previous }, Some diagnostics
            ->
              Sequence.report_rename diagnostics ~location:l.Ast.info ~previous
                ~reserved ~original:candidate ~renamed:name
          | _ -> ());
          Some
            (match label with
            | Some label -> { label with desc = name }
            | None -> Ast.no_loc name))
        else None),
      {
        ns;
        stack =
          ( Option.map (fun (l : Src.name) -> l.Wax_utils.Ast.desc) label,
            (name, used) )
          :: st.stack;
      } )

  let get st (idx : Src.idx) =
    let name, used =
      match idx.desc with
      | Num n -> (
          match List.nth_opt st.stack (Uint32.to_int n) with
          | Some entry -> snd entry
          | None -> raise (Unresolved_reference idx.Ast.info))
      | Id id -> (
          match List.assoc_opt (Some id) st.stack with
          | Some entry -> entry
          | None -> raise (Unresolved_reference idx.Ast.info))
    in
    used := true;
    { idx with desc = name }

  let make () = { ns = Namespace.make ~kind:`Label (); stack = [] }
end

module CondTbl = struct
  (* A single Wax name may stand for several declarations across conditional
     branches with different definitions (e.g. a function imported with a
     different signature, hence a different arity, in each branch of an
     [(@if …)]). Each declaration is recorded with the assumption under which
     it holds, and a lookup resolves against the current branch's assumption,
     so a reference in a given branch sees the matching declaration. With a
     single declaration this degenerates to a plain name-keyed table. *)
  type 'a t = (string, (Cond.t * 'a) list) Hashtbl.t

  let make () : _ t = Hashtbl.create 16

  let add tbl asm name v =
    let prev = try Hashtbl.find tbl name with Not_found -> [] in
    Hashtbl.replace tbl name ((asm, v) :: prev)

  (* Raises [Not_found] when the name is unknown, like the plain table did. *)
  let find tbl asm name =
    match Hashtbl.find tbl name with
    | [ (_, v) ] -> v
    | entries -> (
        (* Resolve to the declaration whose branch is reachable under the
           current assumption, pruning declarations from mutually-exclusive
           branches. Falls back to the most recent if none is compatible
           (only for a reference that is itself unreachable). *)
        match
          List.find_opt
            (fun (c, _) -> Cond.is_satisfiable (Cond.and_ asm c))
            entries
        with
        | Some (_, v) -> v
        | None -> snd (List.hd entries))

  (* All declarations whose branch is reachable under [asm]. More than one
     means the reference does not select a single branch. *)
  let compatible tbl asm name =
    match Hashtbl.find_opt tbl name with
    | None -> []
    | Some entries ->
        List.filter_map
          (fun (c, v) ->
            if Cond.is_satisfiable (Cond.and_ asm c) then Some v else None)
          entries
end

(*** The conversion context ***)

(* How a value's own printed form re-types it on a re-parse, as far as the
   dead-code backing scan can classify it from the node (and the tables below):
   a REFERENCE settled in a hierarchy — [eq] telling whether it is provably an
   [eq]-subtype, i.e. a valid [ref.eq] operand, which only an [any]-hierarchy
   reference other than a bare [&any] can be — a NULL (which every hierarchy
   accepts), a NON-REFERENCE value, or unclassifiable. What the dead-code
   reference pins ([ref.is_null] / [ref.eq] / the cross-hierarchy converts) ask
   of a residual their hole would reconnect to (see [backing_class_of]). *)
type backing_class =
  | Ref_class of { hier : [ `Any | `Extern | `Func | `Exn | `Cont ]; eq : bool }
  | Null_class
  | Value_class
  | Unknown_class

type ctx = {
  types : Sequence.t;
  struct_fields : (string, Sequence.t * string list) Hashtbl.t;
  globals : Sequence.t;
  functions : Sequence.t;
  memories : Sequence.t;
  tables : Sequence.t;
  tags : Sequence.t;
  datas : Sequence.t;
  elems : Sequence.t;
  referenced_elems : (string, unit) Hashtbl.t;
      (* Wax names of element segments used by table.init / elem.drop /
         array.*_elem. A declarative segment is normally dropped (regenerated by
         [to_wasm] from ref.func usage), but one that is referenced this way
         needs an explicit declaration so the reference resolves. *)
  type_defs : Src.subtype CondTbl.t;
  implicit_types : (Uint32.t, Src.functype) Hashtbl.t;
      (* Function types that the WAT text format synthesises from inline
         [(param)]/[(result)] signatures (the type-use abbreviation), keyed by
         the type index they occupy. The source AST keeps such uses inline and
         does not materialise them as [Types] fields, so this table is what lets
         a numeric [(type N)] elsewhere resolve to the implicit type. These types
         are anonymous: they are rendered inline ([&fn(..)] / an inline [sign]),
         never as a named Wax type. Empty for modules with conditional
         annotations, where numeric references are forbidden anyway. *)
  mutable named_implicit : (string * Src.functype) list;
      (* Implicit function types that had to be given a name because they are
         referenced from a ref-type position (where Wax has no inline
         function-type form). Each is emitted as a [type <name> = fn(..)]
         declaration; accumulated in reverse order of first use. *)
  function_types : Src.typeuse CondTbl.t;
  exports :
    ( Src.exportable * string,
      (Cond.t * Wax_wasm.Ast.cond * Src.name) list )
    Hashtbl.t;
      (* Standalone [(export …)] fields, keyed by the Wax name of their target,
         attached to that target as [#[export]] attributes. Each is paired with
         the conditional-branch assumption under which it appears -- both the
         solved form (for satisfiability/implication tests) and the syntactic
         condition (for a [#[export …, if <cond>]] guard) -- so a target that
         exists in several mutually exclusive branches receives only the exports
         of its own branch, and an export narrower than its target's reachability
         is emitted as a guarded attribute. *)
  starts : (string, (Cond.t * Wax_wasm.Ast.cond) list) Hashtbl.t;
      (* [(start …)] fields, keyed by the Wax name of their function, rendered as
         a [#[start]] attribute on it rather than a separate field. As with
         [exports], each is paired with the branch condition under which it
         appears, so a start narrower than its function's reachability becomes a
         guarded [#[start, if <cond>]] and mutually exclusive starts (at most one
         per configuration) stay on their own functions. *)
  locals : Sequence.t;
  local_valtypes : (string, Ast.valtype) Hashtbl.t;
      (* The Wax type of each local (parameters included), keyed by the Wax name;
         a fresh table per function, like [locals] itself. *)
  global_valtypes : (string, Ast.valtype) Hashtbl.t;
      (* The same for the module's globals, imported ones included, filled while
         their names are registered (before any body is converted, so a forward
         reference resolves).

         [LocalGet]/[GlobalGet] record a NUMERIC type from these on the node they
         emit (see [expect]), which is what tells [Stack.effective_backing] that
         such a residual cannot be the reference backing a dead [ref.is_null] /
         [ref.eq] hole: a [Get] carries no width tag and states no type of its
         own — its type lives in its declaration — so without the record a
         numeric local or global read looked like a reference and left the hole
         unpinned, re-lowering [!] to [i32.eqz]. *)
  address_types : (string, Ast.valtype) Hashtbl.t;
      (* The address type ([i32], or [i64] under memory64) of each memory and
         table, keyed by the Wax name — what [memory.size]/[memory.grow] and
         [table.size]/[table.grow] return. Filled in the naming pre-pass, where the
         field's limits are in hand, and read at those four instructions so a dead
         residual of one is known not to be a reference backing (see
         [Stack.effective_backing]). Memories and tables share one table: their Wax
         names live in different index spaces but are drawn from one namespace, so
         a name identifies at most one of them. *)
  multi_ref_results : (string, backing_class array) Hashtbl.t;
      (* For a function with a MULTI-value signature: the classification of
         each result, in result order (see [backing_class]), keyed by the Wax
         name (like [address_types]). The expectation channel is single-valued,
         so a multi-value call residual cannot record its composition on the
         node; this is what lets a dead reference op ask what such a backing
         would hand its reconnecting hole. Reconnection is POSITIONAL — a hole
         takes the topmost pending value — so the consulting op indexes from
         the entry's top by the claims interposed holes have already eaten (see
         [backing_class_of]). Filled at each [Call] emission (any call node the
         backing scan can see was emitted before the consulting op). *)
  labels : LabelStack.t;
  tag_types : Src.typeuse CondTbl.t;
  label_arities : (string option * int) list;
  block_params : Src.valtype array;
      (* The parameters of the INNERMOST enclosing block, which it takes off the
         enclosing stack and which are therefore its first stack values. A
         reference among them BACKS a hole popped there, so the dead-code
         reference pins ([ref.is_null]) leave it bare instead of pinning a
         hierarchy of their own: the hole reconnects to the parameter on re-parse
         and takes its type. A function's parameters are locals, not stack values,
         so the function level leaves this empty. *)
  return_arity : int;
  strict_constants : bool;
      (* When set, every numeric constant is wrapped in a cast to its concrete
         type ([0 as i32], [0.0 as f64], ...). This keeps Wax type inference
         from re-typing an otherwise polymorphic literal, so a type mismatch in
         the source survives the round-trip. *)
  faithful : bool;
      (* When set (the [--faithful] decompilation mode), the recoveries that
         rewrite the instruction stream to a shorter or differently-shaped one
         are turned off, so the decompiled Wax re-lowers to the exact original
         opcodes. Here it keeps the [!(a == b)] form of [t.eq; i32.eqz] rather
         than fusing it to [a != b] (which recompiles to a single [t.ne]); it is
         also threaded into {!Recover_match} to disable the flat
         [br_on_cast_fail]-chain arm. *)
  diagnostics : Wax_utils.Diagnostic.context;
  cond_env : Cond.env;
  cond_diag : Wax_utils.Diagnostic.context;
  mutable cond_asm : Cond.t;
      (* Assumption for the conditional branch currently being registered or
         converted; threaded through [Module_if_annotation]/[If_annotation] so
         the type tables above resolve to the right per-branch declaration. *)
}

(*** Names, indices, and type conversions ***)

let get_annot e = fst e.Wax_utils.Ast.desc
let get_type e = snd e.Wax_utils.Ast.desc

(* Build a located [annotated_array] element ([name : type] in a struct, or a
   subtype in a rec group), keeping the source location so a trailing comment
   attaches to the whole entry. *)
let annotated loc a t = { Ast.desc = (a, t); info = loc }

let idx ctx kind i =
  match kind with
  | `Type -> Sequence.get ctx.types i
  | `Global -> Sequence.get ctx.globals i
  | `Func -> Sequence.get ctx.functions i
  | `Mem -> Sequence.get ctx.memories i
  | `Table -> Sequence.get ctx.tables i
  | `Tag -> Sequence.get ctx.tags i
  | `Data -> Sequence.get ctx.datas i
  | `Elem -> Sequence.get ctx.elems i
  | `Local -> Sequence.get ctx.locals i

let label ctx i = LabelStack.get ctx.labels i

(* The Wax name for a concrete type reference [i] appearing in a ref-type. An
   implicit (inline-signature) function type has no source name and is normally
   rendered inline, but a ref-type position has no inline function-type form, so
   such a type is given a name on first use and emitted as a [type] declaration
   (see [named_implicit] / [extra_type_decls]). *)
let type_ref_name ctx (i : Src.idx) =
  match i.Ast.desc with
  | Src.Num n when Hashtbl.mem ctx.implicit_types n ->
      let name =
        match Sequence.find_bound ctx.types n with
        | Some name -> name
        | None ->
            let name = Sequence.mint_name ctx.types in
            Sequence.bind_at ctx.types n name;
            ctx.named_implicit <-
              (name, Hashtbl.find ctx.implicit_types n) :: ctx.named_implicit;
            name
      in
      { i with desc = name }
  | _ -> idx ctx `Type i

(* The spine ([heaptype]…[fieldtype]) copies each constructor through, naming
   each index via [type_ref_name]; [functype]/[comptype]/[subtype] below stay
   hand-written because they allocate Wax names (with rename diagnostics) and
   look up struct-field names. *)
module Map =
  Wax_wasm.Ast.Map_types_spine (Src) (Ast)
    (struct
      type nonrec ctx = ctx

      let idx st i = type_ref_name st i
    end)

let heaptype = Map.heaptype
let reftype = Map.reftype
let valtype = Map.valtype

let storagetype ctx (st : Src.storagetype) : Ast.storagetype =
  match st with Value v -> Value (valtype ctx v) | Packed p -> Packed p

(* Convert one WAT data-segment element back to a Wax data element: a string
   stays a string, a scalar numlist becomes a [Data_run] of literal strings (the
   type is stated once, so nan/inf need no suffix), and a [v128] run stays one
   [Data_v128] grouping all its constants (preserving the WAT grouping). *)
let data_elem_to_wax ctx (e : (Src.datavalelem, Ast.location) Ast.annotated) :
    Ast.data_elem =
  match e.Ast.desc with
  | Str s -> Ast.Data_string s
  | Numlist (st, vals) ->
      Ast.Data_run (storagetype ctx st, List.map Ast.no_loc vals)
  | V128list vs -> Ast.Data_v128 (List.map Ast.no_loc vs)

let data_init_to_wax ctx init = List.map (data_elem_to_wax ctx) init

(* Render a function type's parameters into a fresh namespace, renaming a named
   parameter that is a reserved word or collides with an earlier one (and
   warning about it, as for any other declared name). Unnamed parameters stay
   anonymous. Shared by function-type definitions and inline signatures. *)
let functype_params ctx params =
  let ns = Namespace.make () in
  Array.map
    (fun p ->
      let id, t = p.Wax_utils.Ast.desc in
      let id =
        Option.map
          (fun id ->
            let name, outcome =
              Namespace.add' ~loc:(id : Src.name).Wax_utils.Ast.info ns
                id.Wax_utils.Ast.desc
            in
            (match outcome with
            | Namespace.Renamed { reserved; previous } ->
                Sequence.report_rename ctx.diagnostics ~location:id.Ast.info
                  ~previous ~reserved ~original:id.Ast.desc ~renamed:name
            | Namespace.Available -> ());
            { id with Ast.desc = name })
          id
      in
      (* Keep the parameter's source location on the Wax side too. *)
      annotated p.Ast.info id (valtype ctx t))
    params

let functype st (t : Src.functype) : Ast.functype =
  {
    params = functype_params st t.params;
    results = Array.map (fun t -> valtype st t) t.results;
  }

let muttype typ st (t : _ Src.muttype) : _ Ast.muttype =
  { t with typ = typ st t.typ }

let fieldtype = Map.fieldtype

let comptype st name (t : Src.comptype) : Ast.comptype =
  match t with
  | Func t -> Func (functype st t)
  | Struct l ->
      let seq = fst (Hashtbl.find st.struct_fields name) in
      Struct
        (Array.mapi
           (fun i t ->
             let id =
               Sequence.get seq
                 (match get_annot t with
                 | None -> Ast.no_loc (Src.Num (Uint32.of_int i))
                 | Some id -> { id with desc = Id id.Wax_utils.Ast.desc })
             in
             annotated t.Ast.info id (fieldtype st (get_type t)))
           l)
  | Array t -> Array (fieldtype st t)
  | Cont i -> Cont (idx st `Type i)

let subtype st name (t : Src.subtype) : Ast.subtype =
  {
    typ = comptype st name t.typ;
    supertype = Option.map (fun i -> idx st `Type i) t.supertype;
    final = t.final;
    descriptor = Option.map (fun i -> idx st `Type i) t.descriptor;
    describes = Option.map (fun i -> idx st `Type i) t.describes;
  }

let rectype st (t : Src.rectype) : Ast.rectype =
  Array.map
    (fun (t : (_, Ast.location) Ast.Annot.annotated) ->
      let name : Ast.ident = Sequence.get_current st.types in
      annotated t.info name (subtype st name.desc (get_type t)))
    t

let globaltype st = muttype valtype st

(* Remember a global's non-reference type under its Wax name, for the
   numeric-residual test in [Stack.effective_backing] (see [global_valtypes]).
   Read off the SOURCE type rather than through [globaltype]: this runs while
   the names are being registered, before the type section is, so resolving a
   reference type here would report an unbound name. Only the non-reference
   types are wanted anyway — they rule a residual out as a reference, [v128]
   included (its record is what tells [effective_backing] a dead vector
   residual is not the reference a bare hole reconnects to; leaving it out was
   a recording gap the [--debug width-record] census found) — and they need no
   resolution. *)
let record_global_valtype ctx (typ : Src.globaltype) name =
  match typ.Wax_wasm.Ast.typ with
  | I32 -> Hashtbl.replace ctx.global_valtypes name Ast.I32
  | I64 -> Hashtbl.replace ctx.global_valtypes name Ast.I64
  | F32 -> Hashtbl.replace ctx.global_valtypes name Ast.F32
  | F64 -> Hashtbl.replace ctx.global_valtypes name Ast.F64
  | V128 -> Hashtbl.replace ctx.global_valtypes name Ast.V128
  | Ref _ -> ()

(*** Type lookup and arity ***)

type _ kind =
  | Type : Src.subtype kind
  | Func : Src.typeuse kind
  | Tag : Src.typeuse kind

(* Run [f] with [ctx.cond_asm] extended by the branch condition [cond] (taken
   positively for [@then], negatively for [@else]), restoring it afterwards.
   Used in both the name-registration passes and the conversion so that type
   declarations are recorded under, and references resolved against, the
   assumption of the branch they appear in. *)
let with_cond ctx ~location cond positive f =
  let saved = ctx.cond_asm in
  let c = Cond.of_cond ctx.cond_env ctx.cond_diag ~location cond in
  ctx.cond_asm <- Cond.and_ saved (if positive then c else Cond.not_ c);
  Fun.protect ~finally:(fun () -> ctx.cond_asm <- saved) f

let lookup_type (type typ) ctx (kind : typ kind) idx : typ =
  let get seq tbl idx =
    CondTbl.find tbl ctx.cond_asm (Sequence.get seq idx).desc
  in
  match kind with
  | Type -> get ctx.types ctx.type_defs idx
  | Func -> get ctx.functions ctx.function_types idx
  | Tag -> get ctx.tags ctx.tag_types idx

let register_type (type typ) ?hint ctx export_tbl (kind : typ kind) idx exports
    (typ : typ) =
  let register seq tbl kind idx =
    CondTbl.add tbl ctx.cond_asm
      (Sequence.register' ?hint seq export_tbl kind idx exports)
      typ
  in
  match kind with
  | Type -> assert false
  | Func -> register ctx.functions ctx.function_types (Some Func) idx
  | Tag -> register ctx.tags ctx.tag_types (Some Tag) idx

(* The source module is converted without being validated first (validation is
   off by default), so it may be type-invalid in ways the conversion cannot
   represent. Report such a case and abort the conversion rather than crashing
   on an [assert false]. *)
let conversion_error ctx ~location message =
  Wax_utils.Diagnostic.report ctx.diagnostics ~location ~severity:Error ~message
    ();
  Wax_utils.Diagnostic.abort ()

(* The field sequence and names of the struct type [type_name] refers to.
   [ctx.struct_fields] holds only struct types, so a miss means the index names a
   non-struct type -- a [struct.new]/[.get]/[.set] validation would reject.
   Report it and abort like other conversion errors rather than crash on the
   missing table entry. *)
let struct_fields ctx type_name =
  match Hashtbl.find_opt ctx.struct_fields type_name.Wax_utils.Ast.desc with
  | Some fields -> fields
  | None ->
      conversion_error ctx ~location:type_name.Ast.info
        (Wax_utils.Message.text "This type should be a struct type.")

(* Decompilation ergonomics: when a reconstructed struct's leading fields exactly
   match (name and type) its supertype's full field list, replace that prefix
   with a [..] splice sentinel so the printer renders [type c: p = { .., delta }].
   A renamed or covariantly-refined inherited field breaks the match and stays
   explicit. Field types are compared at the Src level, which carries no Wax
   source locations (Ast field types would differ on location alone). The
   supertype is always defined-before (earlier in the group or in an earlier
   group), so the reconstructed [..] re-typechecks. *)
let collapse_splices ctx (rt : Ast.rectype) : Ast.rectype =
  let src_struct name =
    match
      try Some (CondTbl.find ctx.type_defs ctx.cond_asm name.Wax_utils.Ast.desc)
      with Not_found -> None
    with
    | Some { Src.typ = Struct fields; _ } -> Some fields
    | _ -> None
  in
  (* Compare field types without their source locations (which differ between a
     supertype's declaration and the subtype's copy): [Src] text-format indices
     carry a location, so print the reconstructed Wax type and compare that. *)
  let same_type (a : Ast.fieldtype) (b : Ast.fieldtype) =
    let s (ft : Ast.fieldtype) =
      Wax_utils.Printer.run_string (fun pp ->
          Wax_lang.Output.storagetype pp ft.typ)
    in
    a.mut = b.mut && String.equal (s a) (s b)
  in
  Array.map
    (fun elt ->
      let (name : Ast.ident), (sub : Ast.subtype) = elt.Wax_utils.Ast.desc in
      match (sub.typ, sub.supertype) with
      | Struct child_ast_fields, Some parent_name -> (
          match
            ( src_struct parent_name,
              Hashtbl.find_opt ctx.struct_fields parent_name.Ast.desc )
          with
          | Some parent_src, Some (_, parent_names) ->
              let parent_names = Array.of_list parent_names in
              let n = Array.length parent_src in
              let prefix_matches =
                (* [n = 0] would splice nothing, so [..] is pure noise there. *)
                n >= 1
                && n <= Array.length child_ast_fields
                && n <= Array.length parent_names
                &&
                let ok = ref true in
                for i = 0 to n - 1 do
                  if
                    not
                      (String.equal (fst child_ast_fields.(i).Ast.desc).Ast.desc
                         parent_names.(i)
                      && same_type
                           (snd child_ast_fields.(i).Ast.desc)
                           (fieldtype ctx (get_type parent_src.(i))))
                  then ok := false
                done;
                !ok
              in
              if prefix_matches then
                let delta =
                  Array.sub child_ast_fields n
                    (Array.length child_ast_fields - n)
                in
                let fields =
                  Array.append [| Ast.splice_field name.Ast.info |] delta
                in
                { elt with Ast.desc = (name, { sub with typ = Struct fields }) }
              else elt
          | _ -> elt)
      | _ -> elt)
    rt

let functype_arity { Src.params; results } =
  (Array.length params, Array.length results)

(* The implicit (anonymous) function type a numeric [(type N)] denotes, if [N]
   was synthesised from an inline signature; [None] for a named/explicit type or
   a symbolic reference. Consulted before the named-type tables so such a
   reference resolves to its signature rather than raising. *)
let implicit_functype ctx (idx : Src.idx) =
  match idx.Ast.desc with
  | Src.Num n -> Hashtbl.find_opt ctx.implicit_types n
  | Id _ -> None

(* The type to RECORD on a call's result node, so a dead call residual is known
   not to be the reference a bare hole reconnects to (see
   [Stack.effective_backing]): the single non-reference result — or, the
   expectation channel being single-valued, the FIRST result of a multi-value
   signature none of whose results is a reference. On a multi-value node the
   record's only reader is the backing scan's not-a-reference test (the width
   reconciliation and the census look at single-cell nodes only), and "provably
   no reference among these values" is exactly what it asks: unrecorded, an
   all-numeric pair read as `Backing`, a dead [ref.is_null]'s hole was left
   bare, and on re-parse the pair was consumed by earlier numeric holes and the
   bare [!_] re-defaulted to [i32.eqz] (a backing-scan grid finding). [None]
   for a void signature or any signature with a reference result, whichever
   position it is in: a reference result is exactly what must stay a candidate
   backing. *)
let functype_value_result ctx { Src.results; _ } =
  let nonref t = match valtype ctx t with Ast.Ref _ -> None | t -> Some t in
  match Array.to_list results with
  | [] -> None
  | t :: rest ->
      if List.for_all (fun t -> Option.is_some (nonref t)) rest then nonref t
      else None

let type_arity ctx idx =
  match implicit_functype ctx idx with
  | Some ty -> functype_arity ty
  | None -> (
      match (lookup_type ctx Type idx).typ with
      | Func ty -> functype_arity ty
      | Struct _ | Array _ | Cont _ ->
          conversion_error ctx ~location:idx.Ast.info
            (Wax_utils.Message.text "This type should be a function type."))

(* The value type a NON-PACKED, non-reference field or element holds — what an
   UNSIGNED aggregate read yields ([struct.get]/[array.get]), recorded so a dead read
   is known not to be a reference backing (see [Stack.effective_backing]). A packed
   field is read through the signed/unsigned path, whose i32 result is recorded
   there; a reference field records nothing, since that is exactly the value a hole
   may reconnect to. The field is located by the name its immediate resolves to,
   against the ordered name list [ctx.struct_fields] already keeps for the type. *)
let src_typedef ctx (name : Ast.ident) =
  try Some (CondTbl.find ctx.type_defs ctx.cond_asm name.Wax_utils.Ast.desc)
  with Not_found -> None

let field_value_type ctx (ft : Src.fieldtype) =
  match ft.Src.typ with
  | Src.Value v -> ( match valtype ctx v with Ref _ -> None | t -> Some t)
  | Src.Packed _ -> None

let struct_field_value_type ctx type_name (field_name : Ast.ident) =
  match src_typedef ctx type_name with
  | Some { Src.typ = Struct fields; _ } -> (
      let names = Array.of_list (snd (struct_fields ctx type_name)) in
      let rec position k =
        if k >= Array.length names then None
        else if String.equal names.(k) field_name.Wax_utils.Ast.desc then Some k
        else position (k + 1)
      in
      match position 0 with
      | Some k when k < Array.length fields ->
          field_value_type ctx (get_type fields.(k))
      | _ -> None)
  | _ -> None

let array_element_value_type ctx type_name =
  match src_typedef ctx type_name with
  | Some { Src.typ = Array ft; _ } -> field_value_type ctx ft
  | _ -> None

let type_value_result ctx idx =
  match implicit_functype ctx idx with
  | Some ty -> functype_value_result ctx ty
  | None -> (
      match (lookup_type ctx Type idx).typ with
      | Func ty -> functype_value_result ctx ty
      | Struct _ | Array _ | Cont _ -> None)

(* Resolve a typeuse to its function type, through an implicit or a named
   type; [None] if the name resolves to no function type. *)
let typeuse_functype ctx ((i, ty) : Src.typeuse) =
  match ty with
  | Some ft -> Some ft
  | None -> (
      match i with
      | Some i -> (
          match implicit_functype ctx i with
          | Some ft -> Some ft
          | None -> (
              match (lookup_type ctx Type i).typ with
              | Func ft -> Some ft
              | Struct _ | Array _ | Cont _ -> None))
      | None -> None)

let typeuse_value_result ctx (i, ty) =
  match (i, ty) with
  | _, Some t -> functype_value_result ctx t
  | Some i, None -> type_value_result ctx i
  | None, None -> None

let typeuse_arity ctx (i, ty) =
  match (i, ty) with
  | _, Some t -> functype_arity t
  | Some i, None -> type_arity ctx i
  | None, None -> assert false

let blocktype_arity ctx (typ : Src.blocktype option) =
  match typ with
  | None -> (0, 0)
  | Some (Valtype _) -> (0, 1)
  | Some (Typeuse t) -> typeuse_arity ctx t

(* The types a block takes off the enclosing stack as its own parameters (see
   [ctx.block_params]). A [Valtype] blocktype declares a result, not a parameter,
   and a missing one declares neither. *)
let blocktype_params ctx (typ : Src.blocktype option) : Src.valtype array =
  let of_functype { Src.params; _ } =
    Array.map (fun p -> snd p.Wax_utils.Ast.desc) params
  in
  match typ with
  | None | Some (Valtype _) -> [||]
  | Some (Typeuse (i, ty)) -> (
      match (i, ty) with
      | _, Some t -> of_functype t
      | Some i, None -> (
          (* Through [implicit_functype] first, as [type_arity] does: a blocktype
             index may name a type synthesised from an inline signature, which the
             named-type tables do not hold — looking it up there reports it as an
             unbound reference. *)
          match implicit_functype ctx i with
          | Some t -> of_functype t
          | None -> (
              match (lookup_type ctx Type i).typ with
              | Func t -> of_functype t
              | Struct _ | Array _ | Cont _ -> [||]))
      | None, None -> [||])

(* The arity used to convert a reference (how many operands a call consumes) is
   fixed in the produced Wax, so it must be the same in every branch reachable
   here. If a name is declared with different arities in mutually-exclusive
   branches and the reference does not select one (e.g. it sits in unconditional
   code, as [dv_make] does in io.wat), there is no single faithful conversion;
   report it rather than emit a wrong-arity call. *)
let checked_arity ctx kind tbl what name_idx compatible =
  let arity = typeuse_arity ctx (lookup_type ctx kind name_idx) in
  let name = (Sequence.get tbl name_idx).Ast.desc in
  (match compatible ctx.cond_asm name with
  | _ :: _ :: _ as l when List.exists (fun t -> typeuse_arity ctx t <> arity) l
    ->
      Wax_utils.Diagnostic.report ctx.diagnostics ~location:name_idx.Ast.info
        ~severity:Error
        ~message:
          (Wax_utils.Message.text
             (Printf.sprintf
                "%s $%s is declared with different arities in \
                 mutually-exclusive conditional branches but referenced where \
                 the branch is undetermined; this cannot be converted to Wax."
                what name))
        ()
  | _ -> ());
  arity

let function_arity ctx f =
  checked_arity ctx Func ctx.functions "Function" f
    (CondTbl.compatible ctx.function_types)

let tag_arity ctx t =
  checked_arity ctx Tag ctx.tags "Tag" t (CondTbl.compatible ctx.tag_types)

let label_arity ctx (idx : Src.idx) =
  match idx.desc with
  | Id id -> (
      match
        List.find_opt
          (fun e -> match e with Some id', _ -> id = id' | _ -> false)
          ctx.label_arities
      with
      | Some e -> snd e
      | None -> raise (Unresolved_reference idx.Ast.info))
  | Num i -> (
      match List.nth_opt ctx.label_arities (Uint32.to_int i) with
      | Some e -> snd e
      | None -> raise (Unresolved_reference idx.Ast.info))

(* (parameter count, result count) of the function type a continuation type
   wraps. *)
let cont_arity ctx idx =
  match (lookup_type ctx Type idx).typ with
  | Cont ft -> type_arity ctx ft
  | Func _ | Struct _ | Array _ ->
      conversion_error ctx ~location:idx.Ast.info
        (Wax_utils.Message.text "This type should be a continuation type.")

(* Number of values a [switch] to continuation [ct] produces: the parameters of
   the continuation referenced by the last parameter of [ct]'s function type. *)
let switch_output ctx ct =
  match (lookup_type ctx Type ct).typ with
  | Cont ft -> (
      match (lookup_type ctx Type ft).typ with
      | Func { params; _ } when Array.length params > 0 -> (
          match snd params.(Array.length params - 1).Ast.desc with
          | Ref { typ = Type ct2; _ } -> fst (cont_arity ctx ct2)
          | _ -> 0)
      | Func _ | Struct _ | Array _ | Cont _ -> 0)
  | Func _ | Struct _ | Array _ -> 0

let on_clause ctx (c : Src.on_clause) : Ast.on_clause =
  match c with
  | OnLabel (tag, lbl) -> OnLabel (idx ctx `Tag tag, label ctx lbl)
  | OnSwitch tag -> OnSwitch (idx ctx `Tag tag)

(*
Step 1: traverse types and find existing names
Step 2: use this info to generate using names without reusing existing names
*)

(* Remember the address type of a memory or table under the Wax [name] it was just
   registered under (see [ctx.address_types]). *)
let record_address_type ctx name (at : [ `I32 | `I64 ]) =
  Hashtbl.replace ctx.address_types name
    (match at with `I32 -> Ast.I32 | `I64 -> Ast.I64)

(*** Recorded type expectations ***)

(* A Wasm opcode states the type of every value it produces; the Wax surface form
   this conversion prints only *re-infers* it, and the two silently disagreeing is
   the "width drift" bug class the width pins below guard against (an unpinned
   [i64] literal tree re-defaults to [i32] on re-parse, so [i64.div_u] recompiles
   as [i32.div_u]). [expect] records the Wasm-stated type on the node itself
   ([Ast.instr]'s [expected]), so the typer — which already runs over this
   conversion's output — can compare its own inference against it and report a
   drift instead of shipping it (see {!Wax_lang.Typing.f}'s [~width_check]).
   Recording is annotation only: it never changes what is emitted.

   Every non-reference value type is recorded — the four numeric scalars and
   [v128]. Only the scalars are ever CHECKED (the drift class is a flexible numeric
   literal defaulting to [i32]/[f64], and [v128] has no member in that lattice, so
   the reconciliation's arms skip it: [numeric_width]/[numeric_valtype] return
   nothing for it). A recorded [v128] serves a second purpose the check does not:
   it marks the value as PROVABLY NOT A REFERENCE for
   {!Stack.effective_backing}, which otherwise reads an untagged residual as the
   reference a bare hole reconnects to — a dead v128 residual there left a
   [ref.is_null] unpinned and it re-parsed as an [i32.eqz] (a smith finding). A
   reference type is still not recorded: that is the one class outside this
   channel — marked [Contextual] ("considered, deliberately no claim") rather
   than left [Unset], so an [Unset] numeric node in this conversion's output
   always means a recording GAP (see [--debug width-record]). *)
let recorded_expectation (ty : Ast.valtype) : Ast.expectation =
  match ty with
  | I32 | I64 | F32 | F64 | V128 -> Recorded ty
  | Ref _ -> Contextual

let expect (ty : Ast.valtype) (i : _ Ast.instr) : _ Ast.instr =
  { i with Ast.expected = recorded_expectation ty }

(* Mark [i] [Contextual]: a position whose re-parse type is fixed by the
   construct it sits in, so it needs no claim of its own — an IMMEDIATE of the
   printed form (a memarg label, a lane index, a vector-constructor component),
   or the literal under a [Neg]/pin whose enclosing node carries the claim for
   the whole (their cells are one). NOT for a value that sat on the conversion
   stack: record what its opcode states instead. What this buys is that [Unset]
   stays reserved for a recording GAP, which is what the census
   ([--debug width-record]) reports. *)
let contextual (i : _ Ast.instr) : _ Ast.instr =
  { i with Ast.expected = Ast.Contextual }

(* A deliberately BARE hole: ADAPTIVE on the re-parse — it takes whatever type
   its context demands, which is the behaviour the emission site wants where a
   pin would state a type the Wasm side leaves polymorphic. [Contextual]
   because the site considered it; a hole that must state its type is built
   with {!typed_hole} instead (and the width repair pins whichever bare hole
   would resolve wrong — see {!Wax_lang.Typing.f}'s [~width_check]). *)
let bare_hole () : _ Ast.instr = contextual (Ast.no_loc_instr Ast.Hole)

(* Record a call's single non-reference result type on its node (see
   {!functype_value_result}); a void, multi-value or reference-returning call is
   left as is. *)
let expect_value_result ty e = match ty with Some t -> expect t e | None -> e

(* Record the address type of the memory or table [name] on [e] — the result type of
   its [size]/[grow] (see [ctx.address_types]). *)
let expect_address_type ctx (name : Ast.ident) e =
  match Hashtbl.find_opt ctx.address_types name.Ast.desc with
  | Some t -> expect t e
  | None -> e

let valtype_of_width : [ `I32 | `I64 | `F32 | `F64 ] -> Ast.valtype = function
  | `I32 -> I32
  | `I64 -> I64
  | `F32 -> F32
  | `F64 -> F64

(* The type a cast's *result* has, which is the new node's expectation — not the
   operand's. *)
let cast_result (ty : Ast.casttype) : Ast.expectation =
  match ty with
  | Ast.Valtype ty -> recorded_expectation ty
  | Signedtype { typ; _ } -> Recorded (valtype_of_width typ)
  | Functype _ -> Contextual

(* Wrap [e] in a cast to [ty]. The single constructor for every cast this
   conversion inserts: the [{ e with … }] copy would otherwise carry [e]'s own
   expectation onto a node of a different type. *)
let cast_to (ty : Ast.casttype) (e : _ Ast.instr) : _ Ast.instr =
  { e with Ast.desc = Ast.Cast (e, ty); expected = cast_result ty }

(* The typed hole [(_ as ty)] the conversions give an absent operand — a pop from
   the polymorphic stack of dead code. Both nodes record [ty]: the opcode's
   signature states the operand type whether or not a value was there to take. *)
let typed_hole (ty : Ast.valtype) =
  cast_to (Valtype ty) (expect ty (Ast.no_loc_instr Ast.Hole))

(* The bottom heap types. A bare hole ascribed one — [(_ as &?none)] and kin —
   is the CLAIM-FREE pin: the typer's [count_holes] gives that shape no pending
   value (nothing but a null or a value off the polymorphic bottom inhabits the
   type), so unlike a top-of-hierarchy pin it can never capture a stranded
   residual that an [(@if)] branch, in its own configuration, consumes instead.
   The dead-code pins below use it wherever a wrong-hierarchy residual is what
   the printed hole would otherwise reconnect to. *)
let is_bottom_heaptype (t : Ast.heaptype) =
  match t with None_ | NoExtern | NoFunc | NoExn | NoCont -> true | _ -> false

(* Drop the expectation recorded on [i] and on everything under it. Used where a
   value's width comes from its CONTEXT rather than from its own printed form — a
   block/function result, an initialiser, a branch delivery. The conversion leaves
   such a value unpinned for exactly that reason, and the typer types it against
   the context type instead of merging that type into the value's own cell, so the
   type inferred for the node stays flexible and states nothing about the width the
   value takes: a claim recorded there would be checked against a defaulted
   flexible literal and misfire. It clears as far down as the context type
   reaches, no further — a [do f32 { 3 + 4 }] exit is pinned by the block
   annotation down to both literals, whereas a comparison's operands keep their
   claim, their own printed form still having to carry their width. *)
let rec forget_expected (i : _ Ast.instr) : _ Ast.instr =
  let desc : _ Ast.instr_desc =
    match i.Ast.desc with
    (* An arithmetic operator's result type IS its operands' — a context type
       reaching the sum reaches them too, exactly as a pin cast on the sum would
       (a comparison's i32 result says nothing about its operands, so it stops
       here, and so does a cast, a call or a narrow store, which fix their
       operand's type themselves). *)
    | Ast.BinOp
        ( ({
             Ast.desc =
               Add | Sub | Mul | Div _ | Rem _ | And | Or | Xor | Shl | Shr _;
             _;
           } as op),
          a,
          b ) ->
        Ast.BinOp (op, forget_expected a, forget_expected b)
    | Ast.UnOp (({ Ast.desc = Neg | Pos; _ } as op), a) ->
        Ast.UnOp (op, forget_expected a)
    (* A [select]'s arms share its result type; its condition does not. *)
    | Ast.Select (c, a, b) ->
        Ast.Select (c, forget_expected a, forget_expected b)
    (* A sequence's value is its last element. *)
    | Ast.Sequence (_ :: _ as l) ->
        let rev = List.rev l in
        Ast.Sequence (List.rev (forget_expected (List.hd rev) :: List.tl rev))
    (* A nested block's own exits were cleared by its own [run]. *)
    | d -> d
  in
  { i with Ast.desc; expected = Contextual }

(*** The conversion stack ***)

(* An operand tree whose printed form re-parses type-ADAPTIVELY: with no width or
   type of its own it re-defaults (a numeric tree to [i32]). A bare hole is the
   base case, and an untyped [select] is adaptive when BOTH arms are (its result
   type is its arms'). Mirrors the typer's [reparse_adaptive] (kept local to
   from_wasm so it carries no dependency on the typer). *)
let rec reparse_adaptive (i : _ Ast.instr) =
  match i.Ast.desc with
  | Ast.Hole | Ast.Null -> true
  | Ast.Select (_, a, b) -> reparse_adaptive a && reparse_adaptive b
  | _ -> false

module Stack = struct
  (* [width] records the numeric result width the producing opcode states — a
     const or arithmetic op tags its own width, everything else is [None]. It is
     recorded on the value itself as it is pushed ({!expect}/[push_num]), and that
     RECORD is what keeps the width across the round trip: the typer reconciles it
     with what the printed Wax would re-infer and pins whatever would resolve
     elsewhere (see {!Wax_lang.Typing.f}'s [~width_check]). Nothing here places a
     width pin any more — a consumer whose surface erases its operand's width
     ([drop], [i32.wrap_i64], a comparison, [eqz]) simply pops it.

     The tag lives on in the STACK for what it says about a value's flexibility,
     which pinning cannot replace:
     - a numeric residual is not a candidate backing for a bare hole (see
       [effective_backing]: a [ref.is_null]/[ref.eq] operand is a reference);
     - an arithmetic result is only width-FLEXIBLE while both its operands are, and
       a method-form op inherits its receiver's flexibility — which decides the tag
       a consumer sees and, for [drop], whether its [Let] carries a type
       annotation. *)
  type width = [ `I32 | `I64 | `F32 | `F64 ] option

  (* Each entry is [(arity, width, instr)]: [arity] is the number of stack values
     the instruction produces. Only a single value ([arity = 1]) can be popped as
     an operand; [arity = 0] is a statement (a [nop], a void call, a branch whose
     targets carry no value) and [arity >= 2] a multi-value residual, both of which
     a pop reads as a hole; [arity = -1] is a value a block-shaped consumer took as
     its parameter ([consume]) — it still prints as its own statement, but its
     value is spoken for. The distinction matters for [effective_backing]: a
     zero-value statement is transparent (a bare hole reconnects THROUGH it to
     whatever is below), a value residual is not, and a consumed value cancels
     against its consumer's parameter claim. *)
  type stack = (int * width * Ast.location Ast.instr) list
  type 'a t = stack -> stack * 'a

  let rec complete n cur =
    if n = 0 then cur else complete (n - 1) (bare_hole () :: cur)

  let rec grab_rec n stack cur =
    if n = 0 then (stack, cur)
    else
      match stack with
      | (1, _, instr) :: rem -> grab_rec (n - 1) rem (instr :: cur)
      | _ -> (stack, complete n cur)

  let consume inputs stack =
    if inputs = 0 then (stack, ())
    else
      ( (match stack with
        | (1, w, instr) :: rem -> (-1, w, instr) :: rem
        | _ -> stack),
        () )

  let grab n stack = grab_rec n stack []
  let push arity i stack = ((arity, None, i) :: stack, ())

  (* Record the tagged width as the value's expected type (see {!expect}): the
     tag IS the width the producing opcode states, and recording it is all this
     conversion does about width — the typer pins whatever would otherwise default
     to another one (see {!Wax_lang.Typing.f}'s [~width_check]). An untagged value
     ([None]) keeps whatever its producer recorded: the tag says the value is
     width-FLEXIBLE, not that its type is unknown (a grounded arithmetic result is
     untagged yet has the opcode's width, recorded at the call site). *)
  let expect_width w i =
    match w with Some w -> expect (valtype_of_width w) i | None -> i

  (* Push a numeric value tagged with the width its opcode states. *)
  let push_num width i stack = ((1, width, expect_width width i) :: stack, ())

  (* An unconditional control-flow instruction ([br]/[br_table]/[return]/[become]/
     [unreachable]/[throw]/…) leaves the values still on the stack — below the
     operands it consumed — dead: [run] emits them as leftover statements but no
     consumer ever pops them. Their width rests on the expectation recorded when
     they were pushed — a width-sensitive leftover (an [i64.div_u]/[i64.shr_u] whose
     divisor or shift count is load-bearing) would re-default to i32 on re-parse and
     trap / mask differently, and the typer pins it from that record. The tags are
     dropped because nothing will pop these entries again. *)
  let push_poly i stack =
    let stack = List.map (fun (a, _, e) -> (a, None, e)) stack in
    ((0, None, i) :: stack, ())

  (* Pop one operand. Whether the consumer's Wax surface carries the operand's
     width or erases it ([drop], [i32.wrap_i64], a comparison, [eqz]) no longer
     changes anything here: the value was annotated with its opcode's width when it
     was PUSHED, and the typer pins it from that record if the printed form would
     resolve elsewhere. An empty/absent stack reads as a hole (dead code). *)
  let pop stack =
    match stack with (1, _, i) :: rem -> (rem, i) | _ -> (stack, bare_hole ())

  (* Pop with the width tag, without pinning — the caller decides. Used by [drop],
     which records the tag in its [Let]'s type annotation rather than an identity
     cast. A hole reads as an untagged empty pop. (Binops/comparisons/select use
     [try_pop_tagged] instead, to tell a hole apart from a real operand.) *)
  let pop_tagged stack =
    match stack with
    | (1, w, i) :: rem -> (rem, (i, w))
    | _ -> (stack, (bare_hole (), None))

  let try_pop stack =
    match stack with (1, _, i) :: rem -> (rem, Some i) | _ -> (stack, None)

  (* The REFERENCE value a bare hole reconnects to, seen THROUGH interposed
     entries that cannot be that value:
      - a zero-value statement ([arity] 0) — a [nop], a void call, a [br_if] whose
        condition was the value just above it;
      - a NUMERIC value residual (a [Some] width tag): it cannot be a
        [ref.is_null]/[ref.eq] operand (they take a reference), so in valid code it
        is a leftover from a consumer whose grab an interposed statement blocked
        (e.g. [i32.const c ; atomic.fence ; br_if] leaves [c] stranded, its role as
        the [br_if] condition lost), not the operand the ref op actually pops.
     [stop] marks the terminator sentinels ([arity] 0 too, but the polymorphic
     bottom, so they stop the scan). Returns the first residual that CAN back the
     hole — an [arity] >= 1 value that is neither tagged nor recorded — else [None]
     (a terminator bottom, a numeric/vector residual only, or empty). A [None] tag
     with no record also covers an untyped [select] of holes, correctly treated as a
     backing that the caller then pins.

     What is RECORDED, and therefore skipped, is the accurate list of what cannot be
     a reference: every const and arithmetic result (the width tags); the
     method-form ops, which record their opcode's type even when their tag stays
     flexible; the loads; a local's or global's numeric or vector type; every SIMD
     result (a [v128] record exists for this scan alone — the reconciliation skips
     it); the i32-valued reference ops ([ref.test], [ref.eq], [ref.is_null],
     [array.len], [i31.get_s/u]); the numeric conversions ([wrap], [promote],
     [demote], [extend_i32]); a [Char]; a signed packed field or element read; and a
     CALL whose signature returns one non-reference value ([call], [call_ref],
     [call_indirect] — the callee's type is reachable at the push site even though it
     is not from this scan).

     With the aggregate reads and the memory/table sizes recorded, that list is
     complete for a valid module: every instruction whose result is a numeric or
     vector value now says so on its node, so the only residual this scan can
     return is a value that really may be a reference. (The one thing it cannot
     see is a value from a producer added later without a record — which is why
     fuzz/ref-width.sh enumerates the shape and the round-trip legs
     FAITHDRIFT/WIDTHDRIFT watch the rest.) *)
  (* A statement carrying a HOLE is NOT transparent to the scan below, however
     zero-valued it is: on a re-parse its hole claims the first
     value above it, so that value cannot also back a later hole. This is where the
     scan's model used to diverge from both Wasm and Wax. In
     [array.get ; atomic.fence ; drop ; ref.is_null] the WASM [drop] pops the
     array element; the fence's zero-value entry only blocks the pop in THIS
     conversion's stack, so the element is left as a residual and the [drop] emits
     [_ = _]. Reading the element as a backing for the [ref.is_null] hole then
     suppressed its pin — but on a re-parse the [_ = _] claims the element (exactly
     as the Wasm [drop] did), leaving the bare [!_] to default to i32 and re-lower
     as an [i32.eqz]: an opcode-family change. *)
  (* A hole the re-parse types NUMERICALLY is not such a claimant: it cannot take
     the reference residual, so the statement stays transparent. The value a
     [set]/[tee] writes to a numeric local or global records its type exactly for
     this ([expect_local]/[expect_global]) — without it, [x = _] over a
     [ref.null func] blocked the scan, the [ref.is_null] below it was pinned
     [(_ as &?any)] as if bottom-sprung, and on re-parse the hole DID reconnect to
     the func-hierarchy value: the pin crossed hierarchies and the decompiled Wax
     did not type-check (a wat-mutation-fuzzer finding). *)
  (* How many values a statement claims from THIS stack on a re-parse: one per
     UNTYPED hole (a hole whose recorded type is numeric claims no reference, as
     above), plus a block's PARAMETERS, which it takes from here whether or not any
     hole is involved. A block BODY runs on its own stack, which starts empty, so a
     hole inside it claims nothing here — only the operands a block-shaped node
     evaluates in the enclosing frame do: an [if]'s or [while]'s condition, a
     [match]'s scrutinee. *)
  let rec hole_claims (i : _ Ast.instr) =
    match i.Ast.desc with
    (* EVERY printed hole claims one value: the typer's claiming is positional
       and type-blind ([count_holes] is syntactic), so a hole whose recorded
       type is numeric still takes the next pending value — it merely pairs, in
       a valid module, with the numeric residual the scan's value arms absorb
       below. (The old model gave a recorded hole zero claims and skipped every
       numeric residual unconditionally; the two cancelled only while the
       pairing was type-consistent, which an [(@if)] breaks.) *)
    | Ast.Hole -> 1
    (* A bare hole under a BOTTOM reference ascription is the claim-free pin:
       the typer's [count_holes] gives it no pending value (see
       [is_bottom_heaptype]), so it claims nothing here either. *)
    | Ast.Cast ({ Ast.desc = Ast.Hole; _ }, Ast.Valtype (Ast.Ref { typ; _ }))
      when is_bottom_heaptype typ ->
        0
    (* A conditional annotation claims NOTHING from the tree-typing stack this
       scan models: the typer that builds the tree the lowering reads types each
       branch as an isolated void block, so a branch's holes take no enclosing
       value and a branch's leftovers deliver none. (The CONFIGURATION passes —
       the Wax checker's spliced typing, like the Wasm validator's — instead
       splice the chosen branch into the enclosing frame, where its claims mirror
       the source's own pops per configuration; the emission already mirrors that
       by construction, one hole per branch pop. What the scan must predict is
       the reconnection in the PRESERVED tree, whose types drive [To_wasm].) *)
    | Ast.If_annotation _ -> 0
    | Ast.Block { typ; _ }
    | Ast.Loop { typ; _ }
    | Ast.TryTable { typ; _ }
    | Ast.Try { typ; _ }
    | Ast.TryCatch { typ; _ } ->
        Array.length typ.Ast.params
    | Ast.If { typ; cond; _ } -> Array.length typ.Ast.params + hole_claims cond
    | Ast.While { cond; _ } -> hole_claims cond
    | Ast.Match { scrutinee; _ } -> hole_claims scrutinee
    | _ ->
        List.fold_left (fun n s -> n + hole_claims s) 0 (Ast_utils.sub_instrs i)

  (* Whether a statement carries a conditional annotation: only such a
     statement can have consumed — per configuration, in the source's spliced
     validation — a value whose printed form the tree-typing then pairs with a
     LATER hole. The scan reports it ([`Backing]'s [crossed]) so a caller whose
     pin cannot prove the capture sound from the node alone (the [call_ref]
     callee type pin) can fall back to the claim-free bottom pin only where the
     hazard exists, keeping the annotation-free behaviour untouched. *)
  let rec has_cond_annotation (i : _ Ast.instr) =
    match i.Ast.desc with
    | Ast.If_annotation _ -> true
    | _ -> List.exists has_cond_annotation (Ast_utils.sub_instrs i)

  (* [claims] counts the values the holes ABOVE are still owed: each takes the next
     residual, so the scan skips that many before asking whether what it reaches can
     back this hole. Counting them is what makes a hole-bearing statement
     TRANSPARENT rather than opaque — [_.f = _] claims the two values sitting above
     an extern residual, so the [ref.is_null] hole below it reconnects to that
     extern and needs no pin at all. Read as an opaque blocker, the scan stopped one
     entry early, pinned [(_ as &?any)] as if the hole were bottom-sprung, and on a
     re-parse that pin became an [any.convert_extern]: a hierarchy crossing, and an
     opcode the source never had (a wasm-smith FAITHDRIFT).

     MAINTENANCE: this scan and [hole_claims] are a hand-rolled simulation of the
     Wax re-parser's reconnection behaviour, and [fuzz/backing-scan.sh] enumerates
     their input space exhaustively over an alphabet read off these match arms —
     one representative per entry class. A new arm (a new entry kind, a new claim
     shape) must add its representative there, or the guard degrades back to
     fuzzing luck for exactly that arm. *)
  let rec effective_backing stop ~crossed claims = function
    (* A CONSUMED value ([consume] marked it): it prints as its own statement,
       and on the re-parse the block-shaped consumer above takes it as its
       parameter — the very claim [hole_claims] charged for that consumer. The
       two cancel: without this, the parameter charge ate a REAL value further
       down and the scan pinned over a residual the hole in fact reconnects to
       (the backing-scan grid's Bp1 cluster: the pin materialised as an
       [any.convert_extern]). Spoken for, it can back nothing itself. *)
    | (-1, _, _) :: rem ->
        effective_backing stop ~crossed (max 0 (claims - 1)) rem
    | (0, _, i) :: _ when stop i -> `Blocked
    | (0, _, i) :: rem ->
        effective_backing stop
          ~crossed:(crossed || has_cond_annotation i)
          (claims + hole_claims i)
          rem
    (* Numeric by its width TAG, or by the type its producer RECORDED on it
       ([Ast.instr]'s [expected], which only ever holds a numeric scalar): either
       way it cannot be the reference operand, so keep scanning. The record is what
       catches a residual the tag cannot: a method-form op inherits its receiver's
       flexibility, so [f32.sqrt] of a hole is UNTAGGED while still being an f32 —
       read as a reference backing, it left a dead [ref.eq] unpinned and it
       re-parsed as an [i32.eq] (a bottom-fuzz finding). *)
    | (a, w, i) :: rem
      when a >= 1
           && (w <> None
              ||
              match i.Ast.expected with
              | Ast.Recorded _ -> true
              | Ast.Unset | Ast.Contextual -> false) ->
        (* If holes above are still owed values, these are the values they take
           — ALL of them for a multi-value entry (a record on one means every
           result is non-reference, see [functype_value_result]) — and the scan
           keeps looking. But a value the claims do NOT absorb is what the
           reader's own hole captures (claiming is positional and type-blind),
           and it is provably a NON-reference: report [`Value] so the caller
           grounds its hole with the claim-free bottom pin — a bare hole would
           re-default the op to its numeric family, and a top-of-hierarchy pin
           would capture the value and fail to type. Reachable only through an
           [(@if)] (whose branches consume the value per configuration); in
           plain wasm the validator types the residual into the reference op
           and rejects. *)
        if claims >= a then effective_backing stop ~crossed (claims - a) rem
        else `Value
    (* A value entry the holes above fully claim: not this hole's operand, so
       keep looking past it. *)
    | (a, None, _) :: rem when a >= 1 && claims >= a ->
        effective_backing stop ~crossed (claims - a) rem
    (* An ADAPTIVE value — an untyped [select] of holes, or a bare hole — is not a
       backing: its own printed form carries no hierarchy, so on a re-parse the ref
       op's hole reconnects to it and the pair re-defaults to the NUMERIC form (a
       [select] of holes becomes the i32 select and [!] on it an [i32.eqz]). It
       stops the scan rather than being skipped: the hole reconnects to IT, so
       whatever reference lies deeper is not what the printed form would find. The
       caller then pins the hole, which grounds the reconnected value through the
       same unification (as it already does for such a value popped directly as the
       operand). *)
    | (a, None, i) :: _ when a >= 1 && reparse_adaptive i -> `Blocked
    (* The value the reader's hole captures. Claiming is POSITIONAL: the
       [claims] still owed eat this entry's TOPMOST values, so the capture is
       the entry's value [claims] positions from its top — 0 for a single-value
       entry, and for a partially-claimed multi-value residual a middle result
       (the classification indexes the signature accordingly; the old model
       instead skipped the whole entry, losing the reference a claimed-past
       multi still hands the hole — the VmultiER grid cells). *)
    | (a, None, i) :: _ when a >= 1 -> `Backing (i, claims, crossed)
    (* The two no-backing outcomes are NOT the same: [`Floor] means the scan
       walked cleanly to the block's own floor — where the enclosing block's
       PARAMETERS are the next stack values, so a reference among them can still
       back the hole (see [ctx.block_params]) — while [`Blocked] means a
       terminator sentinel or a hole-bearing statement stands between: the printed
       hole is bottom-sprung there and reconnects to nothing, so nothing (a block
       parameter included) can back it. Conflating them let a block's reference
       parameter suppress the pin THROUGH an [unreachable] — [do (&?extern) {
       unreachable; !_ }] re-defaulted to [i32.eqz] even though the parameter was
       real (a ref-width grid finding). *)
    | [] -> `Floor
    | _ -> `Blocked

  (* [claims] seeds the scan with the hole count of the consulting statement's
     SIBLING operands: a receiver is its statement's deepest operand, so its
     positional capture sits below the values its shallower siblings' own holes
     take first. *)
  let effective_backing ?(claims = 0) stop stack =
    (stack, effective_backing stop ~crossed:false claims stack)

  (* [try_pop] carrying the width tag — a method-form op tags its result with its
     receiver's flexibility, so an erasing consumer pins it (and the pin, cast on
     the result, propagates back to the receiver: [((5).clz()) as i64] is
     [i64.clz]). *)
  let try_pop_tagged stack =
    match stack with
    | (1, w, i) :: rem -> (rem, Some (i, w))
    | _ -> (stack, None)

  (* Flush the leftover stack as statements. A value stranded past a conditional
     branch ([br_if]/[br_on_null]/[br_on_cast]/…) is popped by neither a
     width-erasing consumer nor [push_poly] (which only fires at an
     *unconditional* terminator): the branch pushes a statement entry
     ([present = false]) on top of it, so it can no longer be consumed and
     reaches here as a leftover — its width tag would otherwise be lost, and a
     load-bearing [i64.shr_u]/[f32.sqrt] leftover would re-default to i32/f64 on
     re-parse (masking/precision change). Pin such a stranded value from its
     discarded tag.

     Only a *present* stranded value is pinned: a present value that a statement
     entry sits above (closer to the top) can never be popped again, so it is a
     genuine leftover. Two shapes keep the pin off values whose width is already
     fixed by context (where a pin would be redundant cast noise): the block's own
     RESULTS — the top [results] present entries, fixed by the block/function/
     const-initialiser type — and a value [consume] flipped to [present = false]
     as a block input, fixed by the block's declared input type. A value consumed
     later pops normally and never reaches [run].

     [results] is the block's declared output arity: the top [results] present
     entries are its results and stay unpinned; a present entry BEYOND that count
     (or below a statement) is an excess leftover — a value stranded below the
     block's own results with no statement between them (the block-arity gap) is
     otherwise mistaken for a result and never pinned, so a width-tagged leftover
     ([f64.trunc]) narrows on re-parse. Callers that cannot state an arity default
     to the old leading-present-run heuristic ([max_int] = every leading present
     entry is a result); the control constructs pass their real output count. *)
  let run ?(results = max_int) f =
    let st, () = f [] in
    let rec pin_stranded results_left below_stmt = function
      | [] -> []
      | (arity, _, i) :: rem ->
          (* Only a single-value entry ([arity = 1]) is a pinnable leftover; a
             statement ([0]) or multi-value residual is left as is and, like a
             statement below it, marks everything deeper as below-statement. *)
          let present = arity = 1 in
          let is_result = present && (not below_stmt) && results_left > 0 in
          (* A leftover keeps the width recorded on it at push time, which is
             what the typer pins it from. A RESULT instead has its expectation
             CLEARED: its width comes from the enclosing block/function/initialiser
             type, and the typer types such a value against that context type
             rather than merging it into the value's own cell, so the value's own
             inferred type stays flexible and says nothing about the width it will
             take. *)
          let i = if present && is_result then forget_expected i else i in
          let results_left =
            if is_result then results_left - 1 else results_left
          in
          i :: pin_stranded results_left (below_stmt || not present) rem
    in
    List.rev (pin_stranded results false st)
end

let ( let* ) e f st =
  let st, v = e st in
  f v st

let return v st = (st, v)

let sequence l =
  match l with [ i ] -> i | _ -> Ast.no_loc_instr (Ast.Sequence l)

(*** Instruction-conversion helpers ***)

let is_integer =
  let int_re =
    Re.(
      compile
        (whole_string
           (alt
              [
                rep1 (alt [ rg '0' '9'; char '_' ]);
                seq
                  [
                    str "0x";
                    rep1 (alt [ rg '0' '9'; rg 'a' 'f'; rg 'A' 'F'; char '_' ]);
                  ];
              ])))
  in
  fun s -> Re.execp int_re s

let is_negative n = n.[0] = '-'

let remove_sign n =
  if n.[0] = '-' || n.[0] = '+' then String.sub n 1 (String.length n - 1) else n

(* A Wax operator carries its own source location; reuse the (source or target)
   instruction's, which is the best approximation we have when reconstructing
   from Wasm. Polymorphic in the carried [desc] so it works for either AST. *)
(* A located operator, sharing the span of the node it was recovered from. Takes
   the span rather than the node: the node can be an [annotated] or an instruction,
   which are no longer the same shape. *)
let op_loc (loc : Ast.location) op : (_, Ast.location) Ast.annotated =
  { Ast.desc = op; info = loc }

(* [loc] is the span of the instruction the literal was decoded from. *)
let integer (loc : Ast.location) n : _ Ast.instr =
  let at desc : _ Ast.instr =
    { desc; info = loc; hints = Wax_wasm.Hints.none; expected = Unset }
  in
  let e = at (Int (remove_sign n)) in
  (* The literal under the [Neg] is [Contextual]: the [Neg] node is the value,
     and whatever claim its consumer records lands there — the two share one
     inference cell, so a claim on the literal itself would be redundant. *)
  if is_negative n then at (UnOp (op_loc loc Ast.Neg, contextual e)) else e

let float i n =
  (* Test the magnitude, not the signed string: a negative integer-valued float
     (e.g. [-4.0] printed as [-4]) must take the [integer] path too, else it
     becomes a [Float] node whose integer-looking text ([-4]) re-lexes as an
     integer literal on the round-trip — dropping the block/cast annotation that
     pinned it to a float and leaving [.to_bits()] applied to an [i64]. *)
  if is_integer (remove_sign n) then integer i.Src.info n
  else
    let e : _ Ast.instr =
      {
        desc = Float (remove_sign n);
        info = i.Src.info;
        hints = Wax_wasm.Hints.none;
        expected = Unset;
      }
    in
    if is_negative n then
      {
        (* As in [integer]: the claim carrier is the [Neg] node. *)
        Ast.desc = UnOp (op_loc i.Src.info Ast.Neg, contextual e);
        info = i.Src.info;
        hints = Wax_wasm.Hints.none;
        expected = Unset;
      }
    else e

let sequence_opt l =
  match l with
  | [] -> None
  | [ i ] -> Some i
  | l -> Some (Ast.no_loc_instr (Ast.Sequence l))

let reasonable_string =
  Re.(
    compile
      (whole_string
         (rep
            (alt
               [ diff any (rg '\000' '\031'); char '\n'; char '\r'; char '\t' ]))))

let string_args n args =
  if n = Uint32.zero then None
  else
    let byte_of_arg arg =
      match arg.Ast.desc with
      | Ast.Int c -> (
          (* [int_of_string_opt]: a byte value too large for an [int] (let alone a
             byte) is simply not a string byte, not a crash. *)
          match int_of_string_opt c with
          | Some c when c >= 0 && c < 256 -> Some c
          | _ -> None)
      | Ast.Char c when Uchar.to_int c < 128 -> Some (Uchar.to_int c)
      | _ -> None
    in
    try
      if Uint32.of_int (List.length args) <> n then raise Exit;
      let b = Bytes.create (Uint32.to_int n) in
      List.iteri
        (fun i arg ->
          match byte_of_arg arg with
          | Some c -> Bytes.set b i (Char.chr c)
          | None -> raise Exit)
        args;
      let s = Bytes.to_string b in
      if String.is_valid_utf_8 s && Re.execp reasonable_string s then Some s
      else None
    with Exit -> None

(* As [string_args], but for an [i16] array: each argument is a UTF-16 code unit
   (0..0xffff), decoded back to the source string. Falls back ([None]) on a
   value out of range or a lone surrogate, so a genuine numeric array stays one. *)
let wide_string_args n args =
  if n = Uint32.zero then None
  else
    let unit_of_arg arg =
      match arg.Ast.desc with
      | Ast.Int c -> (
          match int_of_string_opt c with
          | Some c when c >= 0 && c < 0x10000 -> Some c
          | _ -> None)
      | Ast.Char c when Uchar.to_int c < 0x10000 -> Some (Uchar.to_int c)
      | _ -> None
    in
    try
      if Uint32.of_int (List.length args) <> n then raise Exit;
      let units =
        List.map
          (fun arg ->
            match unit_of_arg arg with Some c -> c | None -> raise Exit)
          args
      in
      match Wax_utils.Unicode.utf16_decode units with
      | Some s when Re.execp reasonable_string s -> Some s
      | _ -> None
    with Exit -> None

let inttype ty : Ast.valtype =
  match ty with
  | `I32 -> I32
  | `I64 -> I64
  | `F32 -> I32
  | `F64 -> I64
  | _ -> assert false

(* The scalar type one lane of a SIMD shape holds — the type a lane EXTRACTION
   produces (a narrow [i8x16]/[i16x8] lane extends to an i32, as in Wasm). *)
let lane_valtype (s : Wax_wasm.Ast.vec_shape) : Ast.valtype =
  match s with
  | I8x16 | I16x8 | I32x4 -> I32
  | I64x2 -> I64
  | F32x4 -> F32
  | F64x2 -> F64

let floattype ty : Ast.valtype =
  match ty with
  | `I32 -> F32
  | `I64 -> F64
  | `F32 -> F32
  | `F64 -> F64
  | _ -> assert false

let int_un_op ~faithful i0 sz (op : Src.int_un_op) =
  (* A Wax instruction at the source instruction's span. Built fresh rather than
     with [{ i0 with desc }]: a Wasm and a Wax instruction differ in the type of
     their call-target hints, so one cannot be reinterpreted as the other. *)
  let with_loc (i : _ Ast.instr_desc) : _ Ast.instr =
    {
      desc = i;
      info = i0.Src.info;
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  (* A no-argument instruction method [recv.meth()]. *)
  let method_call recv meth =
    with_loc (Call (with_loc (StructGet (recv, Ast.no_loc meth)), []))
  in
  let* recv = Stack.try_pop_tagged in
  let e' = Option.map fst recv in
  (* The operand's own width tag (its flexibility): a method-form op below
     ([clz]/[ctz]/[popcnt]/[extend8_s]/[extend16_s]) has result width = receiver
     width, so it carries the receiver's flexibility to its result — an erasing
     consumer then pins it, and the pin (a cast on the result) propagates back to
     the receiver. Ops that fix a concrete result width (a cast: [trunc], [eqz]'s
     i32) are grounded, [None]. *)
  let recv_w = match recv with Some (_, w) -> w | None -> None in
  let e ty = match e' with Some e -> e | None -> typed_hole ty in
  (* Materialise the operand of a TRUNCATION with its float width [ty] cast on,
     when the operand is inlined. The reconciliation would place the same cast for
     a valid module (the truncation's surface [as int] carries the RESULT width, so
     the operand's recorded width is what the typer pins it from — verified
     byte-identical over the corpus and by fuzz/drop-width.sh), and this is kept
     for the two things it does that the reconciliation cannot:
     - a source module the validator would REJECT keeps its ill-typedness visible:
       without the cast, [(0 as i32) as i64_s_strict] re-reads as an integer
       extend — a different, well-typed program — instead of a truncation whose
       operand is not a float (the spec suite asserts that Wax typing mirrors Wasm
       validation on such a module, see test/wasm_test_suite.expected);
     - it keeps the [eqz] special case below matchable ([sz] is [i32] there, so no
       cast is added and the [BinOp] shape shows through).
     An [i32] target needs no cast (i32 is the re-parse default) and an absent
     operand is already the typed hole [e] builds. *)
  let pin ty =
    let x = e ty in
    match (e', ty) with
    | Some _, (Ast.I64 | F32 | F64) -> cast_to (Valtype ty) x
    | _ -> x
  in
  (* Width-preserving method-form ops carry the receiver's flexibility; the rest
     produce a concrete (grounded) result. *)
  let result_w =
    match op with
    | Clz | Ctz | Popcnt | ExtendS (`_8 | `_16) -> recv_w
    | _ -> None
  in
  (* The type the opcode's result HAS, whatever the flexibility tag says: [eqz]
     yields i32 whatever its operand's width, every other op here the integer
     size the opcode names. Recorded so a re-inference at another width is
     caught — and, for a width-preserving method ([.clz()] and friends), that
     record is what pins an adaptive receiver too: the typer's pin lands on the
     call's RESULT and reaches the receiver through it ([i64.clz] on a
     select-of-holes would otherwise re-parse as [i32.clz]). *)
  let result_ty = match op with Eqz -> Ast.I32 | _ -> inttype sz in
  Stack.push_num result_w
  @@ expect result_ty
       (match op with
       | Clz -> method_call (e (inttype sz)) "clz"
       | Ctz -> method_call (e (inttype sz)) "ctz"
       | Popcnt -> method_call (e (inttype sz)) "popcnt"
       | Eqz -> (
           let operand = pin (inttype sz) in
           match operand.Ast.desc with
           (* [eqz] of an equality is exactly the negated comparison; recover
           [i32.eqz (ref.eq a b)] — how [a != b] on references lowers — as
           [a != b] rather than [!(a == b)]. ([sz] is [i32] here, so [pin] leaves
           the [BinOp] shape untouched.) Under [--faithful] this rewrite is off:
           it turns [t.eq; i32.eqz] into a single [t.ne], so keep the [!(...)]
           form, which re-lowers to the original [eq; eqz] pair. *)
           | BinOp ({ Ast.desc = Ast.Eq; _ }, e1, e2) when not faithful ->
               with_loc (BinOp (op_loc i0.info Ast.Ne, e1, e2))
           | _ -> with_loc (UnOp (op_loc i0.info Ast.Not, operand)))
       | Trunc (f, signage) ->
           (* The operand is a float of [f]'s width, NOT [floattype sz] ([sz] is the
           integer *result* size — wrong for e.g. [i32.trunc_f64], whose operand
           is f64 not f32). Unlike the trunc's own [as int] cast (which fixes the
           *result* width), nothing here pins the *source* float width, so an
           inlined operand must carry it explicitly: a bare float literal
           re-defaults to f64 (so an f32 source drifts), and an integer-valued
           float const prints as a bare integer that re-defaults to i32 (so even
           an f64 source drifts) — both silently changing which inputs trap. Pin
           it with a cast, as [Reinterpret] does; [simplify] drops the pin again
           when the operand already settles on [fty] (a plain f64 literal). *)
           let fty : Ast.valtype = match f with `F32 -> F32 | `F64 -> F64 in
           cast_to (Signedtype { typ = sz; signage; strict = true }) (pin fty)
       | TruncSat (f, signage) ->
           let fty : Ast.valtype = match f with `F32 -> F32 | `F64 -> F64 in
           cast_to (Signedtype { typ = sz; signage; strict = false }) (pin fty)
       | Reinterpret ->
           (* [to_bits]/[from_bits] are the one method pair whose result width is
              NOT their receiver's (they cross the int/float divide), so a pin on
              the result cannot reach the receiver and the reconciliation has no way
              to place this cast. Without it the receiver re-defaults and the method
              picks the wrong result type, which does not even type-check. *)
           method_call
             (let e = e (floattype sz) in
              if e' = None then e else cast_to (Valtype (floattype sz)) e)
             "to_bits"
       | ExtendS `_32 ->
           (* i64.extend32_s, rendered [((operand as i64) as i32) as i64_s] so
           [to_wasm] re-fuses it: the [as i32] wraps an i64 to i32 and the outer
           [as i64_s] sign-extends, and the fusion keys on the inner operand
           being typed i64. Pin the i64 source in every case — a bare [i64.const]
           source would re-default to i32 (collapsing the wrap and re-emitting the
           value-equal but distinct [extend_i32_s]), and a dead-code hole is
           polymorphic so [(_ as i64)] pins it i64 and the pair re-fuses to
           [extend32_s] rather than dropping the wrap to [extend_i32_s]. A
           non-constant i64 operand is already i64-typed, so [pin] is a no-op and
           [simplify] leaves the wrap. *)
           cast_to
             (Signedtype { typ = sz; signage = Signed; strict = false })
             (cast_to (Valtype (inttype `I32)) (pin (inttype `I64)))
       | ExtendS `_8 -> method_call (e (inttype sz)) "extend8_s"
       | ExtendS `_16 -> method_call (e (inttype sz)) "extend16_s")

(* Pop an operand for a method-form intrinsic, ascribing it the operator's
   scalar type [ty]. A non-inlinable operand becomes a typed hole [(_ as ty)]
   rather than a bare [_], so the call type-checks in unreachable code where the
   operand stack is polymorphic (mirrors the unary ops [int_un_op]/[float_un_op]).
   The arithmetic/comparison operators lower to plain [BinOp]s, which accept a
   polymorphic operand for *type-checking*, but for *width fidelity* they pin one
   anchor-free hole with the opcode type too (see [int_bin_op]'s [symbol]). *)
let pop_typed ty =
  let* o = Stack.try_pop in
  return (match o with Some e -> e | None -> typed_hole ty)

(* Give a conversion's absent operand — a hole on the polymorphic stack in dead
   code — the opcode's source type, [(_ as src)], so the conversion survives the
   round trip. A width-narrowing/widening conversion ([wrap]/[extend]/[demote]/
   [promote]) whose source width the surface [as] cannot recover from a bare [_]
   would otherwise drop entirely ([unreachable; i32.wrap_i64; drop] losing the
   wrap): pinning the source makes [(_ as i64) as i32] re-emit the [wrap]. The
   same holds for the reference conversions [ref.i31] ([(_ as i32) as &i31]) and
   [i31.get_s/u] ([(_ as &?i31) as i32_s]), whose surface [as] erases the source
   hierarchy — a bare [_ as &i31] / [_ as i32_s] re-types the hole directly to the
   target and drops the op. A [select] operand is grounded for the same reason,
   as [convert_src] does below: an untyped [select] of holes re-parses
   type-adaptively (a numeric select re-defaults to i32, a reference select loses
   its hierarchy), so under the outer [as] a bare [(_?_:_) as i32_s] takes the
   target type directly and drops the op ([select; i31.get_s] losing the
   [i31.get_s]); pinning the source ([((_?_:_) as &?i31) as i32_s]) keeps it. (The
   cross-hierarchy [extern.convert_any] / [any.convert_extern] need the still
   wider [convert_src] below, which also grounds a forwarding [br_on_null].) A
   present, concrete operand is returned unchanged, so reachable code is untouched
   — the redundant pin on a grounded select is pruned by the same reparse-adaptive
   mirror in the typer that keeps the load-bearing one. Mirrors the dead-code
   numeric-operand pins in [int_bin_op]/[pop_typed]. *)
let type_hole_src src e =
  match e.Ast.desc with
  | Ast.Hole | Ast.Select _ -> cast_to (Valtype src) e
  | _ -> e

(* As [type_hole_src] for the cross-hierarchy converts ([extern.convert_any] /
   [any.convert_extern]), but also grounds an operand whose printed form re-parses
   type-ADAPTIVELY and would otherwise take the target hierarchy under the outer
   [as], collapsing the convert into a plain [ref.null]: a hole, and a [select]
   whose arms are adaptive (its result type is its arms'). A bare [null] arrives
   already cast ([ref.null any] -> [null as &?any]) so is left alone; a concrete
   reference fixes the convert on its own and is left alone. The typer keeps the
   pin only when load-bearing (its [restore_inner] mirrors [reparse_adaptive]) and
   prunes it for a concrete operand, so reachable non-adaptive code is untouched. *)
(* A bare HOLE is pinned NON-NULL ([nullable = false], the default): it stands for
   a value off the polymorphic bottom, which is non-null (the bottom reference is a
   subtype of every non-nullable type), and the converts propagate that — pinned
   nullable, the convert yields [&?extern] where the original yielded [&extern] and
   a consumer typed non-null (a [(ref extern)] local) rejects the decompiled Wax
   outright, breaking the round trip. Non-null satisfies a nullable consumer too,
   by subtyping.

   Everywhere else the source's own nullability is kept: a [select]'s arms may be
   concrete nullable values (or [null] literals), and a [br_on_null]'s tested ref
   and a [ref.as_non_null]'s operand are nullable by construction — narrowing any
   of those would be a real cast, not a pin. *)
(* A bare hole — the shape [convert_src] pins non-null (see there). *)
let is_bare_hole (e : _ Ast.instr) =
  match e.Ast.desc with Ast.Hole -> true | _ -> false

(* The hierarchy a heaptype's own name settles a value in; [None] where the name
   alone does not say (a [Type]/[Exact] reference could name a func, a
   struct/array, or a continuation type). *)
let hierarchy_top (t : Ast.heaptype) =
  match t with
  | Any | Eq | I31 | Struct | Array | None_ -> Some `Any
  | Extern | NoExtern -> Some `Extern
  | Func | NoFunc -> Some `Func
  | Exn | NoExn -> Some `Exn
  | Cont | NoCont -> Some `Cont
  | Type _ | Exact _ -> None

(* As [hierarchy_top], resolving a named type through the module's definitions
   (a struct/array type is in the [any] hierarchy, a func type in [func], a
   continuation type in [cont]); [None] when the name is unknown here (an
   implicit type interned for an inline signature). *)
let heaptype_hierarchy ctx (t : Ast.heaptype) =
  match hierarchy_top t with
  | Some h -> Some h
  | None -> (
      match t with
      | Type n | Exact n -> (
          match src_typedef ctx n with
          | Some { Src.typ = Struct _ | Array _; _ } -> Some `Any
          | Some { Src.typ = Func _; _ } -> Some `Func
          | Some { Src.typ = Cont _; _ } -> Some `Cont
          | None -> None)
      | _ -> None)

(* The [backing_class] a value of heap type [t] presents: its hierarchy, and
   whether it is provably an [eq]-subtype ([Any] itself and the unresolvable
   named types are not). *)
let heaptype_class ctx (t : Ast.heaptype) =
  match heaptype_hierarchy ctx t with
  | None -> Unknown_class
  | Some hier -> Ref_class { hier; eq = hier = `Any && t <> Any }

let valtype_class ctx (t : Ast.valtype) =
  match t with Ast.Ref { typ; _ } -> heaptype_class ctx typ | _ -> Value_class

(* The per-result classes of a multi-value signature, in result order. *)
let result_classes ctx (results : Src.valtype array) =
  Array.map (fun t -> valtype_class ctx (valtype ctx t)) results

(* The class of the result [from_top] positions below a residual's topmost
   value — what the residual hands a reconnecting hole once the [from_top]
   claims interposed holes are owed have eaten its top. *)
let indexed_class (classes : backing_class array) ~from_top =
  let i = Array.length classes - 1 - from_top in
  if i < 0 then Unknown_class else classes.(i)

(* Classify the residual [b] that [Stack.effective_backing] says a bare hole
   reconnects to: what [b]'s own printed form re-types it as, when the node
   (with the context's tables) can say. A [Get] is a local or global — whose
   declared type is its re-parse type — or, when neither table knows the name,
   a function reference. A multi-value call residual does not name its results
   on the node: a direct call is looked up by its Wax name
   ([ctx.multi_ref_results], filled at emission); a [call_ref]'s callee cast
   names the function type, resolved through the module; a [call_indirect]
   through an inline signature carries the (already converted) type itself.
   Reconnection is POSITIONAL — the hole takes the residual's topmost value not
   yet eaten by interposed claims — so a multi-value residual is indexed by
   [from_top] (the scan's leftover claims); a single-value node with
   [from_top > 0] cannot occur (the scan absorbs a fully-claimed entry). *)
let rec backing_class_of ctx ~from_top (b : _ Ast.instr) =
  match b.Ast.desc with
  | Ast.Call ({ Ast.desc = Ast.Get f; _ }, _) -> (
      match Hashtbl.find_opt ctx.multi_ref_results f.Ast.desc with
      | Some classes -> indexed_class classes ~from_top
      | None -> Unknown_class)
  | Ast.Call
      ( {
          Ast.desc = Ast.Cast (_, Valtype (Ref { typ = Type tn | Exact tn; _ }));
          _;
        },
        _ ) -> (
      match src_typedef ctx tn with
      | Some { Src.typ = Func { results; _ }; _ } ->
          indexed_class (result_classes ctx results) ~from_top
      | _ -> Unknown_class)
  | Ast.Call ({ Ast.desc = Ast.Cast (_, Functype { sign; _ }); _ }, _) ->
      indexed_class (Array.map (valtype_class ctx) sign.Ast.results) ~from_top
  | _ when from_top > 0 -> Unknown_class
  | Ast.Null -> Null_class
  | Ast.NonNull e -> backing_class_of ctx ~from_top e
  | Ast.Cast (_, Valtype (Ref { typ; _ })) -> heaptype_class ctx typ
  | Ast.Cast (_, Functype _) -> Ref_class { hier = `Func; eq = false }
  | Ast.Struct _ | Ast.StructDefault _ | Ast.StructDesc _
  | Ast.StructDefaultDesc _ | Ast.Array _ | Ast.ArrayFixed _
  | Ast.ArraySegment _ | Ast.String _ ->
      Ref_class { hier = `Any; eq = true }
  | Ast.ContNew _ -> Ref_class { hier = `Cont; eq = false }
  | Ast.Get n -> (
      match Hashtbl.find_opt ctx.local_valtypes n.Ast.desc with
      | Some t -> valtype_class ctx t
      | None -> (
          match Hashtbl.find_opt ctx.global_valtypes n.Ast.desc with
          | Some t -> valtype_class ctx t
          | None -> Ref_class { hier = `Func; eq = false }))
  | _ -> Unknown_class

(* Whether [b] is settled by its own printed form in the hierarchy [src] (a
   convert's source), or is a null, which every hierarchy accepts. Only then
   may a cross-hierarchy convert leave its absent operand BARE: the hole
   reconnects to [b] and the convert's own [as] surface lowers over the real
   value, one opcode, exactly the source. Pinned instead, the pin lands on the
   reconnected value and materialises as a [ref.cast] the source never had (the
   backing-scan grid's founding convert cluster). *)
let backing_in_hierarchy ctx src ~from_top (b : _ Ast.instr) =
  match backing_class_of ctx ~from_top b with
  | Null_class -> true
  | Ref_class { hier; _ } -> hier = src
  | Value_class | Unknown_class -> false

(* The opposite polarity: [b] provably re-types OUTSIDE the hierarchy [src] (a
   wrong-hierarchy reference, or a non-reference value). A top-of-hierarchy pin
   over such a backing would capture it and materialise as the very
   hierarchy-crossing it should not add, so the caller pins the source
   hierarchy's BOTTOM instead — the claim-free ascription (see
   [is_bottom_heaptype]) that grounds the hole without touching [b]. Only an
   [(@if)] can make this reachable: in plain Wasm the validator types the
   residual into the consumer and rejects, while an annotation's branches
   consume it only per configuration. An UNCLASSIFIABLE backing stays on the
   top-of-hierarchy pin: in valid annotation-free input whatever the pin
   captures is right-hierarchy (the validator typed it into the consumer), so
   the pin is inert after unification — while a claim-free pin would strand
   the residual the source consumed. *)
let backing_wrong_hierarchy ctx src ~from_top (b : _ Ast.instr) =
  match backing_class_of ctx ~from_top b with
  | Ref_class { hier; _ } -> hier <> src
  | Value_class -> true
  | Null_class | Unknown_class -> false

(* As [backing_wrong_hierarchy] for [ref.eq]: [b] provably re-types as
   something other than an [eq]-subtype, so a bare [_ == _] hole capturing it
   would not type-check (and an [(_ as &?eq)] pin capturing it would be a
   hierarchy crossing). *)
let backing_not_eq ctx ~from_top (b : _ Ast.instr) =
  match backing_class_of ctx ~from_top b with
  | Ref_class { eq; _ } -> not eq
  | Value_class -> true
  | Null_class | Unknown_class -> false

(* As [backing_wrong_hierarchy] for [ref.is_null], which accepts every
   reference: only a provable NON-reference re-typing is wrong (the bare [!_]
   over it would re-default to [i32.eqz], and an [(_ as &?any)] pin over it
   would not type-check). *)
let backing_not_ref ctx ~from_top (b : _ Ast.instr) =
  match backing_class_of ctx ~from_top b with
  | Value_class -> true
  | Ref_class _ | Null_class | Unknown_class -> false

let rec convert_src ?(nullable = true) src e =
  match e.Ast.desc with
  | Ast.Hole ->
      cast_to
        (Valtype
           (match src with
           | Ast.Ref r when not nullable -> Ast.Ref { r with nullable = false }
           | t -> t))
        e
  | Ast.Select _ -> cast_to (Valtype src) e
  (* [br_on_null] forwards its operand's value on the fall-through (its non-null
     version), so the source cast must pin that operand INSIDE the branch, not wrap
     the branch result: wrapping would cast the branch's already-[any]-defaulted
     result and insert a spurious [extern.convert_any]. Recurse to the innermost
     hole. ([br_on_non_null] does NOT forward — its fall-through consumes the
     operand and yields nothing — so it never appears as a convert's value operand
     and needs no case here.) *)
  | Ast.Br_on_null (l, inner) ->
      { e with Ast.desc = Ast.Br_on_null (l, convert_src src inner) }
  (* A [br_on_null] whose label carries values delivers them THEN the tested ref;
     the operand is a [Sequence] of [branch-values…; tested-ref], and its
     fall-through non-null ref — the value a following convert consumes — takes
     the LAST element's (the tested ref's) hierarchy, so pin that last element.
     ([ref.as_non_null] on the tested ref shows as a [NonNull] wrapper; recurse
     through it to the hole so the pin lands on the reference itself.) *)
  | Ast.Sequence (_ :: _ as l) ->
      let rev = List.rev l in
      let last = convert_src src (List.hd rev) in
      { e with Ast.desc = Ast.Sequence (List.rev (last :: List.tl rev)) }
  | Ast.NonNull inner ->
      { e with Ast.desc = Ast.NonNull (convert_src src inner) }
  | _ -> e

(* Ground the tested-ref of a forwarding [br_on_null] residual sitting on top of
   the stack, for a following cross-hierarchy convert. A [br_on_null] into a block
   with a ref result pushes an arity >= 2 residual (the delivered branch values
   plus the fall-through non-null ref); that residual cannot be split, so the
   convert's own pop reads a fresh hole which, on re-parse, reconnects to the
   fall-through ref — typed by the block's declared ref result (e.g. [(ref null
   any)]). The convert's source pin on that hole would then cross hierarchies and
   materialise a spurious extra opcode (an [extern.convert_any] ahead of the
   [any.convert_extern]). Pinning the residual's tested-ref operand to the convert
   SOURCE instead grounds the fall-through ref at the source hierarchy, so the
   hole reconnects there and the convert lowers to exactly one opcode. A no-op
   unless the top is such a residual; the arity-1 (no-result-block) case is a
   directly-popped [br_on_null] operand already handled by [convert_src]. *)
let pin_forwarding_source src stack =
  match stack with
  | (a, w, ({ Ast.desc = Ast.Br_on_null (l, inner); _ } as node)) :: rem
    when a >= 2 ->
      ( ( a,
          w,
          { node with Ast.desc = Ast.Br_on_null (l, convert_src src inner) } )
        :: rem,
        () )
  | _ -> (stack, ())

(* [pop_typed] carrying the receiver's width tag, for a method-form op that
   inherits its receiver's flexibility (a rotate, a float method). A hole is
   grounded ([None]). *)
let pop_typed_tagged ty =
  let* o = Stack.try_pop_tagged in
  return (match o with Some (e, w) -> (e, w) | None -> (typed_hole ty, None))

(* Whether a popped operand ANCHORS its own type — its printed form fixes it, so a
   consumer need not ascribe one: it is present ([Some]), carries no flexible width
   tag ([None]), and is not an adaptive tree. An untyped [select] of holes is pushed
   with a [None] tag (its arms carry no width) but re-parses like a bare hole, so it
   anchors nothing. Only the TYPED [select] consumer still asks: its arms must carry
   the select's declared type, which for a REFERENCE type the width reconciliation
   cannot supply (it covers the numeric scalars only), and pinning an arm the typer
   already placed in another hierarchy would be a static error. The numeric
   operators no longer ask — each operand carries its own recorded width and the
   typer places whatever pin is needed. *)
let is_anchor = function
  | Some (e, None) -> not (reparse_adaptive e)
  | _ -> false

let int_bin_op (i0 : _ Src.instr) sz (op : Src.int_bin_op) =
  (* A Wax instruction at the source instruction's span. Built fresh rather than
     with [{ i0 with desc }]: a Wasm and a Wax instruction differ in the type of
     their call-target hints, so one cannot be reinterpreted as the other. *)
  let with_loc (i : _ Ast.instr_desc) : _ Ast.instr =
    {
      desc = i;
      info = i0.Src.info;
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  (* An absent operand — a pop from the empty/absent stack, i.e. dead code — is a
     hole carrying the operator's operand type as its recorded width, which is what
     the typer grounds it from if the printed form would resolve elsewhere. A
     PRESENT operand already carries its own record from where it was pushed, so
     nothing distinguishes the two here any more (no anchor analysis, no pin
     placement: the reconciliation decides all of that from the records). *)
  let bare () = expect (inttype sz) (Ast.no_loc_instr Ast.Hole) in
  let arith = Some (sz :> [ `I32 | `I64 | `F32 | `F64 ]) in
  let operand o = match o with Some (e, _) -> e | None -> bare () in
  (* An arithmetic operator yields the operand width, so [a + b] round-trips to
     that width via the sum's own type. Its result stays a flexible literal tree
     (tagged) only when BOTH operands are; if either is grounded the sum is
     grounded too ([x + 1] re-parses to [x]'s width on its own) and takes no tag,
     so a downstream eraser does not read it as flexible. *)
  let symbol width op =
    let* o2 = Stack.try_pop_tagged in
    let* o1 = Stack.try_pop_tagged in
    let e1 = operand o1 and e2 = operand o2 in
    let both_flexible =
      match (o1, o2) with
      | Some (_, Some _), Some (_, Some _) -> true
      | _ -> false
    in
    let width = if both_flexible then width else None in
    (* The sum's own type is the operand width whether or not the tag above keeps
       it flexible. *)
    Stack.push_num width
      (expect (inttype sz) (with_loc (BinOp (op_loc i0.info op, e1, e2))))
  in
  (* A comparison yields i32 whatever its operands' width, so its surface *erases*
     that width ([(4096 >>u 40) == 0] would re-default the shift to i32 and flip
     true->false). Nothing is inserted for it: each operand carries its own
     recorded width, and the typer pins whichever one would resolve elsewhere. The
     i32 result carries no tag. *)
  let compare op =
    let* o2 = Stack.try_pop_tagged in
    let* o1 = Stack.try_pop_tagged in
    let e1 = operand o1 and e2 = operand o2 in
    (* The i32 result carries no width TAG (it is not flexible), but the opcode
       states it, so record it. *)
    Stack.push 1 (expect I32 (with_loc (BinOp (op_loc i0.info op, e1, e2))))
  in
  (* [rotl]/[rotr]: result width = receiver width, so it carries the receiver's
     flexibility (the count arg is pinned by the method once the receiver fixes
     it). Like [clz], an erasing consumer then pins it back to the receiver. *)
  let meth name =
    let* e2 = pop_typed (inttype sz) in
    let* e1, w1 = pop_typed_tagged (inttype sz) in
    Stack.push_num w1
      (expect (inttype sz)
         (with_loc (Call (with_loc (StructGet (e1, Ast.no_loc name)), [ e2 ]))))
  in
  match op with
  | Add -> symbol arith Add
  | Sub -> symbol arith Sub
  | Mul -> symbol arith Mul
  | Div s -> symbol arith (Div (Some s))
  | Rem s -> symbol arith (Rem s)
  | And -> symbol arith And
  | Or -> symbol arith Or
  | Xor -> symbol arith Xor
  | Shl -> symbol arith Shl
  | Shr s -> symbol arith (Shr s)
  | Rotl -> meth "rotl"
  | Rotr -> meth "rotr"
  | Eq -> compare Eq
  | Ne -> compare Ne
  | Lt s -> compare (Lt (Some s))
  | Gt s -> compare (Gt (Some s))
  | Le s -> compare (Le (Some s))
  | Ge s -> compare (Ge (Some s))

let float_un_op i0 sz (op : Src.float_un_op) =
  (* A Wax instruction at the source instruction's span. Built fresh rather than
     with [{ i0 with desc }]: a Wasm and a Wax instruction differ in the type of
     their call-target hints, so one cannot be reinterpreted as the other. *)
  let with_loc (i : _ Ast.instr_desc) : _ Ast.instr =
    {
      desc = i;
      info = i0.Src.info;
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  (* A no-argument instruction method [recv.meth()]. *)
  let method_call recv meth =
    with_loc (Call (with_loc (StructGet (recv, Ast.no_loc meth)), []))
  in
  let* recv = Stack.try_pop_tagged in
  let e' = Option.map fst recv in
  let recv_w = match recv with Some (_, w) -> w | None -> None in
  let e ty = match e' with Some e -> e | None -> typed_hole ty in
  (* As [int_un_op]'s [pin], for a CONVERT's integer source: its surface
     ([8 as f32_s]) carries the result width, not the source's. The reconciliation
     would place the same cast for a valid module; it is kept so that an ill-typed
     source module ([f32.convert_i64_s] of an [i32.const]) still decompiles to Wax
     the typer rejects, rather than to a different well-typed conversion. *)
  (* [i32] is normally the re-parse default, so pinning a convert's i32 source
     would be noise — EXCEPT over an operand that re-parses ADAPTIVELY (a hole, or
     an untyped [select] of them). Such an operand does not default: under the
     convert's own [as f32_u] it takes the TARGET type instead, and the conversion
     collapses to nothing — [f32.convert_i32_u] of a dead-code select vanished
     across the round trip (a wasm-smith width/faithful finding). Pin it there, so
     the source width is stated and the convert survives. *)
  let pin_src ty x =
    match (e', ty) with
    | Some _, (Ast.I64 | F32 | F64) -> cast_to (Valtype ty) x
    | Some e, Ast.I32 when reparse_adaptive e -> cast_to (Valtype ty) x
    | _ -> x
  in
  (* [neg]/[abs]/…/[sqrt] have result width = operand width, so they carry the
     operand's flexibility (like [clz]); [convert]/[reinterpret] fix a concrete
     result width via a cast, so they are grounded ([None]). *)
  let result_w =
    match op with
    | Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt -> recv_w
    | Convert _ | Reinterpret -> None
  in
  (* Every float unary op's result has the float width the opcode names — the
     conversions ([convert]/[reinterpret]) too, whose operand is an integer. That
     record is also what grounds an ADAPTIVE receiver (an untyped dead-code
     [select] of holes, whose printed form would re-default to i32 under [-] or to
     f64 under [.floor()]): the ops whose result width IS their receiver's carry
     the pin back to it through the call, so nothing has to be inserted on the
     receiver itself. *)
  Stack.push_num result_w
  @@ expect (floattype sz)
       (match op with
       | Neg -> with_loc (UnOp (op_loc i0.info Ast.Neg, e (floattype sz)))
       | Abs -> method_call (e (floattype sz)) "abs"
       | Ceil -> method_call (e (floattype sz)) "ceil"
       | Floor -> method_call (e (floattype sz)) "floor"
       | Trunc -> method_call (e (floattype sz)) "trunc"
       | Nearest -> method_call (e (floattype sz)) "nearest"
       | Sqrt -> method_call (e (floattype sz)) "sqrt"
       | Convert (sz', signage) ->
           let ity = inttype (sz' :> [ `I32 | `I64 | `F32 | `F64 ]) in
           cast_to
             (Signedtype { typ = sz; signage; strict = false })
             (pin_src ity (e ity))
       | Reinterpret ->
           (* As [int_un_op]'s [Reinterpret]: the bits methods cross the int/float
              divide, so no pin on the result can reach the receiver. *)
           method_call
             (let e = e (inttype sz) in
              if e' = None then e else cast_to (Valtype (inttype sz)) e)
             "from_bits")

let float_bin_op i0 sz (op : Src.float_bin_op) =
  (* A Wax instruction at the source instruction's span. Built fresh rather than
     with [{ i0 with desc }]: a Wasm and a Wax instruction differ in the type of
     their call-target hints, so one cannot be reinterpreted as the other. *)
  let with_loc (i : _ Ast.instr_desc) : _ Ast.instr =
    {
      desc = i;
      info = i0.Src.info;
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  (* As for [int_bin_op]: an arithmetic operator preserves the operand width and
     its result stays flexible only when both operands are; an absent operand is a
     hole carrying the operator's type as its record, and nothing else is
     inserted — the typer grounds whatever would resolve elsewhere. *)
  let bare () = expect (floattype sz) (Ast.no_loc_instr Ast.Hole) in
  let arith = Some (sz :> [ `I32 | `I64 | `F32 | `F64 ]) in
  let operand o = match o with Some (e, _) -> e | None -> bare () in
  let symbol width op =
    let* o2 = Stack.try_pop_tagged in
    let* o1 = Stack.try_pop_tagged in
    let e1 = operand o1 and e2 = operand o2 in
    let both_flexible =
      match (o1, o2) with
      | Some (_, Some _), Some (_, Some _) -> true
      | _ -> false
    in
    let width = if both_flexible then width else None in
    Stack.push_num width
      (expect (floattype sz) (with_loc (BinOp (op_loc i0.info op, e1, e2))))
  in
  let compare op =
    let* o2 = Stack.try_pop_tagged in
    let* o1 = Stack.try_pop_tagged in
    let e1 = operand o1 and e2 = operand o2 in
    (* The i32 result carries no width TAG (it is not flexible), but the opcode
       states it, so record it. *)
    Stack.push 1 (expect I32 (with_loc (BinOp (op_loc i0.info op, e1, e2))))
  in
  (* [min]/[max]/[copysign]: result width = receiver width (as [rotl]). *)
  let meth name =
    let* e2 = pop_typed (floattype sz) in
    let* e1, w1 = pop_typed_tagged (floattype sz) in
    Stack.push_num w1
      (expect (floattype sz)
         (with_loc (Call (with_loc (StructGet (e1, Ast.no_loc name)), [ e2 ]))))
  in
  match op with
  | Add -> symbol arith Add
  | Sub -> symbol arith Sub
  | Mul -> symbol arith Mul
  | Div -> symbol arith (Div None)
  | Min -> meth "min"
  | Max -> meth "max"
  | CopySign -> meth "copysign"
  | Eq -> compare Eq
  | Ne -> compare Ne
  | Lt -> compare (Lt None)
  | Gt -> compare (Gt None)
  | Le -> compare (Le None)
  | Ge -> compare (Ge None)

let blocktype ctx (typ : Src.blocktype option) =
  match typ with
  | None -> { Ast.params = [||]; results = [||] }
  | Some (Valtype ty) -> { Ast.params = [||]; results = [| valtype ctx ty |] }
  | Some (Typeuse (ty_idx, sign)) ->
      let { Src.params; results } =
        match (ty_idx, sign) with
        | _, Some sign -> sign
        | Some idx, _ -> (
            (* A numeric [(type N)] may name an implicit type synthesised from an
               inline signature, which lives in [ctx.implicit_types], not the
               declared [types] sequence — check it first, as [type_arity] does,
               before [lookup_type]. *)
            match implicit_functype ctx idx with
            | Some sign -> sign
            | None -> (
                let ty = lookup_type ctx Type idx in
                match ty.typ with
                | Struct _ | Array _ | Cont _ -> assert false
                | Func sign -> sign))
        | None, None -> assert false
      in
      {
        Ast.params =
          Array.map
            (fun p ->
              (* A *Wasm* parameter entry, so not [Ast.param_type] (which reads a
                 Wax one). *)
              annotated p.Wax_utils.Ast.info None
                (valtype ctx (snd p.Wax_utils.Ast.desc)))
            params;
        results = Array.map (fun t -> valtype ctx t) results;
      }

let label_name (label : Src.name option) =
  Option.map (fun (l : Src.name) -> l.Wax_utils.Ast.desc) label

let label_targeted ?self (instrs : _ Src.instr list) =
  (* [self] is the block's own source label name, if any. A symbolic [br $self]
     targets this block regardless of nesting depth (unlike a numeric [br N],
     whose depth is tracked), so match an [Id] reference against it. This keeps
     a block reachable only by a name that [sanitize_identifier] later rejects
     (so it renders under the fallback "l") counted as targeted, which reserves
     that fallback name and prevents an inner block from colliding with it. *)
  let hit depth (idx : Src.idx) =
    match idx.desc with
    | Num n -> Uint32.to_int n = depth
    | Id name -> self = Some name
  in
  (* Explicit recursion rather than [List.exists (one depth)]: [any] is called
     once per (nested) block, so a partial-application closure here allocated on
     every block — the hottest allocation in [modulefield]. *)
  let rec any depth = function
    | [] -> false
    | i :: rest -> one depth i || any depth rest
  and one depth (i : _ Src.instr) =
    match i.desc with
    | Br i
    | Br_if i
    | Br_on_null i
    | Br_on_non_null i
    | Br_on_cast (i, _, _)
    | Br_on_cast_fail (i, _, _)
    | Br_on_cast_desc_eq (i, _, _)
    | Br_on_cast_desc_eq_fail (i, _, _) ->
        hit depth i
    | Br_table (labels, lab) -> List.exists (hit depth) (lab :: labels)
    | Block { block; _ } | Loop { block; _ } -> any (depth + 1) block.desc
    | If { if_block; else_block; _ } ->
        any (depth + 1) if_block.desc || any (depth + 1) else_block.desc
    | TryTable { block; catches; _ } ->
        any (depth + 1) block.desc
        || List.exists
             (fun (c : Src.catch) ->
               match c with
               | Catch (_, l) | CatchRef (_, l) | CatchAll l | CatchAllRef l ->
                   hit depth l)
             catches
    | Try { block; catches; catch_all; _ } -> (
        any (depth + 1) block.desc
        || List.exists
             (fun (_, b) -> any (depth + 1) b.Wax_utils.Ast.desc)
             catches
        ||
        match catch_all with
        | Some b -> any (depth + 1) b.Ast.desc
        | None -> false)
    | Resume (_, handlers)
    | ResumeThrowRef (_, handlers)
    | ResumeThrow (_, _, handlers) ->
        List.exists
          (fun (c : Src.on_clause) ->
            match c with OnLabel (_, l) -> hit depth l | OnSwitch _ -> false)
          handlers
    (* Folded WAT form: the operands [l] and the head [i] run at this same
       depth (the wrapper opens no block scope), mirroring how [instruction]
       flattens it. *)
    | Folded (i, l) -> one depth i || any depth l
    | _ -> false
  in
  any 0 instrs

let push_label ctx ~loop ~targeted label typ =
  let arity = blocktype_arity ctx typ in
  let i = if loop then fst arity else snd arity in
  let label_arities =
    (Option.map (fun (l : Src.name) -> l.Wax_utils.Ast.desc) label, i)
    :: ctx.label_arities
  in
  let label, labels =
    LabelStack.push ~diagnostics:ctx.diagnostics ~targeted ctx.labels label
  in
  ( label,
    { ctx with labels; label_arities; block_params = blocktype_params ctx typ }
  )

(*
let bottom_heap_type ctx (t : Src.heaptype) : Ast.heaptype =
  match t with
  | Any | Eq | I31 | Struct | Array | None_ -> None_
  | Func | NoFunc -> NoFunc
  | Exn | NoExn -> NoExn
  | Extern | NoExtern -> NoExtern
  | Type ty -> (
      match (lookup_type ctx Type ty).typ with
      | Struct _ | Array _ -> None_
      | Func _ -> NoFunc)
*)
(* A labelled immediate argument [name: v] of a memory access. Both the label
   node and its payload are [Contextual]: an immediate's type is fixed by its
   position in the call, not by its printed form. *)
let labelled with_loc name v =
  contextual (with_loc (Ast.Labelled (Ast.no_loc name, contextual v)))

(* Trailing labelled [offset]/[align] arguments of a memory access: [offset]
   only when non-zero, [align] only when it differs from the natural
   alignment. *)
let mem_extra with_loc (memarg : Src.memarg) nat =
  let lit v = with_loc (Ast.Int (Wax_utils.Uint64.to_string v)) in
  let nat = Wax_utils.Uint64.of_int nat in
  (if Wax_utils.Uint64.compare memarg.offset Wax_utils.Uint64.zero <> 0 then
     [ labelled with_loc "offset" (lit memarg.offset) ]
   else [])
  @
  if Wax_utils.Uint64.compare memarg.align nat <> 0 then
    [ labelled with_loc "align" (lit memarg.align) ]
  else []

(* The callee of an indirect call: [tab[index]] narrowed to the call's function
   type, i.e. [tab[index] as &$ft] (named type) or [tab[index] as &fn(..)] (an
   inline type, with no named type to reference). The cast is always emitted;
   [to_wasm] re-fuses the whole pattern back to [call_indirect]. *)
let indirect_callee ctx with_loc tab ((tyidx, sign) : Src.typeuse) index =
  let tabget =
    with_loc (Ast.ArrayGet (with_loc (Ast.Get (idx ctx `Table tab)), index))
  in
  let inline_functype (s : Src.functype) : Ast.casttype =
    let sign : Ast.functype =
      {
        params = functype_params ctx s.params;
        results = Array.map (fun t -> valtype ctx t) s.results;
      }
    in
    Ast.Functype { nullable = true; sign }
  in
  let cast_type : Ast.casttype option =
    match Option.bind tyidx (implicit_functype ctx) with
    | Some ft ->
        (* Anonymous implicit type: no named type to reference, render inline. *)
        Some (inline_functype ft)
    | None -> (
        match tyidx with
        | Some ti ->
            Some
              (Ast.Valtype
                 (Ast.Ref { nullable = true; typ = Ast.Type (idx ctx `Type ti) }))
        | None -> Option.map inline_functype sign)
  in
  match cast_type with
  | Some ct -> with_loc (Ast.Cast (tabget, ct))
  | None -> tabget

(* A bottom descriptor operand carries no descriptor type of its own — a hole
   (dead code, popped from an empty stack) or a [ref.null none]-style null (a cast
   to a bottom heap type) — so the typer cannot recover the target from it. Pin it
   to the descriptor type of the target [x] ([exact] matching the target's
   exactness); a concrete operand keeps its own type. An existing bottom cast's
   target is rewritten in place, so [simplify] cannot fold the pin back to bottom. *)
let pin_descriptor ctx ~exact x d =
  match (lookup_type ctx Type x).descriptor with
  | None -> d
  | Some y -> (
      let y = idx ctx `Type y in
      let pin =
        Ast.Valtype
          (Ast.Ref
             {
               nullable = true;
               typ = (if exact then Ast.Exact y else Ast.Type y);
             })
      in
      let is_bottom (t : Ast.heaptype) =
        match t with
        | None_ | NoFunc | NoExtern | NoExn | NoCont -> true
        | _ -> false
      in
      match d.Ast.desc with
      | Ast.Hole | Ast.Null -> cast_to pin d
      | Ast.Cast (inner, Ast.Valtype (Ast.Ref { typ; _ })) when is_bottom typ ->
          (* Rebuilt on [d] to keep the outer node's span; its expectation is the
             new cast's target, not the replaced cast's operand. *)
          {
            d with
            Ast.desc = Ast.Cast (inner, pin);
            expected = cast_result pin;
          }
      | _ -> d)

(* As [pin_descriptor], taking the target as the [reftype] the branch/cast
   immediate carries (an abstract target has no descriptor — leave the hole). *)
let pin_descriptor_reftype ctx (t : Src.reftype) d =
  match t.typ with
  | Type x -> pin_descriptor ctx ~exact:false x d
  | Exact x -> pin_descriptor ctx ~exact:true x d
  | _ -> d

(*** The instruction converter ***)

(* Only value-producing arithmetic and bitwise operators have a compound-
   assignment form; comparisons do not. *)
let has_compound_form : Ast.binop -> bool = function
  | Add | Sub | Mul | Div _ | Rem _ | And | Or | Xor | Shl | Shr _ -> true
  | Eq | Ne | Lt _ | Gt _ | Le _ | Ge _ -> false

(* Build the assignment [target = e], collapsing [x = x op e] back into the
   compound assignment [x op= e] — the inverse of the lowering in {!To_wasm}.
   The variable must be the operator's left operand. *)
let set_desc target e =
  match e.Ast.desc with
  | Ast.BinOp (op, { desc = Get y; _ }, rhs)
    when has_compound_form op.desc
         && String.equal y.desc target.Wax_utils.Ast.desc ->
      Ast.Set (target, Some op, rhs)
  | _ -> Ast.Set (target, None, e)

(* A decompiled struct-literal field. When the value is a plain [Get] of the
   like-named local/global/function, use the punning shorthand [{x}] ([None])
   rather than the redundant [{x: x}]; re-parsing resolves the pun to that same
   [Get], so the output round-trips. *)
let struct_field nm (v : _ Ast.instr) =
  match v.desc with
  | Ast.Get x when String.equal x.desc nm -> (Ast.no_loc nm, None)
  | _ -> (Ast.no_loc nm, Some v)

(* A diverging instruction leaves the stack polymorphic: everything below it is
   dead and a later pop from the empty region springs from a polymorphic bottom
   (an [Unknown]-typed hole). These are exactly the instructions lowered through
   [Stack.push_poly]. Used by the reference comparisons to tell such a bottom
   from a real dead value producer still on the stack (see [RefEq]/[RefIsNull]). *)
let is_poly_terminator (i : _ Ast.instr) =
  match i.Ast.desc with
  | Ast.Unreachable | Ast.Br _ | Ast.Br_table _ | Ast.TailCall _ | Ast.Return _
  | Ast.Throw _ | Ast.ThrowRef _ ->
      true
  | _ -> false

(* Whether two source signatures convert to the same Wax signature — compared
   on the printed converted types, locations aside (the [collapse_splices]
   trick). Used by [pin_callee]: a captured function value of the SAME
   signature satisfies the callee pin as written (the pin drops as redundant
   and the call reads the value, exactly as the source instruction did).
   Deliberately equality, not subtyping (which this module cannot decide): a
   proper-subtype capture behind an annotation falls back to the claim-free
   bottom pin, which is inert there. *)
let same_signature ctx (a : Src.functype) (b : Src.functype) =
  let print (ft : Src.functype) =
    Wax_utils.Printer.run_string (fun pp ->
        Array.iter
          (fun p ->
            Wax_lang.Output.valtype pp (valtype ctx (snd p.Wax_utils.Ast.desc));
            Wax_utils.Printer.string pp "->")
          ft.Src.params;
        Array.iter
          (fun t ->
            Wax_lang.Output.valtype pp (valtype ctx t);
            Wax_utils.Printer.string pp ",")
          ft.Src.results)
  in
  String.equal (print a) (print b)

(* The [call_ref]/[return_call_ref] callee type pin [(_ as &?t)] for an ABSENT
   callee (a pop off the polymorphic stack). The cast names the instruction's
   type immediate, so it must survive — but its hole claims positionally, and
   behind a conditional annotation (the scan's [crossed]) the captured value
   may be anything the branches consume per configuration: a wrong-hierarchy or
   non-reference capture poisons the cast, and a func capture of a DIFFERENT
   signature materialises the pin as a [ref.cast] the source never had. Ground
   such a hole with the claim-free func-hierarchy bottom INSIDE the type pin —
   [((_ as &?nofunc) as &?t)] claims nothing, still names [t], and lowers to no
   instruction — and keep the plain pin everywhere else: with no annotation in
   between, a captured value is the very callee the source popped (the
   validator typed it there), so the claim is load-bearing and sound. *)
let pin_callee ctx t (f : _ Ast.instr) =
  let target : Ast.valtype =
    Ref { nullable = true; typ = Type (idx ctx `Type t) }
  in
  let pin inner = { f with Ast.desc = Ast.Cast (inner, Valtype target) } in
  match f.Ast.desc with
  | Ast.Hole ->
      let* backing = Stack.effective_backing is_poly_terminator in
      let wrong =
        match backing with
        | `Value -> true
        | `Backing (b, from_top, crossed) -> (
            crossed
            &&
            match backing_class_of ctx ~from_top b with
            | Null_class -> false
            | Value_class -> true
            | Unknown_class -> false
            | Ref_class { hier; _ } -> (
                hier <> `Func
                ||
                match b.Ast.desc with
                | Ast.Get g -> (
                    match
                      ( (try
                           Some
                             (CondTbl.find ctx.function_types ctx.cond_asm
                                g.Ast.desc)
                         with Not_found -> None),
                        typeuse_functype ctx (Some t, None) )
                    with
                    | Some gtu, Some tft -> (
                        match typeuse_functype ctx gtu with
                        | Some gft -> not (same_signature ctx gft tft)
                        | None -> true)
                    | _ -> true)
                | _ -> true))
        | `Floor | `Blocked -> false
      in
      let inner =
        if wrong then
          cast_to (Valtype (Ref { nullable = true; typ = NoFunc })) f
        else f
      in
      return (pin inner)
  | _ -> return (pin f)

(* Whether the residual's own printed form names exactly the type [type_name] —
   the one capture a [(_ as &?type_name)] receiver pin provably absorbs as
   written (the pin drops as redundant and the access reads the value, exactly
   as the source instruction did). *)
let backing_names_type ~from_top (b : _ Ast.instr) (type_name : Ast.ident) =
  from_top = 0
  &&
  match b.Ast.desc with
  | Ast.Cast (_, Valtype (Ref { typ = Type n | Exact n; _ })) ->
      String.equal n.Ast.desc type_name.Ast.desc
  | _ -> false

(* The member-access receiver type pin [(recv as &?t)] (a struct/array read,
   write, fill/copy/init receiver) for an ABSENT receiver, as [pin_callee] for
   a callee: behind a conditional annotation ([crossed]) a positional capture
   the pin cannot absorb — a value outside [t]'s hierarchy, a non-reference, or
   a reference whose printed form names a DIFFERENT type — either poisons the
   access (and the lowering, which reads the struct/array type off the
   receiver, has nothing to emit) or materialises the pin as a [ref.cast] the
   source never had. Ground such a hole with the claim-free bottom of [t]'s
   hierarchy inside the type pin — [((_ as &?none) as &?t)] still names [t] —
   and keep the plain pin everywhere else (with no annotation in between a
   captured value is the receiver the source instruction read, validator-typed
   there). [siblings] are the statement's shallower operands, whose own hole
   claims sit between this receiver's hole and its capture. *)
let pin_receiver ctx type_name ~siblings (recv : _ Ast.instr) =
  let target : Ast.valtype = Ref { nullable = true; typ = Type type_name } in
  let pin inner = { recv with Ast.desc = Ast.Cast (inner, Valtype target) } in
  match recv.Ast.desc with
  | Ast.Hole ->
      let claims =
        List.fold_left (fun n e -> n + Stack.hole_claims e) 0 siblings
      in
      let* backing = Stack.effective_backing ~claims is_poly_terminator in
      let wrong =
        match backing with
        | `Value -> true
        | `Backing (b, from_top, crossed) -> (
            crossed
            && (not (backing_names_type ~from_top b type_name))
            &&
            match backing_class_of ctx ~from_top b with
            | Null_class | Unknown_class -> false
            | Value_class | Ref_class _ -> true)
        | `Floor | `Blocked -> false
      in
      let bottom : Ast.heaptype =
        match heaptype_hierarchy ctx (Type type_name) with
        | Some `Func -> NoFunc
        | Some `Extern -> NoExtern
        | Some `Exn -> NoExn
        | Some `Cont -> NoCont
        | Some `Any | None -> None_
      in
      let inner =
        if wrong then
          cast_to (Valtype (Ref { nullable = true; typ = bottom })) recv
        else recv
      in
      return (pin inner)
  | _ -> return (pin recv)

(* Pin the reference HIERARCHY of an operand that leaves it open: a hole is
   polymorphic, and [!e] ([ref.as_non_null]) only forwards its operand's type. The
   pin is pushed down to the hole ITSELF rather than wrapped around the [!] —
   around it the pin would be a cross-hierarchy cast of an any-typed operand, i.e.
   an [extern.convert_any], the very instruction being avoided, whereas on a bare
   hole it merely types the hole and lowers to nothing. [None] when the operand
   pins a hierarchy of its own (a named value, a construction, an expression
   already cast) and so needs no pin.

   An unannotated [select] of holes is deliberately NOT descended into, unlike in
   [RefIsNull]: an unannotated select's value operands must be numeric (or, in
   dead code, bottom), so one feeding a cast into the extern hierarchy always has
   two bottom arms — the expected type then flows into them and the cast is
   dropped as redundant rather than turning into a convert. That is the
   documented best-effort cast fidelity, and pinning an arm would trade it for a
   typed-[select] immediate, itself a documented residual. *)
let rec pin_hierarchy pin (e : _ Ast.instr) =
  match e.Ast.desc with
  (* A hole, or an untyped [select] of holes: both re-parse type-adaptively (the
     select's result type is its arms'), so both take the target hierarchy under the
     outer cast and absorb it. Same shapes [type_hole_src]/[convert_src] pin. *)
  | Ast.Hole | Ast.Select _ -> Some (cast_to pin e)
  | Ast.NonNull inner ->
      Option.map
        (fun inner -> { e with Ast.desc = Ast.NonNull inner })
        (pin_hierarchy pin inner)
  | _ -> None

(* Branch-hinting / compilation-hints proposals: carry a Wasm instruction's hints
   onto the Wax instruction it decompiles to. A Wasm instruction contributes one
   entry to the stack of Wax expressions being built, so the hints go on whatever
   [instruction_desc] left on top. *)
(* Record a local's / global's NUMERIC type on a node that carries its value —
   the [Get] that reads it, and the value a [set]/[tee] writes to it. A reference
   local records nothing: the channel holds numeric scalars only (and [v128], as a
   not-a-reference marker), which is exactly what its readers ask about. *)
let expect_local ctx (name : (string, _) Ast.annotated) e =
  match Hashtbl.find_opt ctx.local_valtypes name.Ast.desc with
  | Some t -> expect t e
  | None -> e

let expect_global ctx (name : (string, _) Ast.annotated) e =
  match Hashtbl.find_opt ctx.global_valtypes name.Ast.desc with
  | Some t -> expect t e
  | None -> e

let rec instruction ctx (i : _ Src.instr) : unit Stack.t =
  let* () = instruction_desc ctx i in
  if Wax_wasm.Hints.is_empty i.hints then return ()
  else
    let hints = Wax_wasm.Hints.map_targets (fun f -> idx ctx `Func f) i.hints in
    fun stack ->
      match stack with
      | (arity, w, top) :: rem -> ((arity, w, { top with Ast.hints }) :: rem, ())
      | [] -> ([], ())

and instruction_desc ctx (i : _ Src.instr) : unit Stack.t =
  let with_loc (i' : _ Ast.instr_desc) : _ Ast.instr =
    {
      Ast.desc = i';
      info = i.info;
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  (* A block-shaped value node ([do]/[loop]/[if]/[try]): its result type is
     stated by its own annotation, or — when [simplify] drops a redundant one —
     re-imposed by the context that made it redundant, so the node needs no
     claim of its own ([Contextual]; the values INSIDE feeding its exits are
     cleared by [forget_expected] for the same reason). *)
  let block_node (i' : _ Ast.instr_desc) : _ Ast.instr =
    contextual (with_loc i')
  in
  let mem_call m meth args =
    with_loc
      (Ast.Call
         ( with_loc
             (Ast.StructGet
                (with_loc (Ast.Get (idx ctx `Mem m)), Ast.no_loc meth)),
           args ))
  in
  let table_call t meth args =
    with_loc
      (Ast.Call
         ( with_loc
             (Ast.StructGet
                (with_loc (Ast.Get (idx ctx `Table t)), Ast.no_loc meth)),
           args ))
  in
  (* [seg.drop()] on a data or element segment. *)
  let drop_call kind seg =
    with_loc
      (Ast.Call
         ( with_loc
             (Ast.StructGet
                (with_loc (Ast.Get (idx ctx kind seg)), Ast.no_loc "drop")),
           [] ))
  in
  (* [recv.meth(args)] method call and [f(args)] free-function call, used for
     SIMD intrinsics. *)
  let meth_call recv meth args =
    with_loc (Ast.Call (with_loc (Ast.StructGet (recv, Ast.no_loc meth)), args))
  in
  (* [ns::name(args)] qualified-path intrinsic call (SIMD free functions, wide
     arithmetic). *)
  let path_call ns name args =
    with_loc
      (Ast.Call (with_loc (Ast.Path (Ast.no_loc ns, Ast.no_loc name)), args))
  in
  (* Ascribe a (struct/array) method receiver its reference type, so the method
     resolves even when the receiver is a hole on a polymorphic stack (unreachable
     code); a redundant cast on a concrete receiver is dropped by [simplify]. *)
  let cast_ref recv typ =
    {
      recv with
      Ast.desc = Ast.Cast (recv, Valtype (Ref { nullable = true; typ }));
    }
  in
  (* Ascribe the continuation operand — the last of [args] — with the
     instruction's type immediate, [(c as &?ct)], so a resume/switch/bind
     through a supertype signature keeps its exact immediate on the round
     trip. The ascription lowers to no instruction; re-typing drops it again
     when it merely names the operand's own type. *)
  let ascribe_cont ct args =
    match List.rev args with
    | c :: rest -> List.rev (cast_ref c (Type ct) :: rest)
    | [] -> []
  in
  match i.desc with
  | Block { label; typ; block } ->
      let label, ctx =
        push_label ctx ~loop:false
          ~targeted:(label_targeted ?self:(label_name label) block.desc)
          label typ
      in
      let inputs, outputs = blocktype_arity ctx typ in
      let block = Stack.run ~results:outputs (instructions ctx block.desc) in
      let* () = Stack.consume inputs in
      Stack.push
        (if inputs > 0 then 0 else outputs)
        (block_node
           (Block
              {
                label = label ();
                typ = blocktype ctx typ;
                block = Ast.no_loc block;
              }))
  | Loop { label; typ; block } ->
      let label, ctx =
        push_label ctx ~loop:true
          ~targeted:(label_targeted ?self:(label_name label) block.desc)
          label typ
      in
      let inputs, outputs = blocktype_arity ctx typ in
      let block = Stack.run ~results:outputs (instructions ctx block.desc) in
      let* () = Stack.consume inputs in
      Stack.push
        (if inputs > 0 then 0 else outputs)
        (block_node
           (Loop
              {
                label = label ();
                typ = blocktype ctx typ;
                block = Ast.no_loc block;
              }))
  | If { label; typ; if_block; else_block } ->
      let label, ctx =
        let self = label_name label in
        push_label ctx ~loop:false
          ~targeted:
            (label_targeted ?self if_block.desc
            || label_targeted ?self else_block.desc)
          label typ
      in
      let inputs, outputs = blocktype_arity ctx typ in
      (* Keep the (then ...)/(else ...) clause locations on the Wax blocks so a
         comment opening a clause attaches to the block rather than the
         condition or the previous clause's last instruction. *)
      let if_block =
        {
          if_block with
          Ast.desc = Stack.run ~results:outputs (instructions ctx if_block.desc);
        }
      in
      let else_block =
        if else_block.desc = [] then None
        else
          Some
            {
              else_block with
              Ast.desc =
                Stack.run ~results:outputs (instructions ctx else_block.desc);
            }
      in
      let* cond = Stack.pop in
      let* () = Stack.consume inputs in
      Stack.push
        (if inputs > 0 then 0 else outputs)
        (block_node
           (If
              {
                label = label ();
                typ = blocktype ctx typ;
                cond;
                if_block;
                else_block;
              }))
  | TryTable { label = labl; typ; block; catches } ->
      let labl, block_ctx =
        push_label ctx ~loop:false
          ~targeted:(label_targeted ?self:(label_name labl) block.desc)
          labl typ
      in
      let inputs, outputs = blocktype_arity ctx typ in
      let block =
        Stack.run ~results:outputs (instructions block_ctx block.desc)
      in
      let catches =
        List.map
          (fun (catch : Src.catch) : Ast.catch ->
            match catch with
            | Catch (t, l) -> Catch (idx ctx `Tag t, label ctx l)
            | CatchRef (t, l) -> CatchRef (idx ctx `Tag t, label ctx l)
            | CatchAll l -> CatchAll (label ctx l)
            | CatchAllRef l -> CatchAllRef (label ctx l))
          catches
      in
      let* () = Stack.consume inputs in
      Stack.push
        (if inputs > 0 then 0 else outputs)
        (block_node
           (TryTable
              {
                label = labl ();
                typ = blocktype ctx typ;
                block = Ast.no_loc block;
                catches;
              }))
  | Try { label; typ; block; catches; catch_all } ->
      (* A [br] out of the try's body or any of its handler blocks targets the
         one try scope, so all of them bear on whether this label renders. *)
      let targeted =
        let self = label_name label in
        label_targeted ?self block.desc
        || List.exists
             (fun (_, b) -> label_targeted ?self b.Wax_utils.Ast.desc)
             catches
        ||
        match catch_all with
        | Some b -> label_targeted ?self b.Ast.desc
        | None -> false
      in
      let label, ctx = push_label ctx ~loop:false ~targeted label typ in
      let inputs, outputs = blocktype_arity ctx typ in
      let block = Stack.run ~results:outputs (instructions ctx block.desc) in
      let catches =
        List.map
          (fun (t, block) ->
            ( idx ctx `Tag t,
              Ast.no_loc
                (Stack.run ~results:outputs
                   (instructions ctx block.Wax_utils.Ast.desc)) ))
          catches
      in
      let catch_all =
        Option.map
          (fun block ->
            Ast.no_loc
              (Stack.run ~results:outputs
                 (instructions ctx block.Wax_utils.Ast.desc)))
          catch_all
      in
      let* () = Stack.consume inputs in
      Stack.push
        (if inputs > 0 then 0 else outputs)
        (block_node
           (Try
              {
                label = label ();
                typ = blocktype ctx typ;
                block = Ast.no_loc block;
                catches;
                catch_all;
              }))
  | Unreachable -> Stack.push_poly (with_loc Unreachable)
  | Nop -> Stack.push 0 (with_loc Nop)
  | Drop ->
      (* A dropped value supplies no expected type: a width eraser (see [Stack]).
         [i64.div_u (2147483648 + 2147483648)] would re-default its divisor to a
         trapping [0]. The drop is an anonymous [Let] ([_ = e]); a non-default
         flexible width is pinned in its type annotation ([_: i64 = e]) rather
         than by an identity cast on the value, so the reader is never left to
         disambiguate a genuine [as] conversion from a width pin. The keep/drop
         of that annotation then reuses the ordinary [Let] machinery. *)
      let* e, w = Stack.pop_tagged in
      let annot : Ast.valtype option =
        match w with
        | Some `I64 -> Some I64
        | Some `F32 -> Some F32
        | Some `F64 -> Some F64
        | Some `I32 | None -> None
      in
      Stack.push 0 (with_loc (Let ([ (None, annot) ], Some e)))
  | Br i ->
      let input = label_arity ctx i in
      let* args = Stack.grab input in
      Stack.push_poly (with_loc (Br (label ctx i, sequence_opt args)))
  | Br_if i ->
      let input = label_arity ctx i in
      let* args = Stack.grab (input + 1) in
      Stack.push input
        (contextual (with_loc (Br_if (label ctx i, sequence args))))
  | Br_table (labels, lab) ->
      let input = label_arity ctx lab in
      let* args = Stack.grab (input + 1) in
      Stack.push_poly
        (with_loc
           (Br_table
              (List.map (fun i -> label ctx i) (labels @ [ lab ]), sequence args)))
  | Br_on_null i ->
      let input = label_arity ctx i in
      let* args = Stack.grab (input + 1) in
      Stack.push (input + 1)
        (contextual (with_loc (Br_on_null (label ctx i, sequence args))))
  | Br_on_non_null i ->
      let input = label_arity ctx i in
      let* args = Stack.grab input in
      Stack.push (input - 1)
        (contextual (with_loc (Br_on_non_null (label ctx i, sequence args))))
  | Br_on_cast (i, _, t) ->
      let input = label_arity ctx i in
      let* args = Stack.grab input in
      Stack.push input
        (contextual
           (with_loc (Br_on_cast (label ctx i, reftype ctx t, sequence args))))
  | Br_on_cast_fail (i, _, t) ->
      let input = label_arity ctx i in
      let* args = Stack.grab input in
      Stack.push input
        (contextual
           (with_loc
              (Br_on_cast_fail (label ctx i, reftype ctx t, sequence args))))
  | Br_on_cast_desc_eq (i, _, t) ->
      (* The descriptor operand is on top of the branch operands. The target type
         and its exactness are recovered from the descriptor, so only the result
         nullability of [t] is kept. *)
      let input = label_arity ctx i in
      let* d = Stack.pop in
      let d = pin_descriptor_reftype ctx t d in
      let* args = Stack.grab input in
      Stack.push input
        (contextual
           (with_loc
              (Br_on_cast_desc_eq (label ctx i, t.nullable, sequence args, d))))
  | Br_on_cast_desc_eq_fail (i, _, t) ->
      let input = label_arity ctx i in
      let* d = Stack.pop in
      let d = pin_descriptor_reftype ctx t d in
      let* args = Stack.grab input in
      Stack.push input
        (contextual
           (with_loc
              (Br_on_cast_desc_eq_fail
                 (label ctx i, t.nullable, sequence args, d))))
  | Folded (head, l) ->
      (* Carry the folded expression's full span (the [(…)]'s [$sloc]) onto its
         head instruction, so the resulting Wax node encloses its operands rather
         than covering just the opcode keyword. Otherwise a comment trailing the
         [)] attaches to the last-ending operand — which, for [select]'s
         value/condition reorder, is the ternary's *first* element (the
         condition), not its last, breaking the wax→wat→wax round-trip. *)
      let* () = instructions ctx l in
      instruction ctx { head with Src.info = i.Src.info }
  | LocalGet x ->
      (* Record the local's numeric type on the node (see [local_valtypes]). *)
      let name = idx ctx `Local x in
      Stack.push 1 (expect_local ctx name (with_loc (Get name)))
  | GlobalGet x ->
      (* As for [LocalGet]: record the global's numeric type on the node. *)
      let name = idx ctx `Global x in
      Stack.push 1 (expect_global ctx name (with_loc (Get name)))
  | LocalSet x ->
      (* Record the target's numeric type on the assigned VALUE too, not only on a
         [Get]: a hole assigned to a numeric local is a hole the re-parse types
         numerically, which is what [Stack.effective_backing] needs to know to see
         past the statement (see [hole_claims]). *)
      let name = idx ctx `Local x in
      let* e = Stack.pop in
      Stack.push 0 (with_loc (set_desc name (expect_local ctx name e)))
  | GlobalSet x ->
      let name = idx ctx `Global x in
      let* e = Stack.pop in
      Stack.push 0 (with_loc (set_desc name (expect_global ctx name e)))
  | LocalTee x ->
      let name = idx ctx `Local x in
      let* e = Stack.pop in
      (* The tee's own result has the local's type too, so record it on the
         node as well as on the assigned value. *)
      Stack.push 1
        (expect_local ctx name (with_loc (Tee (name, expect_local ctx name e))))
  | BinOp (I32 op) -> int_bin_op i `I32 op
  | BinOp (I64 op) -> int_bin_op i `I64 op
  | BinOp (F32 op) -> float_bin_op i `F32 op
  | BinOp (F64 op) -> float_bin_op i `F64 op
  | Add128 | Sub128 | MulWide _ ->
      (* Wide arithmetic decompiles to the [i64::...] path intrinsics, whose two
         i64 results are consumed by a multi-value [let]. *)
      let name, input =
        match i.desc with
        | Add128 -> ("add128", 4)
        | Sub128 -> ("sub128", 4)
        | MulWide Signed -> ("mul_wide_s", 2)
        | MulWide Unsigned -> ("mul_wide_u", 2)
        | _ -> assert false
      in
      let* args = Stack.grab input in
      (* Both results are i64: record it (the all-numeric multi-value mark the
         backing scan reads — see [functype_value_result]). *)
      Stack.push 2 (expect I64 (path_call "i64" name args))
  | UnOp (I64 op) -> int_un_op ~faithful:ctx.faithful i `I64 op
  | UnOp (I32 op) -> int_un_op ~faithful:ctx.faithful i `I32 op
  | UnOp (F64 op) -> float_un_op i `F64 op
  | UnOp (F32 op) -> float_un_op i `F32 op
  | StructNew i ->
      let type_name = idx ctx `Type i in
      let fields = snd (struct_fields ctx type_name) in
      let* args = Stack.grab (List.length fields) in
      Stack.push 1
        (with_loc
           (Struct (Some (idx ctx `Type i), List.map2 struct_field fields args)))
  | StructNewDefault i ->
      Stack.push 1 (with_loc (StructDefault (Some (idx ctx `Type i))))
  | StructNewDesc i ->
      let type_name = idx ctx `Type i in
      let fields = snd (struct_fields ctx type_name) in
      (* The descriptor operand is on top of the field values. The struct type is
         recovered from the descriptor, so it is not written. *)
      let* d = Stack.pop in
      let d = pin_descriptor ctx ~exact:true i d in
      let* args = Stack.grab (List.length fields) in
      Stack.push 1
        (with_loc (StructDesc (d, List.map2 struct_field fields args)))
  | StructNewDefaultDesc i ->
      let* d = Stack.pop in
      let d = pin_descriptor ctx ~exact:true i d in
      Stack.push 1 (with_loc (StructDefaultDesc d))
  | StructGet (s, t, f) ->
      let type_name = idx ctx `Type t in
      let name = Sequence.get (fst (struct_fields ctx type_name)) f in
      let* arg = Stack.pop in
      let* arg = pin_receiver ctx type_name ~siblings:[] arg in
      let e = with_loc (StructGet (arg, name)) in
      Stack.push 1
        (match s with
        (* A packed field read with a sign ([struct.get_s/u] of an [i8]/[i16])
           yields an i32 whatever the field's width; an unsigned read of a
           non-packed field yields the field's own type. Record either. *)
        | None ->
            expect_value_result (struct_field_value_type ctx type_name name) e
        | Some signage ->
            expect I32
              (with_loc
                 (Cast (e, Signedtype { typ = `I32; signage; strict = false }))))
  | StructSet (t, f) ->
      let type_name = idx ctx `Type t in
      let name = Sequence.get (fst (struct_fields ctx type_name)) f in
      let* e2 = Stack.pop in
      let* e1 = Stack.pop in
      let* e1 = pin_receiver ctx type_name ~siblings:[ e2 ] e1 in
      Stack.push 0 (with_loc (StructSet (e1, name, e2)))
  | ArrayNew t ->
      let* len = Stack.pop in
      let* v = Stack.pop in
      Stack.push 1 (with_loc (Array (Some (idx ctx `Type t), v, len)))
  | ArrayNewDefault t ->
      let* len = Stack.pop in
      Stack.push 1 (with_loc (ArrayDefault (Some (idx ctx `Type t), len)))
  | ArrayNewFixed (t, n) ->
      (* [n] is a u32 immediate and each element becomes an argument node, so a
         faithful decompilation of a huge [n] is inherently that large (the
         operands not on the stack are filled with holes). No validation runs
         on this path, so an adversarial [n] (e.g. 2^31) makes conversion slow /
         memory-hungry. Left unguarded by design: capping [n] would silently
         mis-convert valid dead code that legitimately needs holes, and any real
         module's count is small. Validation itself is O(operands present) --
         see [pop_repeat] in validation.ml. *)
      let* args = Stack.grab (Uint32.to_int n) in
      (* A string only builds an [i8] (raw bytes) or [i16] (UTF-16) array, so
         only those decode back to a string literal; any other element type
         stays an array literal. *)
      let str =
        match (lookup_type ctx Type t).typ with
        | Array { typ = Packed I8; _ } -> string_args n args
        | Array { typ = Packed I16; _ } -> wide_string_args n args
        | _ -> None
      in
      Stack.push 1
        (match str with
        | Some s -> with_loc (String (Some (idx ctx `Type t), s))
        | None -> with_loc (ArrayFixed (Some (idx ctx `Type t), args)))
  | ArrayGet (s, t) ->
      let* e2 = Stack.pop in
      let* e1 = Stack.pop in
      let* e1 = pin_receiver ctx (idx ctx `Type t) ~siblings:[ e2 ] e1 in
      let e = with_loc (ArrayGet (e1, e2)) in
      Stack.push 1
        (match s with
        (* As [StructGet], for the array's element type. *)
        | None ->
            expect_value_result
              (array_element_value_type ctx (idx ctx `Type t))
              e
        | Some signage ->
            expect I32
              (with_loc
                 (Cast (e, Signedtype { typ = `I32; signage; strict = false }))))
  | ArraySet t ->
      let* e3 = Stack.pop in
      let* e2 = Stack.pop in
      let* e1 = Stack.pop in
      let* e1 = pin_receiver ctx (idx ctx `Type t) ~siblings:[ e2; e3 ] e1 in
      Stack.push 0 (with_loc (ArraySet (e1, e2, e3)))
  | Call f ->
      let input, output = function_arity ctx f in
      let* args = Stack.grab input in
      let name = idx ctx `Func f in
      let tu = lookup_type ctx Func f in
      (* A multi-value signature with reference results cannot record its
         composition on the node (the expectation channel is single-valued);
         remember the reference hierarchies under the Wax name instead, for
         the converts' backing test (see [ctx.multi_ref_results]). *)
      (if output >= 2 then
         match typeuse_functype ctx tu with
         | Some { Src.results; _ } ->
             Hashtbl.replace ctx.multi_ref_results name.Ast.desc
               (result_classes ctx results)
         | None -> ());
      Stack.push output
        (expect_value_result
           (typeuse_value_result ctx tu)
           (with_loc (Call (with_loc (Get name), args))))
  | CallRef t ->
      let input, output = type_arity ctx t in
      let result_ty = type_value_result ctx t in
      let* f = Stack.pop in
      let* f = pin_callee ctx t f in
      let* args = Stack.grab input in
      Stack.push output
        (expect_value_result result_ty (with_loc (Call (f, args))))
  | ReturnCall f ->
      let input, _ = function_arity ctx f in
      let* args = Stack.grab input in
      Stack.push_poly
        (with_loc (TailCall (with_loc (Get (idx ctx `Func f)), args)))
  | ReturnCallRef t ->
      let input, _ = type_arity ctx t in
      let* f = Stack.pop in
      let* f = pin_callee ctx t f in
      let* args = Stack.grab input in
      Stack.push_poly (with_loc (TailCall (f, args)))
  | Return ->
      let* args = Stack.grab ctx.return_arity in
      Stack.push_poly (with_loc (Return (sequence_opt args)))
  | Const c ->
      let lit, ty, width =
        match c with
        | I32 n -> (integer i.Src.info n, Ast.I32, `I32)
        | I64 n -> (integer i.Src.info n, Ast.I64, `I64)
        | F32 f -> (float i f, Ast.F32, `F32)
        | F64 f -> (float i f, Ast.F64, `F64)
      in
      (* [push_num] records on the pushed node; under [strict_constants] that is
         the pin cast, so the literal beneath it carries the claim [Contextual]ly
         (the cast ascribes its type). *)
      Stack.push_num (Some width)
        (if ctx.strict_constants then
           with_loc (Cast (contextual lit, Valtype ty))
         else lit)
  | RefI31 ->
      (* Source is i32; a dead-code hole is pinned [(_ as i32)] so [ref.i31]
         survives (a bare [_ as &i31] re-types the hole to a null i31 and drops the
         conversion). *)
      let* e = Stack.pop in
      Stack.push 1
        (with_loc
           (Cast
              ( type_hole_src I32 e,
                Valtype (Ref { nullable = false; typ = I31 }) )))
  | I31Get signage ->
      (* Source is [&?i31]; a dead-code hole is pinned [(_ as &?i31)] so [i31.get]
         survives (a bare [_ as i32_s] re-types the hole to i32 and drops it). *)
      let* e = Stack.pop in
      Stack.push 1
        (expect I32
           (with_loc
              (Cast
                 ( type_hole_src (Ref { nullable = true; typ = I31 }) e,
                   Signedtype { typ = `I32; signage; strict = false } ))))
  | I64ExtendI32 signage ->
      (* Source is i32; a dead-code hole is pinned [(_ as i32)] so the widen
         survives (a bare [_ as i64_s] drops the [extend_i32_s]). *)
      let* e = Stack.pop in
      Stack.push 1
        (expect I64
           (with_loc
              (Cast
                 ( type_hole_src I32 e,
                   Signedtype { typ = `I64; signage; strict = false } ))))
  | I32WrapI64 ->
      (* Width eraser: [i32.wrap_i64 (4096 >>u 40)] is 0, but a bare [4096 >>u 40]
         re-defaults to i32 and the shift count masks to 8, yielding 16 (a LIVE
         miscompilation). Pin the i64 operand; a dead-code hole is pinned
         [(_ as i64)] so [(_ as i64) as i32] re-emits the [wrap] (else it drops). *)
      let* e = Stack.pop in
      Stack.push 1
        (expect I32 (with_loc (Cast (type_hole_src I64 e, Valtype I32))))
  | F64PromoteF32 ->
      (* Width eraser: the f32 source is not carried by [e as f64]; a bare float
         literal re-defaults to f64, dropping the promote (and its f32 rounding).
         A dead-code hole is pinned [(_ as f32)] so the promote survives. *)
      let* e = Stack.pop in
      Stack.push 1
        (expect F64 (with_loc (Cast (type_hole_src F32 e, Valtype F64))))
  | F32DemoteF64 ->
      (* Width eraser: an integer-valued f64 source prints as a bare integer that
         re-defaults to i32, turning the demote into an i32->f32 convert. A
         dead-code hole is pinned [(_ as f64)] so the demote survives. *)
      let* e = Stack.pop in
      Stack.push 1
        (expect F32 (with_loc (Cast (type_hole_src F64 e, Valtype F32))))
  | ExternConvertAny ->
      (* Source is [&?any]; a dead-code hole is pinned [(_ as &?any)] so the
         conversion survives (a bare [_ as &?extern] re-types the hole and drops
         it). A forwarding [br_on_null] residual on top has its tested ref pinned
         to the source too, so a stranded fall-through hole reconnects there.

         EXCEPT when a source-hierarchy residual (or a null) backs the hole:
         the printed hole reconnects to it and the convert's own [as] surface
         lowers over the real value — the pin would land on that reconnected
         value instead and materialise as a [ref.cast] the source never had
         (the backing-scan grid's founding convert cluster). Left bare, the
         result stays NULLABLE: the reconnected value may be a null.

         And over a backing provably OUTSIDE the source hierarchy — reachable
         only through an [(@if)], whose branches consume it per configuration —
         neither works: bare, the hole takes the wrong-hierarchy value and the
         convert collapses into (or compounds with) a crossing the source never
         had; pinned at the source TOP, the pin captures that value and
         materialises the same crossing. The source hierarchy's BOTTOM is the
         claim-free pin that grounds the hole and leaves the residual to the
         branch that consumes it (see [backing_wrong_hierarchy]). *)
      let src : Ast.valtype = Ref { nullable = true; typ = Any } in
      let* () = pin_forwarding_source src in
      let* e = Stack.pop in
      let* backing = Stack.effective_backing is_poly_terminator in
      let backed =
        is_bare_hole e
        &&
        match backing with
        | `Backing (b, from_top, _) -> backing_in_hierarchy ctx `Any ~from_top b
        | `Value | `Floor | `Blocked -> false
      in
      let wrong =
        is_bare_hole e
        &&
        match backing with
        | `Backing (b, from_top, _) ->
            backing_wrong_hierarchy ctx `Any ~from_top b
        | `Value -> true
        | `Floor | `Blocked -> false
      in
      (* A bare hole is pinned NON-NULL and the convert preserves non-nullness, so
         the RESULT is non-null too. State that here rather than leaving it to the
         typer's refinement, which is gated on [simplify] and so does not happen
         under [--faithful] — there the nullable target made the decompiled Wax
         ill-typed against a non-null consumer. *)
      let nullable = backed || not (is_bare_hole e) in
      let operand =
        if backed then e
        else if wrong then
          cast_to (Valtype (Ref { nullable = false; typ = None_ })) e
        else convert_src ~nullable src e
      in
      Stack.push 1
        (with_loc (Cast (operand, Valtype (Ref { nullable; typ = Extern }))))
  | AnyConvertExtern ->
      (* Source is [&?extern]; a dead-code hole is pinned [(_ as &?extern)] so the
         conversion survives — except over an extern-hierarchy backing, and with
         the wrong-hierarchy bottom pin [(_ as &noextern)], exactly as
         [ExternConvertAny] above. A forwarding [br_on_null] residual on top has
         its tested ref pinned to the source. *)
      let src : Ast.valtype = Ref { nullable = true; typ = Extern } in
      let* () = pin_forwarding_source src in
      let* e = Stack.pop in
      let* backing = Stack.effective_backing is_poly_terminator in
      let backed =
        is_bare_hole e
        &&
        match backing with
        | `Backing (b, from_top, _) ->
            backing_in_hierarchy ctx `Extern ~from_top b
        | `Value | `Floor | `Blocked -> false
      in
      let wrong =
        is_bare_hole e
        &&
        match backing with
        | `Backing (b, from_top, _) ->
            backing_wrong_hierarchy ctx `Extern ~from_top b
        | `Value -> true
        | `Floor | `Blocked -> false
      in
      (* As [ExternConvertAny]: a non-null pin gives a non-null result. *)
      let nullable = backed || not (is_bare_hole e) in
      let operand =
        if backed then e
        else if wrong then
          cast_to (Valtype (Ref { nullable = false; typ = NoExtern })) e
        else convert_src ~nullable src e
      in
      Stack.push 1
        (with_loc (Cast (operand, Valtype (Ref { nullable; typ = Any }))))
  | ArrayNewData (t, d) ->
      let* len = Stack.pop in
      let* off = Stack.pop in
      Stack.push 1
        (with_loc
           (ArraySegment (Some (idx ctx `Type t), idx ctx `Data d, off, len)))
  | ArrayNewElem (t, e) ->
      let* len = Stack.pop in
      let* off = Stack.pop in
      Stack.push 1
        (with_loc
           (ArraySegment (Some (idx ctx `Type t), idx ctx `Elem e, off, len)))
  | TableGet t ->
      let* index = Stack.pop in
      Stack.push 1
        (with_loc (ArrayGet (with_loc (Get (idx ctx `Table t)), index)))
  | TableSet t ->
      let* value = Stack.pop in
      let* index = Stack.pop in
      Stack.push 0
        (with_loc (ArraySet (with_loc (Get (idx ctx `Table t)), index, value)))
  (* call_indirect desugars to [(tab[i] as &$functype)(args)] (a call_ref);
     [to_wasm] re-fuses this back to call_indirect. *)
  | CallIndirect (tab, tu) ->
      let input, output = typeuse_arity ctx tu in
      let* index = Stack.pop in
      let* args = Stack.grab input in
      let f = indirect_callee ctx with_loc tab tu index in
      Stack.push output
        (expect_value_result
           (typeuse_value_result ctx tu)
           (with_loc (Call (f, args))))
  | ReturnCallIndirect (tab, tu) ->
      let input, _ = typeuse_arity ctx tu in
      let* index = Stack.pop in
      let* args = Stack.grab input in
      let f = indirect_callee ctx with_loc tab tu index in
      Stack.push_poly (with_loc (TailCall (f, args)))
  | ArrayLen ->
      let* e = Stack.pop in
      let e = cast_ref e Array in
      Stack.push 1
        (expect I32
           (with_loc (Call (with_loc (StructGet (e, Ast.no_loc "length")), []))))
  | RefCast t ->
      let* e = Stack.pop in
      (* A cast into the EXTERN hierarchy shares the Wax [as &extern] surface
         with the cross-hierarchy conversion [extern.convert_any]. An operand that
         fixes no hierarchy of its own — a dead-code hole, or one forwarded
         through [!] ([ref.as_non_null]) — types in the ANY hierarchy on a
         re-parse, so the cast re-lowers to [extern.convert_any]: an
         opcode-family change, not a width drift. Pin such an operand with
         [(_ as &?extern)], the reference analogue of the numeric width pins (and
         of [ref.is_null]'s [(_ as &?any)]). Only this direction needs it: a hole
         cast to the any/func hierarchy already re-lowers to [ref.cast], and a
         real extern operand fixes the hierarchy itself and is left bare. *)
      let target = reftype ctx t in
      let e =
        match target.typ with
        | Extern | NoExtern ->
            Option.value ~default:e
              (pin_hierarchy
                 (Ast.Valtype (Ast.Ref { nullable = true; typ = Extern }))
                 e)
        | _ -> e
      in
      Stack.push 1 (with_loc (Cast (e, Valtype (Ref target))))
  | RefCastDescEq t ->
      (* The descriptor operand is on top of the value. The target type and its
         exactness are recovered from the descriptor, so only [t]'s result
         nullability is kept. *)
      let* d = Stack.pop in
      let d = pin_descriptor_reftype ctx t d in
      let* e = Stack.pop in
      Stack.push 1 (with_loc (CastDesc (e, t.nullable, d)))
  | RefGetDesc t ->
      let type_name = idx ctx `Type t in
      let* arg = Stack.pop in
      (* [ref.get_desc $t] requires its operand to be [<: (ref null (exact? $t))],
         so a concrete operand already carries a descriptor-bearing type and
         [e.descriptor] resolves directly — casting it to [&?$t] would only strip
         its exactness (the result's exactness mirrors the operand's). Cast only
         an operand with no descriptor of its own: a bottom reference (a hole in
         dead code, or a [ref.null none]-style null cast to a bottom heap type)
         or a bare null. *)
      (* A bottom operand fits the *exact* operand type, and [ref.get_desc]'s
         result is then exact (validation takes the most precise), so pin the
         exact descriptor type. Rewrite the target of an existing bottom cast
         ([ref.null none] → [null as &?none]) in place rather than wrapping it —
         a nested [(null as &?none) as &?!t] is folded back to the bottom by
         [simplify], undoing the pin. *)
      let exact_pin =
        Ast.Valtype (Ref { nullable = true; typ = Exact type_name })
      in
      let is_bottom (t : Ast.heaptype) =
        match t with
        | None_ | NoFunc | NoExtern | NoExn | NoCont -> true
        | _ -> false
      in
      let arg =
        match arg.Ast.desc with
        | Ast.Hole | Ast.Null -> cast_to exact_pin arg
        | Ast.Cast (inner, Valtype (Ref { typ; _ })) when is_bottom typ ->
            {
              arg with
              desc = Ast.Cast (inner, exact_pin);
              expected = cast_result exact_pin;
            }
        | _ -> arg
      in
      Stack.push 1 (with_loc (GetDescriptor arg))
  | RefTest t ->
      let* e = Stack.pop in
      Stack.push 1 (expect I32 (with_loc (Test (e, reftype ctx t))))
  | RefEq ->
      (* [ref.eq] shares the Wax [==] surface with the numeric comparisons, but
         the numeric width pin ([(_ as i64)]) is an [as t] cast and cannot spell
         a ref type: with no anchor two bare holes re-parse as the numeric
         [i32.eq] — a family change, not just a width drift. Leave the holes bare
         whenever a real ref value backs the comparison (the typer unifies them
         to it): a present anchor (a ref value, whose printed form carries its
         type), or a value residual [effective_backing] finds below any interposed
         zero-value statements (a ref by validity, so the bare [_ == _] recovers
         [ref.eq]). Only when both operands spring from the polymorphic bottom (a
         terminator sentinel / empty, reached through interposed dead statements)
         pin one hole with a nullable eq-ref cast [(_ as &?eq)]. (A ref pin cannot
         be blindly applied like a numeric one: a numeric [as] is always valid, but
         casting a value the typer already typed in another reference hierarchy to
         [&?eq] is a static error — hence it is only used over the polymorphic
         bottom, where it is a valid convert, never over a value residual, which is
         detected and left bare regardless of its hierarchy.) *)
      let* o2 = Stack.try_pop in
      let* o1 = Stack.try_pop in
      let* backing = Stack.effective_backing is_poly_terminator in
      let bare = bare_hole () in
      let eq_pin e =
        Ast.no_loc_instr
          (Ast.Cast (e, Valtype (Ref { nullable = true; typ = Eq })))
      in
      (* An UNANNOTATED [select] operand is pinned, exactly as [RefIsNull] pins the
         same shape: only a numeric select is unannotated, so in dead code it is a
         polymorphic select of holes that re-parses to the numeric form — and then
         [==] on it is an [i32.eq], an opcode-family change. It backs no concrete
         reference either, so it does not count towards [backed]. *)
      let is_select o =
        match o with Some { Ast.desc = Ast.Select _; _ } -> true | _ -> false
      in
      let backs o = Option.is_some o && not (is_select o) in
      let backed =
        backs o1 || backs o2
        ||
        match backing with
        | `Backing _ -> true
        | `Value | `Floor | `Blocked -> false
      in
      (* A backing that provably re-types as something OTHER than an
         [eq]-subtype — an extern/func-hierarchy reference or a non-reference
         multi-value residual, reachable only through an [(@if)] whose branches
         consume it per configuration: a bare hole would capture it and the
         [==] would not type-check (or re-default numeric). Ground each hole
         with the claim-free bottom [(_ as &?none)] instead, leaving the value
         to the branch that consumes it (see [backing_not_eq]). *)
      let wrong =
        match backing with
        | `Backing (b, from_top, _) -> backing_not_eq ctx ~from_top b
        | `Value -> true
        | `Floor | `Blocked -> false
      in
      let bottom_pin e =
        Ast.no_loc_instr
          (Ast.Cast (e, Valtype (Ref { nullable = true; typ = None_ })))
      in
      let e1 =
        match o1 with
        | Some ({ Ast.desc = Ast.Select _; _ } as e) -> eq_pin e
        | Some e -> e
        | None ->
            if wrong then bottom_pin bare
            else if backed then bare
            else eq_pin bare
      in
      let e2 =
        match o2 with
        | Some ({ Ast.desc = Ast.Select _; _ } as e) -> eq_pin e
        | Some e -> e
        | None -> if wrong then bottom_pin (bare_hole ()) else bare
      in
      Stack.push 1
        (expect I32 (with_loc (BinOp (op_loc i.info Ast.Eq, e1, e2))))
  | RefFunc f -> Stack.push 1 (with_loc (Get (idx ctx `Func f)))
  | RefNull typ ->
      Stack.push 1
        (with_loc
           (Cast
              ( with_loc Null,
                Valtype (Ref { nullable = true; typ = heaptype ctx typ }) )))
  | RefIsNull ->
      (* [ref.is_null] lowers to the Wax [!e] surface, which it shares with
         [i32.eqz]; with no ref backing it a bare hole re-parses as [i32.eqz] (a
         family change). Leave the hole bare whenever a real ref backs it (a
         present anchor, or a value residual [effective_backing] finds below any
         interposed zero-value statements — a ref by validity, so the typer types
         [!_] to [ref.is_null]). Pin with a nullable any-ref cast [(_ as &?any)]
         when the hole springs from the polymorphic bottom instead: a terminator
         sentinel or empty stack, INCLUDING one reached through interposed dead
         statements (a [br_if] whose condition consumed the value just above, so
         its own arity-0 entry no longer backs anything — the shape [effective_
         backing] skips to reach the sentinel). [ref.is_null] carries no immediate,
         so any nullable ref top recovers it and [&?any] is canonical.

         A present operand that is an UNANNOTATED [select] is pinned too: only a
         numeric [select] is unannotated, so in dead code it is a polymorphic
         [select] of holes that re-parses to the numeric [i32] select unless
         pinned; it backs no concrete ref. (Every pin is kept only when
         load-bearing: [simplify]/[--faithful] drop it for a concrete ref operand,
         where [ty' <: &?any] holds, and keep it otherwise.) *)
      let* o = Stack.try_pop in
      let* backing = Stack.effective_backing is_poly_terminator in
      let any_pin e =
        Ast.no_loc_instr
          (Ast.Cast (e, Valtype (Ref { nullable = true; typ = Any })))
      in
      (* The claim-free bottom pin, for a hole whose positional capture would
         be a provable NON-reference (see [backing_not_ref] and the scan's
         [`Value] verdict): [(_ as &?none)] grounds the hole without taking a
         pending value, so the numeric residual stays for the [(@if)] branch
         that consumes it. *)
      let ref_bottom_pin () =
        Ast.no_loc_instr
          (Ast.Cast
             (bare_hole (), Valtype (Ref { nullable = true; typ = None_ })))
      in
      (* The innermost enclosing block's own parameters are its first stack
         values, so a REFERENCE among them backs this hole exactly as a value
         residual does: the hole reconnects to the parameter on re-parse and takes
         its type, and pinning [&?any] over it would cross hierarchies instead —
         an [(&?noextern)] block parameter had the pin materialise an
         [any.convert_extern] (a wasm-smith finding). Leave it bare and let the
         parameter type it — but ONLY when the scan reached the block floor
         cleanly ([`Floor]): past a terminator ([`Blocked]) the printed hole is
         bottom-sprung and reconnects to nothing, so the parameter cannot type it
         and the bare [!_] would re-default to [i32.eqz] (a ref-width grid
         finding: [do (&?extern) { unreachable; !_ }]). *)
      let backed_by_block_param =
        match ctx.block_params with
        | [||] -> false
        | params -> (
            match params.(Array.length params - 1) with
            | Src.Ref _ -> true
            | _ -> false)
      in
      (* A backing that provably re-types as a NON-reference (a multi-value
         residual whose last result is numeric — reachable as a hole's backing
         only through an [(@if)] whose branches consume it per configuration):
         a bare [!_] capturing it re-defaults to [i32.eqz], and the [(_ as
         &?any)] pin capturing it does not type-check. Ground the hole with the
         claim-free bottom [(_ as &?none)] instead (see [backing_not_ref]). *)
      let e =
        match o with
        | Some ({ Ast.desc = Ast.Select _; _ } as e) -> any_pin e
        | Some e -> e
        | None -> (
            match backing with
            | `Value -> ref_bottom_pin ()
            | `Backing (b, from_top, _) when backing_not_ref ctx ~from_top b ->
                ref_bottom_pin ()
            | `Backing _ -> bare_hole ()
            | `Floor when backed_by_block_param -> bare_hole ()
            | `Floor | `Blocked -> any_pin (bare_hole ()))
      in
      Stack.push 1 (expect I32 (with_loc (UnOp (op_loc i.info Ast.Not, e))))
  | Select tys -> (
      (* The Wax [?:] carries no result type, so resolve the annotation (if any)
         both to catch an out-of-range type reference and to recover the single
         result type: a typed [select (result t)] with [t] one of [i64]/[f32]/[f64]
         or a REFERENCE type must survive re-parse, but with no type on the [?:] an
         anchor-free numeric arm re-defaults to i32 and an anchor-free reference
         arm re-defaults to the numeric [i32] select — dropping the ref type, which
         a downstream [ref.is_null] then reads as [i32.eqz] (an opcode-family
         change). ([i32] itself is the re-parse default and needs no pin; an
         untyped select is genuinely typeless.) A ref pin is only safe with no
         anchored operand (guarded below by [not any_anchor]): casting an operand
         the typer already placed in another hierarchy to [t] would be a static
         error, but a bare hole is polymorphic. *)
      let sel_ty =
        match tys with
        | Some [ t ] -> ( match valtype ctx t with I32 -> None | t -> Some t)
        | Some ts ->
            List.iter (fun t -> ignore (valtype ctx t : Ast.valtype)) ts;
            None
        | None -> None
      in
      let* cond = Stack.pop in
      let* o2 = Stack.try_pop_tagged in
      let* o1 = Stack.try_pop_tagged in
      let is_hole = function None -> true | _ -> false in
      let any_anchor = is_anchor o1 || is_anchor o2 in
      match sel_ty with
      | Some t when not any_anchor ->
          (* Pin exactly one arm to the select's type: a hole if there is one
             (cast on the hole), else result-cast the first flexible arm. That
             grounds the whole select, so it takes no tag. Kept for the REFERENCE
             case, which the width reconciliation does not cover (numeric scalars
             only) and where a bare [?:] would lose the hierarchy; the numeric
             widths ride along on the same path. *)
          let pin1_hole = is_hole o1 in
          let pin2_hole = is_hole o2 && not pin1_hole in
          let pin1_flex = (not pin1_hole) && not pin2_hole in
          let pinned = typed_hole t in
          let cast e = cast_to (Valtype t) e in
          let e1 =
            match o1 with
            | Some (e, _) -> if pin1_flex then cast e else e
            | None -> if pin1_hole then pinned else bare_hole ()
          in
          let e2 =
            match o2 with
            | Some (e, _) -> e
            | None -> if pin2_hole then pinned else bare_hole ()
          in
          Stack.push_num None (expect t (with_loc (Select (cond, e1, e2))))
      | _ ->
          (* Untyped/i32/reference select, or a typed select an arm anchors: the
             result width is that of the arms (both share the select's type),
             flexible only when BOTH arms are flexible literal trees; if either is
             grounded it fixes the width and re-parse resolves the other to it (as
             in [int_bin_op]'s [symbol]). Carrying the combined tag lets a
             downstream eraser ([i32.wrap_i64]) pin the arms so a flexible i64
             select doesn't re-default to i32.

             When only ONE arm is present (a dead-code hole in the other), the hole
             cannot anchor the present arm's width, and the untyped select carries
             no result type to pin it either, so a present arm with a non-default
             width tag ([f32.const], a small [i64.const]) is pinned directly
             ([_ ? (0x0 as f32) : _]) — otherwise the bare literal re-defaults
             (f32 -> f64, i64 -> i32) on re-parse. *)
          let hole = bare_hole () in
          let e1, e2, width =
            match (o1, o2) with
            | Some (a, wa), Some (b, wb) ->
                let width =
                  match (wa, wb) with Some _, Some _ -> wa | _ -> None
                in
                (a, b, width)
            | Some (a, _), None -> (a, hole, None)
            | None, Some (b, _) -> (hole, b, None)
            | None, None -> (hole, hole, None)
          in
          (* With no width tag ([None]) the untyped select is deliberately
             ADAPTIVE — its arms are — so it is [Contextual], not a gap; a
             tagged one gets the tag recorded by [push_num] itself. *)
          Stack.push_num width (contextual (with_loc (Select (cond, e1, e2)))))
  | Throw t ->
      let input, _ = tag_arity ctx t in
      let* args = Stack.grab input in
      Stack.push_poly (with_loc (Throw (idx ctx `Tag t, args)))
  | ThrowRef ->
      let* e = Stack.pop in
      Stack.push_poly (with_loc (ThrowRef e))
  | ContNew ct ->
      let* f = Stack.pop in
      Stack.push 1 (with_loc (ContNew (idx ctx `Type ct, f)))
  | ContBind (src, dst) ->
      let sp, _ = cont_arity ctx src in
      let dp, _ = cont_arity ctx dst in
      let* args = Stack.grab (sp - dp + 1) in
      let src = idx ctx `Type src in
      Stack.push 1
        (with_loc (ContBind (src, idx ctx `Type dst, ascribe_cont src args)))
  (* The stack-switching results ([suspend]/[resume]/[switch]) are [Contextual]:
     their types come from the DECLARED tag/continuation signature the printed
     form still names (the tag or the [ct] immediate), so a re-parse re-derives
     them from the declarations — these arms only know the result arity, not the
     types, and need no claim of their own. *)
  | Suspend t ->
      let input, output = tag_arity ctx t in
      let* args = Stack.grab input in
      Stack.push output (contextual (with_loc (Suspend (idx ctx `Tag t, args))))
  | Resume (ct, handlers) ->
      let input, output = cont_arity ctx ct in
      let* args = Stack.grab (input + 1) in
      let ct = idx ctx `Type ct in
      Stack.push output
        (contextual
           (with_loc
              (Resume
                 (ct, List.map (on_clause ctx) handlers, ascribe_cont ct args))))
  | ResumeThrow (ct, tag, handlers) ->
      let tinput, _ = tag_arity ctx tag in
      let _, output = cont_arity ctx ct in
      let* args = Stack.grab (tinput + 1) in
      let ct = idx ctx `Type ct in
      Stack.push output
        (contextual
           (with_loc
              (ResumeThrow
                 ( ct,
                   idx ctx `Tag tag,
                   List.map (on_clause ctx) handlers,
                   ascribe_cont ct args ))))
  | ResumeThrowRef (ct, handlers) ->
      let _, output = cont_arity ctx ct in
      let* args = Stack.grab 2 in
      let ct = idx ctx `Type ct in
      Stack.push output
        (contextual
           (with_loc
              (ResumeThrowRef
                 (ct, List.map (on_clause ctx) handlers, ascribe_cont ct args))))
  | Switch (ct, tag) ->
      let input, _ = cont_arity ctx ct in
      let output = switch_output ctx ct in
      let* args = Stack.grab input in
      let ct = idx ctx `Type ct in
      Stack.push output
        (contextual
           (with_loc (Switch (ct, idx ctx `Tag tag, ascribe_cont ct args))))
  | RefAsNonNull ->
      let* e = Stack.pop in
      Stack.push 1 (with_loc (NonNull e))
  | ArrayFill t ->
      let* n = Stack.pop in
      let* v = Stack.pop in
      let* i = Stack.pop in
      let* a = Stack.pop in
      let* a = pin_receiver ctx (idx ctx `Type t) ~siblings:[ i; v; n ] a in
      Stack.push 0
        (with_loc
           (Call (with_loc (StructGet (a, Ast.no_loc "fill")), [ i; v; n ])))
  | ArrayCopy (t1, t2) ->
      let* n = Stack.pop in
      let* i2 = Stack.pop in
      let* a2 = Stack.pop in
      let* i1 = Stack.pop in
      let* a1 = Stack.pop in
      let* a2 = pin_receiver ctx (idx ctx `Type t2) ~siblings:[ i2; n ] a2 in
      let* a1 =
        pin_receiver ctx (idx ctx `Type t1) ~siblings:[ i1; a2; i2; n ] a1
      in
      Stack.push 0
        (with_loc
           (Call
              (with_loc (StructGet (a1, Ast.no_loc "copy")), [ i1; a2; i2; n ])))
  | Load (m, memarg, nt) ->
      let* addr = Stack.pop in
      let meth, nat =
        match nt with
        | NumI32 -> ("load32", 4)
        | NumI64 -> ("load64", 8)
        | NumF32 -> ("loadf32", 4)
        | NumF64 -> ("loadf64", 8)
      in
      (* Record the type the method name states ([m.load64] is an i64), so a dead
         load residual is recognised as numeric by [Stack.effective_backing] rather
         than mistaken for a reference backing. *)
      Stack.push 1
        (expect
           (match nt with
           | NumI32 -> I32
           | NumI64 -> I64
           | NumF32 -> F32
           | NumF64 -> F64)
           (mem_call m meth (addr :: mem_extra with_loc memarg nat)))
  | LoadS (m, memarg, result_ty, size, signage) ->
      let* addr = Stack.pop in
      let meth, nat =
        match size with
        | `I8 -> ("load8", 1)
        | `I16 -> ("load16", 2)
        | `I32 -> ("load32", 4)
      in
      let call = mem_call m meth (addr :: mem_extra with_loc memarg nat) in
      (* The operand is [Contextual]: in the fused spelling ([m.load8(x) as
         i64_s] = [i64.load8_s]) the cast is part of the load's own surface —
         the record for the whole sits on the cast node below. *)
      let cast typ e =
        with_loc
          (Ast.Cast (contextual e, Signedtype { typ; signage; strict = false }))
      in
      let result =
        match (size, result_ty) with
        | _, `I32 -> cast `I32 call
        (* A genuinely fused i64 narrow load ([i64.load8_s]) is a single cast
           [m.load8(x) as i64_s], which [to_wasm]'s single-cast arm re-fuses to
           the same instruction. Only a *pair* ([i32.load8_s ; i64.extend_i32_s])
           decompiles as the two casts [(m.load8(x) as i32_s) as i64_s], which
           re-lowers to that honest pair (the two spellings are distinct now that
           [to_wasm] no longer fuses the double cast); so both round-trip
           opcode-for-opcode under [--faithful], and the default path coalesces
           the pair's two casts to the single-cast spelling via [simplify]. *)
        | (`I8 | `I16 | `I32), `I64 -> cast `I64 call
      in
      (* As for the plain load: the cast states the result type, so record it. *)
      Stack.push 1
        (expect (match result_ty with `I32 -> I32 | `I64 -> I64) result)
  | Store (m, memarg, nt) ->
      let* value = Stack.pop in
      let* addr = Stack.pop in
      let meth, nat =
        match nt with
        | NumI32 -> ("store32", 4)
        | NumI64 -> ("store64", 8)
        | NumF32 -> ("storef32", 4)
        | NumF64 -> ("storef64", 8)
      in
      Stack.push 0
        (mem_call m meth (addr :: value :: mem_extra with_loc memarg nat))
  | StoreS (m, memarg, result_ty, size) ->
      let* value = Stack.pop in
      let* addr = Stack.pop in
      (* A narrow store ([store8/16/32]) picks its i32/i64 type from the value
         operand's type ([To_wasm]), which is the one place a Wax surface names no
         type for its operand at all — [m.store16] is both the i32 and the i64
         form. Record the store's own type on the value, and the typer states it in
         the printed form wherever the value would not carry it: a width-flexible
         expression that would re-default to i32, or (the [Unknown]-cell case) a
         hole on the polymorphic dead-code stack, which the lowering reads as i32.
         See {!Wax_lang.Typing.f}'s [~width_check]. *)
      let value =
        Stack.expect_width
          (Some (result_ty :> [ `I32 | `I64 | `F32 | `F64 ]))
          value
      in
      let meth, nat =
        match size with
        | `I8 -> ("store8", 1)
        | `I16 -> ("store16", 2)
        | `I32 -> ("store32", 4)
      in
      Stack.push 0
        (mem_call m meth (addr :: value :: mem_extra with_loc memarg nat))
  | Atomic (m, op, memarg) -> (
      let operands, results = Atomics.signature op in
      let* ops = Stack.grab (List.length operands) in
      let* addr = Stack.pop in
      let nat = 1 lsl Atomics.natural_align_log2 op in
      (* A narrow store/RMW ([store8/16/32], [rmw*8/16/32]) picks its i32/i64 type
         from the value operand's type on re-parse ([To_wasm.atomic_op]): its method
         name carries only the access width, which is ambiguous ([atomic_store16] is
         both [i32.atomic.store16] and [i64.atomic.store16]). A width-flexible i64
         value operand (an [i64.const], a hole on the dead-code stack) re-defaults
         to i32 and narrows the op, so pin it to its signature type, exactly as the
         plain narrow store [StoreS] above (a redundant i32/already-i64 pin is
         dropped by [simplify]; [to_wasm] re-fuses). The full-width forms
         ([store64]/[rmw.…]/[store]) carry an unambiguous name and need no pin. *)
      let narrow =
        match op with
        | AtomicStore (_, Some _) | AtomicRmw (_, _, Some _) -> true
        | _ -> false
      in
      let ops =
        if narrow then
          List.map2
            (fun e t ->
              Stack.expect_width (Some (t :> [ `I32 | `I64 | `F32 | `F64 ])) e)
            ops operands
        else ops
      in
      let call =
        mem_call m
          (Atomics.method_name (Atomics.family op))
          ((addr :: ops) @ mem_extra with_loc memarg nat)
      in
      (* The method name carries the access width only; a narrow load resolves
         its i32/i64 type with a trailing [as iN_u] cast, following the plain
         narrow-load decompile above: a fused i64 form ([i64.atomic.load8_u]) is
         the single cast [m.atomic_load8(x) as i64_u] (re-fused by [to_wasm]),
         only a genuine pair ([i32.atomic.load8_u ; i64.extend_i32_u]) is two
         casts. Stores and RMWs re-resolve from their value operand's type. *)
      let result =
        match op with
        | AtomicLoad (t, Some w) -> (
            (* As for [LoadS]: in the fused spelling the cast is part of the
               load's surface, so the operand is [Contextual] — the record for
               the whole lands on the cast node ([push_num] below). *)
            let cast typ e =
              with_loc
                (Ast.Cast
                   ( contextual e,
                     Signedtype { typ; signage = Unsigned; strict = false } ))
            in
            match (w, t) with
            | _, `I32 -> cast `I32 call
            | (`I8 | `I16 | `I32), `I64 -> cast `I64 call)
        | _ -> call
      in
      (* An atomic load / RMW / notify / wait produces a single numeric ([i32]/
         [i64]) result; tag it with that width (like every arithmetic result) so a
         downstream width eraser pins it, and so a dead leftover of it is recognised
         as numeric — a value a [ref.is_null]/[ref.eq] can never take, hence not a
         backing (see [effective_backing]). A store has no result. *)
      match results with
      | [ t ] ->
          Stack.push_num (Some (t :> [ `I32 | `I64 | `F32 | `F64 ])) result
      | _ -> Stack.push (List.length results) result)
  | AtomicFence -> Stack.push 0 (path_call "atomic" "fence" [])
  | Char c -> Stack.push 1 (expect I32 (with_loc (Char c)))
  | String (t, s) ->
      let s = Wax_utils.Ast.concat_desc s in
      Stack.push 1 (with_loc (String (Option.map (idx ctx `Type) t, s)))
  | If_annotation { cond; then_body; else_body } ->
      let then_body =
        {
          then_body with
          Ast.desc =
            with_cond ctx ~location:i.info cond true (fun () ->
                Stack.run (instructions ctx then_body.desc));
        }
      in
      let else_body =
        Option.map
          (fun (b : (_ Src.instr list, Ast.location) Ast.Annot.annotated) ->
            {
              b with
              Ast.desc =
                with_cond ctx ~location:i.info cond false (fun () ->
                    Stack.run (instructions ctx b.desc));
            })
          else_body
      in
      Stack.push 0 (with_loc (If_annotation { cond; then_body; else_body }))
  (* [size]/[grow] return the memory's ADDRESS type (i64 under memory64); record
     it (see [ctx.address_types]). *)
  | MemorySize m ->
      Stack.push 1
        (expect_address_type ctx (idx ctx `Mem m) (mem_call m "size" []))
  | MemoryGrow m ->
      let* d = Stack.pop in
      Stack.push 1
        (expect_address_type ctx (idx ctx `Mem m) (mem_call m "grow" [ d ]))
  | MemoryFill m ->
      let* n = Stack.pop in
      let* v = Stack.pop in
      let* d = Stack.pop in
      Stack.push 0 (mem_call m "fill" [ d; v; n ])
  | MemoryCopy (m, m') ->
      let* n = Stack.pop in
      let* s = Stack.pop in
      let* d = Stack.pop in
      (* A copy between two different memories names the source explicitly. *)
      let args =
        if (idx ctx `Mem m).desc = (idx ctx `Mem m').desc then [ d; s; n ]
        else with_loc (Ast.Get (idx ctx `Mem m')) :: [ d; s; n ]
      in
      Stack.push 0 (mem_call m "copy" args)
  | MemoryInit (m, data) ->
      let* n = Stack.pop in
      let* s = Stack.pop in
      let* d = Stack.pop in
      let seg = with_loc (Ast.Get (idx ctx `Data data)) in
      Stack.push 0 (mem_call m "init" [ seg; d; s; n ])
  | DataDrop data -> Stack.push 0 (drop_call `Data data)
  (* As for a memory: a table's [size]/[grow] return its address type. *)
  | TableSize t ->
      Stack.push 1
        (expect_address_type ctx (idx ctx `Table t) (table_call t "size" []))
  | TableGrow t ->
      let* n = Stack.pop in
      let* v = Stack.pop in
      Stack.push 1
        (expect_address_type ctx (idx ctx `Table t)
           (table_call t "grow" [ v; n ]))
  | TableFill t ->
      let* n = Stack.pop in
      let* v = Stack.pop in
      let* d = Stack.pop in
      Stack.push 0 (table_call t "fill" [ d; v; n ])
  | TableCopy (t, t') ->
      let* n = Stack.pop in
      let* s = Stack.pop in
      let* d = Stack.pop in
      let args =
        if (idx ctx `Table t).desc = (idx ctx `Table t').desc then [ d; s; n ]
        else with_loc (Ast.Get (idx ctx `Table t')) :: [ d; s; n ]
      in
      Stack.push 0 (table_call t "copy" args)
  | TableInit (t, elem) ->
      let* n = Stack.pop in
      let* s = Stack.pop in
      let* d = Stack.pop in
      let seg = with_loc (Ast.Get (idx ctx `Elem elem)) in
      Stack.push 0 (table_call t "init" [ seg; d; s; n ])
  | ElemDrop elem -> Stack.push 0 (drop_call `Elem elem)
  | ArrayInitData (t, data) ->
      let* n = Stack.pop in
      let* s = Stack.pop in
      let* d = Stack.pop in
      let* a = Stack.pop in
      let* a = pin_receiver ctx (idx ctx `Type t) ~siblings:[ d; s; n ] a in
      let seg = with_loc (Ast.Get (idx ctx `Data data)) in
      Stack.push 0
        (with_loc
           (Call (with_loc (StructGet (a, Ast.no_loc "init")), [ seg; d; s; n ])))
  | ArrayInitElem (t, elem) ->
      let* n = Stack.pop in
      let* s = Stack.pop in
      let* d = Stack.pop in
      let* a = Stack.pop in
      let* a = pin_receiver ctx (idx ctx `Type t) ~siblings:[ d; s; n ] a in
      let seg = with_loc (Ast.Get (idx ctx `Elem elem)) in
      Stack.push 0
        (with_loc
           (Call (with_loc (StructGet (a, Ast.no_loc "init")), [ seg; d; s; n ])))
  (* Every SIMD result is recorded, so a dead residual of one is known not to be a
     reference (see {!recorded_expectation}): a vector op produces [v128], the
     tests and bitmasks an [i32], and a lane extraction its shape's scalar. *)
  | VecUnOp op ->
      let* v = Stack.pop in
      Stack.push 1 (expect V128 (meth_call v (Simd.unop_name op) []))
  | VecBinOp op ->
      let* e2 = Stack.pop in
      let* e1 = Stack.pop in
      Stack.push 1 (expect V128 (meth_call e1 (Simd.binop_name op) [ e2 ]))
  | VecTernOp op ->
      let* e3 = Stack.pop in
      let* e2 = Stack.pop in
      let* e1 = Stack.pop in
      Stack.push 1 (expect V128 (meth_call e1 (Simd.ternop_name op) [ e2; e3 ]))
  | VecShift op ->
      let* count = Stack.pop in
      let* v = Stack.pop in
      Stack.push 1 (expect V128 (meth_call v (Simd.shift_name op) [ count ]))
  | VecTest op ->
      let* v = Stack.pop in
      (* [any_true]/[all_true] yield an i32. *)
      Stack.push 1 (expect I32 (meth_call v (Simd.test_name op) []))
  | VecBitmask op ->
      let* v = Stack.pop in
      Stack.push 1 (expect I32 (meth_call v (Simd.bitmask_name op) []))
  | VecSplat s ->
      let* x = Stack.pop in
      Stack.push 1 (expect V128 (meth_call x (Simd.splat_name s) []))
  | VecBitselect ->
      let* e3 = Stack.pop in
      let* e2 = Stack.pop in
      let* e1 = Stack.pop in
      Stack.push 1
        (expect V128
           (path_call Simd.free_namespace
              (Simd.free_member Simd.bitselect_name)
              [ e1; e2; e3 ]))
  | VecExtract (s, sign, lane) ->
      let* v = Stack.pop in
      Stack.push 1
        (expect (lane_valtype s)
           (meth_call v (Simd.extract_name s sign)
              [ contextual (integer i.Src.info (Int.to_string lane)) ]))
  | VecReplace (s, lane) ->
      let* value = Stack.pop in
      let* v = Stack.pop in
      Stack.push 1
        (expect V128
           (meth_call v (Simd.replace_name s)
              [ contextual (integer i.Src.info (Int.to_string lane)); value ]))
  | VecShuffle lanes ->
      let* e2 = Stack.pop in
      let* e1 = Stack.pop in
      let imms =
        List.init 16 (fun k ->
            contextual
              (integer i.Src.info (Int.to_string (Char.code lanes.[k]))))
      in
      Stack.push 1
        (expect V128 (meth_call e1 Simd.shuffle_name (imms @ [ e2 ])))
  | VecConst v ->
      let lit =
        match v.Wax_utils.V128.shape with
        | F32x4 | F64x2 -> float i
        | I8x16 | I16x8 | I32x4 | I64x2 -> integer i.Src.info
      in
      Stack.push 1
        (expect V128
           (path_call Simd.free_namespace
              (Simd.free_member (Simd.const_name v.shape))
              (List.map (fun c -> contextual (lit c)) v.components)))
  | VecLoad (m, op, memarg) ->
      let* addr = Stack.pop in
      let nat = Simd.vec_load_nat_align op in
      (* The loads were the gap in "every SIMD result is recorded" (found by the
         first [--debug width-record] census run): a dead residual of one read as
         a reference backing in {!Stack.effective_backing}, exactly the class the
         [v128] record exists for. *)
      Stack.push 1
        (expect V128
           (mem_call m (Simd.vec_load_name op)
              (addr :: mem_extra with_loc memarg nat)))
  | VecStore (m, memarg) ->
      let* value = Stack.pop in
      let* addr = Stack.pop in
      Stack.push 0
        (mem_call m Simd.store_name
           (addr :: value :: mem_extra with_loc memarg 16))
  | VecLoadSplat (m, w, memarg) ->
      let* addr = Stack.pop in
      let nat = Simd.lane_nat_align w in
      Stack.push 1
        (expect V128
           (mem_call m (Simd.load_splat_name w)
              (addr :: mem_extra with_loc memarg nat)))
  | VecLoadLane (m, w, memarg, lane) ->
      let* v = Stack.pop in
      let* addr = Stack.pop in
      let nat = Simd.lane_nat_align w in
      Stack.push 1
        (expect V128
           (mem_call m (Simd.load_lane_name w)
              (addr :: v
              :: labelled with_loc "lane"
                   (integer i.Src.info (Int.to_string lane))
              :: mem_extra with_loc memarg nat)))
  | VecStoreLane (m, w, memarg, lane) ->
      let* v = Stack.pop in
      let* addr = Stack.pop in
      let nat = Simd.lane_nat_align w in
      Stack.push 0
        (mem_call m (Simd.store_lane_name w)
           (addr :: v
           :: labelled with_loc "lane" (integer i.Src.info (Int.to_string lane))
           :: mem_extra with_loc memarg nat))

and instructions ctx l =
  match l with
  | [] -> return ()
  | i :: rem ->
      let* () = instruction ctx i in
      instructions ctx rem

(*** Module-field conversion ***)

let bind_locals st l =
  List.map
    (fun e ->
      let _, t = e.Wax_utils.Ast.desc in
      let name = Sequence.get_current st.locals in
      let t = valtype st t in
      Hashtbl.replace st.local_valtypes name.Ast.desc t;
      Ast.no_loc_instr (Ast.Let ([ (Some name, Some t) ], None)))
    l

let typeuse ctx ((typ, sign) : Src.typeuse) =
  let signature ({ params; results } : Src.functype) : Ast.functype =
    {
      params = functype_params ctx params;
      results = Array.map (fun t -> valtype ctx t) results;
    }
  in
  match Option.bind typ (implicit_functype ctx) with
  | Some ft ->
      (* The reference points at an anonymous implicit type; there is no named
         type to refer to, so render it inline. *)
      (None, Some (signature (match sign with Some s -> s | None -> ft)))
  | None ->
      (Option.map (fun i -> idx ctx `Type i) typ, Option.map signature sign)

let string_of_name (nm : Src.name) : Ast.location Ast.instr =
  {
    desc = Ast.String (None, nm.Wax_utils.Ast.desc);
    info = nm.Wax_utils.Ast.info;
    hints = Wax_wasm.Hints.none;
    expected = Unset;
  }

(* Reserve, in a function's fresh local namespace, the Wax names of the
   module-level entities its body references by a bare identifier: globals (via
   [global.get]/[global.set]), functions (via [call]/[return_call]/[ref.func]),
   the memories/tables a memory/table access names as its receiver
   ([mem.load(..)], [tab[..]], [tab.size()], …), and the data/element segments
   named by [seg.drop()] / [mem.init] / [tab.init] / array segment ops. Without
   this an auto-named local could be assigned a colliding name and shadow the
   reference, since Wax resolves a bare name to a local before anything else. *)
let rec reserve_module_names_in_instr ctx ns (i : _ Src.instr) =
  match i.desc with
  | Block { block; _ } | Loop { block; _ } | TryTable { block; _ } ->
      reserve_module_names_in_instrs ctx ns block.desc
  | If { if_block; else_block; _ } ->
      reserve_module_names_in_instrs ctx ns if_block.desc;
      reserve_module_names_in_instrs ctx ns else_block.desc
  | Try { block; catches; catch_all; _ } ->
      reserve_module_names_in_instrs ctx ns block.desc;
      List.iter
        (fun (_, block) ->
          reserve_module_names_in_instrs ctx ns block.Wax_utils.Ast.desc)
        catches;
      Option.iter
        (fun block ->
          reserve_module_names_in_instrs ctx ns block.Wax_utils.Ast.desc)
        catch_all
  | If_annotation { then_body; else_body; _ } ->
      reserve_module_names_in_instrs ctx ns then_body.desc;
      Option.iter
        (fun b -> reserve_module_names_in_instrs ctx ns b.Wax_utils.Ast.desc)
        else_body
  | Folded (i, l) ->
      reserve_module_names_in_instrs ctx ns l;
      reserve_module_names_in_instr ctx ns i
  | GlobalGet x | GlobalSet x -> Namespace.reserve ns (idx ctx `Global x).desc
  | Call f | ReturnCall f | RefFunc f ->
      Namespace.reserve ns (idx ctx `Func f).desc
  | Load (m, _, _)
  | LoadS (m, _, _, _, _)
  | Store (m, _, _)
  | StoreS (m, _, _, _)
  | Atomic (m, _, _)
  | MemorySize m
  | MemoryGrow m
  | MemoryFill m
  | VecLoad (m, _, _)
  | VecStore (m, _)
  | VecLoadSplat (m, _, _)
  | VecLoadLane (m, _, _, _)
  | VecStoreLane (m, _, _, _) ->
      Namespace.reserve ns (idx ctx `Mem m).desc
  | MemoryCopy (m, m') ->
      Namespace.reserve ns (idx ctx `Mem m).desc;
      Namespace.reserve ns (idx ctx `Mem m').desc
  | MemoryInit (m, d) ->
      Namespace.reserve ns (idx ctx `Mem m).desc;
      Namespace.reserve ns (idx ctx `Data d).desc
  | TableGet t
  | TableSet t
  | TableSize t
  | TableGrow t
  | TableFill t
  | CallIndirect (t, _)
  | ReturnCallIndirect (t, _) ->
      Namespace.reserve ns (idx ctx `Table t).desc
  | TableCopy (t, t') ->
      Namespace.reserve ns (idx ctx `Table t).desc;
      Namespace.reserve ns (idx ctx `Table t').desc
  | TableInit (t, e) ->
      Namespace.reserve ns (idx ctx `Table t).desc;
      Namespace.reserve ns (idx ctx `Elem e).desc
  | DataDrop d | ArrayNewData (_, d) | ArrayInitData (_, d) ->
      Namespace.reserve ns (idx ctx `Data d).desc
  | ElemDrop e | ArrayNewElem (_, e) | ArrayInitElem (_, e) ->
      Namespace.reserve ns (idx ctx `Elem e).desc
  | _ -> ()

and reserve_module_names_in_instrs ctx ns l =
  List.iter (reserve_module_names_in_instr ctx ns) l

(* Collect the Wax names of element segments referenced by table.init /
   elem.drop / array.new_elem / array.init_elem, so a declarative segment used
   this way is emitted explicitly rather than dropped. *)
let rec collect_elem_refs ctx acc (i : _ Src.instr) =
  match i.desc with
  | Block { block; _ } | Loop { block; _ } | TryTable { block; _ } ->
      collect_elem_refs_instrs ctx acc block.desc
  | If { if_block; else_block; _ } ->
      collect_elem_refs_instrs ctx acc if_block.desc;
      collect_elem_refs_instrs ctx acc else_block.desc
  | If_annotation { then_body; else_body; _ } ->
      collect_elem_refs_instrs ctx acc then_body.desc;
      Option.iter
        (fun b -> collect_elem_refs_instrs ctx acc b.Wax_utils.Ast.desc)
        else_body
  | Try { block; catches; catch_all; _ } ->
      collect_elem_refs_instrs ctx acc block.desc;
      List.iter
        (fun (_, b) -> collect_elem_refs_instrs ctx acc b.Wax_utils.Ast.desc)
        catches;
      Option.iter
        (fun b -> collect_elem_refs_instrs ctx acc b.Wax_utils.Ast.desc)
        catch_all
  | Folded (i, l) ->
      collect_elem_refs_instrs ctx acc l;
      collect_elem_refs ctx acc i
  | TableInit (_, e) | ElemDrop e | ArrayNewElem (_, e) | ArrayInitElem (_, e)
    -> (
      try Hashtbl.replace acc (idx ctx `Elem e).desc () with _ -> ())
  | _ -> ()

and collect_elem_refs_instrs ctx acc l = List.iter (collect_elem_refs ctx acc) l

(* Collect the wasm indices of locals referenced by a function body. A parameter
   that is both unnamed in the source and absent here needs no Wax name: it can
   be rendered anonymously instead of inventing one. Only numeric references
   matter, since an unnamed parameter has no [$id] to be referenced by. *)
let rec collect_local_refs acc (i : _ Src.instr) =
  match i.desc with
  | Block { block; _ } | Loop { block; _ } | TryTable { block; _ } ->
      collect_local_refs_instrs acc block.desc
  | If { if_block; else_block; _ } ->
      collect_local_refs_instrs acc if_block.desc;
      collect_local_refs_instrs acc else_block.desc
  | If_annotation { then_body; else_body; _ } ->
      collect_local_refs_instrs acc then_body.desc;
      Option.iter
        (fun b -> collect_local_refs_instrs acc b.Wax_utils.Ast.desc)
        else_body
  | Try { block; catches; catch_all; _ } ->
      collect_local_refs_instrs acc block.desc;
      List.iter
        (fun (_, b) -> collect_local_refs_instrs acc b.Wax_utils.Ast.desc)
        catches;
      Option.iter
        (fun b -> collect_local_refs_instrs acc b.Wax_utils.Ast.desc)
        catch_all
  | Folded (i, l) ->
      collect_local_refs_instrs acc l;
      collect_local_refs acc i
  | LocalGet x | LocalSet x | LocalTee x -> (
      match x.Ast.desc with Num n -> Hashtbl.replace acc n () | Id _ -> ())
  | _ -> ()

and collect_local_refs_instrs acc l = List.iter (collect_local_refs acc) l

(* The guard printed on a folded attribute (an [export]/[start] moved onto a
   definition) is its branch condition with the conjuncts already entailed by
   the target's own position ([ctx.cond_asm]) dropped: the target is emitted
   inside those enclosing conditionals, so repeating them would be redundant
   (and, worse, would re-accumulate on every round-trip). [location] anchors the
   condition, which has no source of its own in the binary. *)
let simplify_guard ctx ~location (syn : Wax_wasm.Ast.cond) :
    (Wax_wasm.Ast.cond, Ast.location) Ast.annotated =
  let rec conjuncts (c : Wax_wasm.Ast.cond) =
    match c with Cond_and l -> List.concat_map conjuncts l | c -> [ c ]
  in
  let kept =
    List.filter
      (fun c ->
        not
          (Cond.logical_implies ctx.cond_asm
             (Cond.of_cond ctx.cond_env ctx.cond_diag ~location c)))
      (conjuncts syn)
  in
  {
    Ast.desc = (match kept with [] -> syn | [ c ] -> c | l -> Cond_and l);
    info = location;
  }

(* Fold the branch conditions [entries] of some attribute that a [(…)] field
   attaches to a definition (an export, a start) into attribute guards on a
   target at [ctx.cond_asm]: drop the attribute where its branch is unreachable,
   keep it plain where the target's position already entails the branch, and
   otherwise guard it with the branch condition simplified against the position.
   [make guard nm] builds the attribute for one entry, [guard] being [None] for
   a plain attribute. *)
(* A synthesized attribute: one the conversion invents rather than reads, so it
   has no source span of its own and takes the entity's. *)
let synth_attr ~location attr_name attr_value attr_guard : Ast.attribute =
  { attr_name; attr_value; attr_guard; attr_span = location }

let folded_attrs ctx ~location entries make =
  List.filter_map
    (fun (c, syn, nm) ->
      if not (Cond.is_satisfiable (Cond.and_ ctx.cond_asm c)) then None
      else if Cond.logical_implies ctx.cond_asm c then Some (make None nm)
      else Some (make (Some (simplify_guard ctx ~location syn)) nm))
    entries

let exports ctx kind name e : Ast.attributes =
  (* Reuse the bare [#[export]] short form when the export name matches the
     field's own Wax name; only a differing name needs to be spelled out.
     [guard] makes just this export conditional. *)
  let attr guard (nm : Src.name) =
    let value =
      if nm.Wax_utils.Ast.desc = (name : Src.name).Wax_utils.Ast.desc then None
      else Some (string_of_name nm)
    in
    synth_attr ~location:name.Ast.info "export" value guard
  in
  (* [e] are the inline exports declared on this field (already in the right
     branch), so they inherit the field's reachability unconditionally. *)
  let inline = List.map (fun nm -> attr None nm) e in
  (* The table holds standalone exports; each is kept only when its branch is
     reachable here, plain or guarded per [folded_attrs]. *)
  let standalone =
    match Hashtbl.find_opt ctx.exports (kind, name.Ast.desc) with
    | None -> []
    | Some entries -> folded_attrs ctx ~location:name.Ast.info entries attr
  in
  (* When a field carries several exports, put the unnamed [#[export]] (the one
     reusing the field's own Wax name) first; [partition] is stable, so the rest
     keep their order. *)
  let unnamed, named =
    List.partition
      (fun (a : Ast.attribute) -> Option.is_none a.attr_value)
      (inline @ standalone)
  in
  unnamed @ named

(* The [#[start]] attribute(s) on function [name]: a [(start …)] whose branch is
   reachable here, plain or guarded like a standalone export. *)
let start_attribute ctx name : Ast.attributes =
  match Hashtbl.find_opt ctx.starts name.Wax_utils.Ast.desc with
  | None -> []
  | Some entries ->
      folded_attrs ctx ~location:name.Ast.info
        (List.map (fun (c, syn) -> (c, syn, ())) entries)
        (fun guard () ->
          synth_attr ~location:name.Wax_utils.Ast.info "start" None guard)

(* Compilation-hints proposal: the function's [metadata.code.compilation_priority]
   entry, back as the attributes it is written with. [#[priority]] always comes
   first, since it is what makes the entry exist; the reserved optimization value
   prints as [#[run_once]] rather than the number. *)
let priority_attributes ~location (p : Wax_wasm.Hints.priority option) :
    Ast.attributes =
  match p with
  | None -> []
  | Some { compilation; optimization } ->
      let num n = Some (Ast.no_loc_instr (Ast.Int (string_of_int n))) in
      let int_attr k n = synth_attr ~location k (num n) None in
      int_attr "priority" compilation
      :: Option.to_list
           (Option.map
              (fun o ->
                if o = Wax_wasm.Hints.run_once then
                  synth_attr ~location "run_once" None None
                else int_attr "optimization" o)
              optimization)

let single_expression ctx ~location l =
  match l with
  | [ e ] -> e
  | _ ->
      conversion_error ctx ~location
        (Wax_utils.Message.text
           "A constant expression must produce a single value.")

let rec modulefield ctx export_tbl (f : (_ Src.modulefield, _) Ast.annotated) =
  (* Sibling fields synthesised alongside [f] (e.g. an element segment for an
     inline table initializer), emitted right after it. *)
  let extra = ref [] in
  let desc : _ Ast.modulefield option =
    match f.desc with
    | Types t -> Some (Type (collapse_splices ctx (rectype ctx t)))
    | Import_group1 _ | Import_group2 _ ->
        (* Wax has no compact-import concept: flatten the group into individual
           imports (each converted as usual), which [group_imports] later
           re-forms as a Wax [import "m" { … }] block. *)
        extra :=
          List.concat_map
            (modulefield ctx export_tbl)
            (Wax_wasm.Ast_utils.expand_import_group f);
        None
    | Func { locals; instrs; typ; exports = e; priority; _ } ->
        let label, labels =
          LabelStack.push ~targeted:(label_targeted instrs) (LabelStack.make ())
            None
        in
        let ctx =
          let return_arity = snd (typeuse_arity ctx typ) in
          let local_namespace =
            let ns = Namespace.make () in
            reserve_module_names_in_instrs ctx ns instrs;
            ns
          in
          {
            ctx with
            locals =
              Sequence.make ~diagnostics:ctx.diagnostics local_namespace "x";
            local_valtypes = Hashtbl.create 16;
            labels;
            label_arities = [ (None, return_arity) ];
            block_params = [||];
            return_arity;
          }
        in
        let used_locals =
          let acc = Hashtbl.create 16 in
          collect_local_refs_instrs acc instrs;
          acc
        in
        (* Name a parameter, unless it is unnamed in the source and never
           referenced by the body, in which case it is rendered anonymously. Its
           index slot is still consumed so later locals stay correctly aligned.
           [i] is the parameter's position, i.e. its wasm local index. *)
        let convert_params ~claimed params =
          Array.mapi
            (fun i p ->
              let id, t = p.Wax_utils.Ast.desc in
              let pat =
                if
                  Option.is_none id
                  && not (Hashtbl.mem used_locals (Uint32.of_int i))
                then (
                  Sequence.skip ctx.locals;
                  None)
                else
                  let name =
                    Sequence.register' ~claimed ctx.locals export_tbl None id []
                  in
                  Some
                    (match id with
                    | None ->
                        (* Unnamed in the source but referenced by the body, so
                           it cannot be rendered anonymously: warn that a name
                           was invented, pointing at the parameter. *)
                        Wax_utils.Diagnostic.report ctx.diagnostics
                          ~location:p.Ast.info ~severity:Warning
                          ~warning:Wax_utils.Warning.Generated_name
                          ~message:
                            (Wax_utils.Message.text
                               (Printf.sprintf
                                  "An unnamed parameter is used; generating \
                                   the name '%s' for it."
                                  name))
                          ();
                        Ast.no_loc name
                    | Some id -> { id with Ast.desc = name })
              in
              let t = valtype ctx t in
              Option.iter
                (fun (nm : Ast.ident) ->
                  Hashtbl.replace ctx.local_valtypes nm.Ast.desc t)
                pat;
              annotated p.Ast.info pat t)
            params
        in
        let param_arr, result_arr =
          match typ with
          | _, Some { params; results } -> (params, results)
          | Some i, None -> (
              let functype =
                match implicit_functype ctx i with
                | Some ft -> Some ft
                | None -> (
                    match (lookup_type ctx Type i).typ with
                    | Func ft -> Some ft
                    | Struct _ | Array _ | Cont _ -> None)
              in
              match functype with
              | Some { params; results } -> (params, results)
              | None -> assert false)
          | None, None -> assert false (* Should not happen *)
        in
        (* Priority pass: claim every source name (params, then locals) before
           any unnamed entity is registered, so the generated default never
           displaces a real source name (a user local [$x] keeps [x], the
           unnamed one becomes [x_2], not the reverse). Renames are reported here
           once; [register']/[register] then take the claimed name as-is. *)
        let claimed = Hashtbl.create 16 in
        let claim id =
          match id with
          | Some nm
            when Lexer.is_valid_identifier nm.Wax_utils.Ast.desc
                 && not (Hashtbl.mem claimed nm.Ast.desc) ->
              Hashtbl.replace claimed nm.Ast.desc
                (Sequence.claim_name ctx.locals ~loc:nm.Ast.info nm.Ast.desc)
          | _ -> ()
        in
        Array.iter (fun p -> claim (fst p.Wax_utils.Ast.desc)) param_arr;
        List.iter (fun e -> claim (fst e.Wax_utils.Ast.desc)) locals;
        let sign =
          let params = convert_params ~claimed param_arr in
          Sequence.consume_currents ctx.locals;
          {
            Ast.params;
            results = Array.map (fun t -> valtype ctx t) result_arr;
          }
        in
        (* An anonymous implicit type has no name to reference; the inline [sign]
           above already carries its signature, so drop the named reference. *)
        let typ =
          match fst typ with
          | Some i when Option.is_some (implicit_functype ctx i) -> None
          | t -> Option.map (fun i -> idx ctx `Type i) t
        in
        List.iter
          (fun e ->
            Sequence.register ~claimed ctx.locals export_tbl None
              (fst e.Wax_utils.Ast.desc) [])
          locals;
        let locals = bind_locals ctx locals in
        let name = Sequence.get_current ctx.functions in
        Some
          (Func
             {
               name;
               typ;
               sign = Some sign;
               body = (label (), locals @ Stack.run (instructions ctx instrs));
               attributes =
                 priority_attributes ~location:name.Ast.info priority
                 @ start_attribute ctx name @ exports ctx Func name e;
             })
    | Import { module_; name = nm; desc; exports = e; _ } -> (
        (* Build a single [import "module" <decl>;]. A name-only
           [#[import = "name"]] is emitted only when the imported name differs
           from the Wax name; consecutive same-module imports are grouped into
           blocks in a later pass. *)
        let build ?(start = []) id kind export_kind =
          let attributes =
            start
            @ (if nm.Ast.desc = id.Wax_utils.Ast.desc then []
               else
                 [
                   synth_attr ~location:id.Wax_utils.Ast.info "import"
                     (Some (string_of_name nm))
                     None;
                 ])
            @ exports ctx export_kind id e
          in
          Some
            (Ast.Import
               {
                 module_;
                 decl =
                   { Ast.desc = { Ast.id; kind; attributes }; info = f.info };
               })
        in
        match desc with
        | Func { exact; typ } ->
            let typ, sign = typeuse ctx typ in
            let id = Sequence.get_current ctx.functions in
            (* An imported function named by [(start …)] carries a [#[start]]
               attribute, like a defined start function. *)
            build ~start:(start_attribute ctx id) id
              (Import_func { typ; sign; exact })
              Func
        | Tag typ ->
            let typ, sign = typeuse ctx typ in
            build (Sequence.get_current ctx.tags) (Import_tag { typ; sign }) Tag
        | Global typ ->
            let typ' = globaltype ctx typ in
            build
              (Sequence.get_current ctx.globals)
              (Import_global { mut = typ'.mut; typ = typ'.typ })
              Global
        | Memory lim ->
            let l = lim.Ast.desc in
            build
              (Sequence.get_current ctx.memories)
              (Import_memory
                 {
                   address_type = l.address_type;
                   limits = Some (l.mi, l.ma);
                   page_size_log2 = l.page_size_log2;
                   shared = l.shared;
                 })
              Memory
        | Table tt ->
            let l = tt.Src.limits.Ast.desc in
            build
              (Sequence.get_current ctx.tables)
              (Import_table
                 {
                   address_type = l.address_type;
                   reftype = reftype ctx tt.Src.reftype;
                   limits = Some (l.mi, l.ma);
                 })
              Table)
    | Global { typ; init; exports = e; _ } ->
        let typ' = globaltype ctx typ in
        let name = Sequence.get_current ctx.globals in
        Some
          (Global
             {
               name;
               mut = typ'.mut;
               typ = Some typ'.typ;
               def =
                 single_expression ctx ~location:f.info
                   (Stack.run (instructions ctx init));
               attributes = exports ctx Global name e;
             })
    | Tag { typ; exports = e; _ } ->
        let typ, sign = typeuse ctx typ in
        let name = Sequence.get_current ctx.tags in
        Some (Tag { name; typ; sign; attributes = exports ctx Tag name e })
    | Memory { limits = lim; init; exports = e; _ } ->
        let l = lim.Ast.desc in
        let name = Sequence.get_current ctx.memories in
        let data =
          match init with
          | None -> []
          | Some bytes ->
              [
                {
                  Ast.data_name = None;
                  offset = Ast.no_loc_instr (Ast.Int "0");
                  init = data_init_to_wax ctx bytes;
                };
              ]
        in
        Some
          (Memory
             {
               name;
               address_type = l.address_type;
               limits = Some (l.mi, l.ma);
               page_size_log2 = l.page_size_log2;
               shared = l.shared;
               data;
               attributes = exports ctx Memory name e;
             })
    | Data { init; mode; _ } ->
        let name = Sequence.get_current ctx.datas in
        let init = data_init_to_wax ctx init in
        let mode' : _ Ast.datamode =
          match mode with
          | Passive -> Passive
          | Active (memidx, off) ->
              Active
                ( idx ctx `Mem memidx,
                  single_expression ctx ~location:f.info
                    (Stack.run (instructions ctx off)) )
        in
        Some (Data { name = Some name; mode = mode'; init; attributes = [] })
    | Table { typ = tt; init; exports = e; _ } ->
        let name = Sequence.get_current ctx.tables in
        let l = tt.Src.limits.Ast.desc in
        let init =
          match init with
          | Init_default -> None
          | Init_expr ex ->
              Some
                (single_expression ctx ~location:f.info
                   (Stack.run (instructions ctx ex)))
          | Init_segment segs ->
              (* A per-element initializer is not expressible on the table
                 itself; desugar it into a separate active element segment
                 filling the table from offset 0. *)
              let elem_init =
                List.map
                  (fun ex ->
                    single_expression ctx ~location:f.info
                      (Stack.run (instructions ctx ex)))
                  segs
              in
              let elem : _ Ast.modulefield =
                Elem
                  {
                    name = Sequence.fresh_name ctx.elems;
                    reftype = reftype ctx tt.Src.reftype;
                    mode = EActive (name, Ast.no_loc_instr (Ast.Int "0"));
                    init = elem_init;
                    attributes = [];
                  }
              in
              extra := [ { f with desc = elem } ];
              None
        in
        Some
          (Table
             {
               name;
               address_type = l.address_type;
               reftype = reftype ctx tt.Src.reftype;
               limits = Some (l.mi, l.ma);
               init;
               attributes = exports ctx Table name e;
             })
    | Elem { typ; init; mode; _ } -> (
        (* Declare elems are regenerated by [to_wasm] from [call_ref] usage, so
           they are normally dropped. One referenced by table.init / elem.drop /
           array.*_elem still needs a binding: emit it as an empty passive
           segment, which is runtime-equivalent (a declarative segment is a
           dropped passive one — table.init traps, elem.drop is a no-op). *)
        match mode with
        | Declare ->
            let name = Sequence.get_current ctx.elems in
            if Hashtbl.mem ctx.referenced_elems name.Ast.desc then
              Some
                (Elem
                   {
                     name;
                     reftype = reftype ctx typ;
                     mode = EPassive;
                     init = [];
                     attributes = [];
                   })
            else None
        | Passive | Active _ ->
            let name = Sequence.get_current ctx.elems in
            let init =
              List.map
                (fun e ->
                  single_expression ctx ~location:f.info
                    (Stack.run (instructions ctx e)))
                init
            in
            let mode' : _ Ast.elemmode =
              match mode with
              | Passive -> EPassive
              | Active (tab, off) ->
                  EActive
                    ( idx ctx `Table tab,
                      single_expression ctx ~location:f.info
                        (Stack.run (instructions ctx off)) )
              | Declare -> assert false
            in
            Some
              (Elem
                 {
                   name;
                   reftype = reftype ctx typ;
                   mode = mode';
                   init;
                   attributes = [];
                 }))
    | Start _ | Export _ -> None
    (* A [(@feature "name")] annotation becomes a [#![feature = "name"]] inner
       attribute. *)
    | Feature_annotation name ->
        Some
          (Module_annotation
             [
               synth_attr ~location:name.Wax_utils.Ast.info "feature"
                 (Some (string_of_name name))
                 None;
             ])
    | String_global { typ; init; _ } ->
        let name = Sequence.get_current ctx.globals in
        Some
          (Global
             {
               name;
               mut = false;
               typ = None;
               def =
                 {
                   desc =
                     String
                       ( Option.map (idx ctx `Type) typ,
                         Wax_utils.Ast.concat_desc init );
                   info = f.Ast.info;
                   hints = Wax_wasm.Hints.none;
                   expected = Unset;
                 };
               attributes = [];
             })
    | Module_if_annotation { cond; then_fields; else_fields } ->
        (* Convert [then] before [else]: positional naming via [get_current]
           must consume names in the same order [register_names] registered
           them (then-branch first). A record literal would leave the field
           evaluation order unspecified (OCaml evaluates right-to-left), which
           would consume the names swapped and scramble them across branches.
           [with_cond] sets the branch assumption so per-branch declarations
           (e.g. an import with a branch-dependent signature) resolve correctly
           in the branch's bodies. *)
        let then_fields =
          {
            then_fields with
            Ast.desc =
              with_cond ctx ~location:f.info cond true (fun () ->
                  List.concat_map (modulefield ctx export_tbl) then_fields.desc);
          }
        in
        let else_fields =
          Option.map
            (fun (e :
                   ( ( Ast.location Src.modulefield,
                       Ast.location )
                     Ast.Annot.annotated
                     list,
                     Ast.location )
                   Ast.Annot.annotated) ->
              {
                e with
                Ast.desc =
                  with_cond ctx ~location:f.info cond false (fun () ->
                      List.concat_map (modulefield ctx export_tbl) e.desc);
              })
            else_fields
        in
        (* An [@else] emptied by pulling out its standalone exports carries no
           fields, so drop it; a conditional left empty in both branches -- e.g.
           one that held only a standalone [(export …)] now re-emitted as a
           guard on its target -- is a no-op and is dropped entirely. *)
        let else_fields =
          match else_fields with Some e when e.Ast.desc = [] -> None | e -> e
        in
        if then_fields.Ast.desc = [] && else_fields = None then None
        else Some (Conditional { cond; then_fields; else_fields })
  in
  Option.to_list (Option.map (fun desc -> { f with desc }) desc) @ !extra

(*** Implicit type elaboration and name registration ***)

let empty_functype : Src.functype = { params = [||]; results = [||] }

(* A hashable key identifying a function type up to the structural equality the
   WAT type-use abbreviation needs — parameter names and source locations
   ignored — so [elaborate_implicit_types] can dedup inline signatures against
   the known types with a hashtable set rather than an O(n) scan (which, run per
   inline signature, was quadratic and re-resolved references on every compare).

   Each parameter and result value type is keyed structurally, except a
   [(type …)] reference, which is resolved to its canonical type name first: a
   numeric [(type N)] and a symbolic [(type $s)] naming the *same* declared type
   must key equal, or a duplicate inline signature would mint a spurious implicit
   type and shift every later numeric type reference. A reference that does not
   resolve to a declared name (e.g. one pointing at an implicit type, which
   carries no name here) falls back to its raw index form. *)
let functype_key ctx (ft : Src.functype) =
  let heaptype_key (h : Src.heaptype) =
    match h with
    | Type i -> (
        match Sequence.get ctx.types i with
        | { Ast.desc = name; _ } -> `Named name
        | exception (Unresolved_reference _ | Numeric_ref_in_conditional _) ->
            `Raw i.Ast.desc)
    | h -> `Other h
  in
  let valtype_key (v : Src.valtype) =
    match v with
    | Ref { nullable; typ } -> `Ref (nullable, heaptype_key typ)
    | v -> `Scalar v
  in
  ( Array.map (fun p -> valtype_key (snd p.Wax_utils.Ast.desc)) ft.params,
    Array.map valtype_key ft.results )

(* Populate [ctx.implicit_types] with the function types the WAT text format
   synthesises from inline [(param)]/[(result)] signatures. Explicit type
   definitions occupy the low indices in source order; each inline signature
   then reuses the lowest-indexed identical type, or appends a new one at the
   end of the index space. This mirrors the spec's elaboration so that a numeric
   [(type N)] referring to such a type resolves to the right signature.

   Only called for modules without conditional annotations (where numeric
   references are allowed); there the index space is unambiguous. *)
let elaborate_implicit_types ctx fields =
  let next = ref 0 in
  (* Keys of the function types seen so far — explicit ones first, then minted
     implicit ones — used to decide whether an inline signature duplicates one
     already known (in which case it mints no fresh index). A set of keys, not a
     list scanned with [functype_eq], keeps this linear. *)
  let seen : (_, unit) Hashtbl.t = Hashtbl.create 64 in
  let record ft = Hashtbl.replace seen (functype_key ctx ft) () in
  (* Phase 1: explicit type definitions, in source order. *)
  List.iter
    (fun (field : (_ Src.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Types rectype ->
          Array.iter
            (fun e ->
              (match (snd e.Wax_utils.Ast.desc : Src.subtype).typ with
              | Func ft -> record ft
              | Struct _ | Array _ | Cont _ -> ());
              incr next)
            rectype
      | _ -> ())
    fields;
  (* Phase 2: every inline signature, in source order, appended after the
     explicit types. *)
  let consider ((typ, sign) : Src.typeuse) =
    match typ with
    | Some _ -> () (* references an existing type; mints nothing *)
    | None ->
        let ft = Option.value sign ~default:empty_functype in
        let key = functype_key ctx ft in
        if not (Hashtbl.mem seen key) then (
          Hashtbl.replace ctx.implicit_types (Uint32.of_int !next) ft;
          Hashtbl.replace seen key ();
          incr next)
  in
  let blocktype = function Some (Src.Typeuse tu) -> consider tu | _ -> () in
  let rec instr (i : _ Src.instr) =
    match i.desc with
    | CallIndirect (_, tu) | ReturnCallIndirect (_, tu) -> consider tu
    | Block { typ; block; _ } | Loop { typ; block; _ } ->
        blocktype typ;
        instrs block.desc
    | If { typ; if_block; else_block; _ } ->
        blocktype typ;
        instrs if_block.Ast.desc;
        instrs else_block.Ast.desc
    | TryTable { typ; block; _ } ->
        blocktype typ;
        instrs block.desc
    | Try { typ; block; catches; catch_all; _ } ->
        blocktype typ;
        instrs block.desc;
        List.iter (fun (_, b) -> instrs b.Wax_utils.Ast.desc) catches;
        Option.iter (fun b -> instrs b.Wax_utils.Ast.desc) catch_all
    | If_annotation { then_body; else_body; _ } ->
        instrs then_body.desc;
        Option.iter (fun b -> instrs b.Wax_utils.Ast.desc) else_body
    | Folded (i, l) ->
        instr i;
        instrs l
    | _ -> ()
  and instrs l = List.iter instr l in
  List.iter
    (fun (field : (_ Src.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Func { typ; instrs = body; _ } ->
          consider typ;
          instrs body
      | Import { desc = Func { typ = tu; _ }; _ } | Import { desc = Tag tu; _ }
        ->
          consider tu
      | Tag { typ; _ } -> consider typ
      | Global { init; _ } -> instrs init
      | Elem { init; _ } -> List.iter instrs init
      | Table { init = Init_expr e; _ } -> instrs e
      | Table { init = Init_segment l; _ } -> List.iter instrs l
      (* Groups are flattened below, so only their [Import] members reach here. *)
      | Import_group1 _ | Import_group2 _ | Types _ | Import _ | Memory _
      | Table _ | Export _ | Start _ | Data _ | String_global _
      | Feature_annotation _ | Module_if_annotation _ ->
          ())
    (List.concat_map Wax_wasm.Ast_utils.expand_import_group fields)

let register_names ctx export_tbl fields =
  (* Both passes recurse into the branches of a conditional, in the same order
     the converter visits them, so positional naming stays aligned. *)
  let rec pass1 fields =
    List.iter
      (fun (field : (_ Src.modulefield, _) Ast.annotated) ->
        match field.desc with
        | Import { id; name; desc; exports; _ } -> (
            (* Failing an explicit [$id] and an export name, borrow the imported
               name as the Wax name (like an export name), so an imported
               [malloc] is named [malloc] rather than the generic default. *)
            let hint =
              if Lexer.is_valid_identifier name.Ast.desc then Some name.Ast.desc
              else None
            in
            match desc with
            | Func _ -> ()
            | Memory limits ->
                (* Record the address type exactly as for a module-defined
                   memory: an import's [size]/[grow] results state it too (an
                   unrecorded one was a recording gap the [--debug width-record]
                   census found). *)
                record_address_type ctx
                  (Sequence.register' ?hint ctx.memories export_tbl
                     (Some (Memory : Src.exportable))
                     id exports)
                  limits.Ast.desc.address_type
            | Table typ ->
                record_address_type ctx
                  (Sequence.register' ?hint ctx.tables export_tbl (Some Table)
                     id exports)
                  typ.Src.limits.Ast.desc.address_type
            | Global typ ->
                record_global_valtype ctx typ
                  (Sequence.register' ?hint ctx.globals export_tbl (Some Global)
                     id exports)
            | Tag ty -> register_type ?hint ctx export_tbl Tag id exports ty)
        | Types rectype ->
            Array.iter
              (fun e ->
                let id, ty = e.Wax_utils.Ast.desc in
                let name = Sequence.register' ctx.types export_tbl None id [] in
                CondTbl.add ctx.type_defs ctx.cond_asm name ty;
                match (ty : Src.subtype).typ with
                | Func _ | Array _ | Cont _ -> ()
                | Struct l ->
                    let seq =
                      Sequence.make ~diagnostics:ctx.diagnostics
                        (Namespace.make ()) "f"
                    in
                    (* A struct subtype inherits its supertype's fields by
                       position, so an unnamed field can borrow the name the
                       parent gave that slot rather than the generic "f". *)
                    let parent_fields =
                      match ty.supertype with
                      | None -> [||]
                      | Some sup -> (
                          match Sequence.get ctx.types sup with
                          | exception
                              ( Unresolved_reference _
                              | Numeric_ref_in_conditional _ ) ->
                              [||]
                          | { desc = parent; _ } -> (
                              match
                                Hashtbl.find_opt ctx.struct_fields parent
                              with
                              | Some (_, names) -> Array.of_list names
                              | None -> [||]))
                    in
                    let fields =
                      Array.mapi
                        (fun i t ->
                          let hint =
                            if i < Array.length parent_fields then
                              Some parent_fields.(i)
                            else None
                          in
                          Sequence.register' ?hint seq export_tbl None
                            (get_annot t) [])
                        l
                    in
                    Hashtbl.replace ctx.struct_fields name
                      (seq, Array.to_list fields))
              rectype
        | Global { id; exports; typ; _ } ->
            record_global_valtype ctx typ
              (Sequence.register' ctx.globals export_tbl (Some Global) id
                 exports)
        (* Groups are flattened below, so only their [Import] members reach here. *)
        | Func _ | Export _ | Start _ | Import_group1 _ | Import_group2 _
        | Feature_annotation _ ->
            ()
        | Elem { id; _ } -> Sequence.register ctx.elems export_tbl None id []
        | Data { id; _ } -> Sequence.register ctx.datas export_tbl None id []
        | Memory { id; exports; limits; _ } ->
            (* [register'] rather than [register]: the Wax name it returns is the
               key the address type is remembered under. ([get_current] must not be
               used here — it advances the conversion pass's positional cursor.) *)
            record_address_type ctx
              (Sequence.register' ctx.memories export_tbl (Some Memory) id
                 exports)
              limits.Ast.desc.address_type
        | Table { id; exports; typ; _ } ->
            record_address_type ctx
              (Sequence.register' ctx.tables export_tbl (Some Table) id exports)
              typ.Src.limits.Ast.desc.address_type
        | Tag { id; exports; typ; _ } ->
            register_type ctx export_tbl Tag id exports typ
        | String_global { id; _ } ->
            Sequence.register ctx.globals export_tbl (Some Global) (Some id) []
        | Module_if_annotation { then_fields; else_fields; cond } ->
            with_cond ctx ~location:field.info cond true (fun () ->
                pass1 then_fields.desc);
            Option.iter
              (fun e ->
                with_cond ctx ~location:field.info cond false (fun () ->
                    pass1 e.Wax_utils.Ast.desc))
              else_fields)
      (List.concat_map Wax_wasm.Ast_utils.expand_import_group fields)
  in
  let rec pass2 fields =
    List.iter
      (fun (field : (_ Src.modulefield, _) Ast.annotated) ->
        match field.desc with
        | Import { id; name; desc; exports; _ } -> (
            match desc with
            | Func { typ; _ } ->
                let hint =
                  if Lexer.is_valid_identifier name.Ast.desc then
                    Some name.Ast.desc
                  else None
                in
                register_type ?hint ctx export_tbl Func id exports typ
            | Memory _ | Table _ | Global _ | Tag _ -> ())
        | Func { id; exports; typ; _ } ->
            register_type ctx export_tbl Func id exports typ
        | Module_if_annotation { then_fields; else_fields; cond } ->
            with_cond ctx ~location:field.info cond true (fun () ->
                pass2 then_fields.desc);
            Option.iter
              (fun e ->
                with_cond ctx ~location:field.info cond false (fun () ->
                    pass2 e.Wax_utils.Ast.desc))
              else_fields
        | Types _ | Global _ | Export _ | Start _ | Elem _ | Data _ | Memory _
        | Table _ | Tag _ | String_global _ | Import_group1 _ | Import_group2 _
        | Feature_annotation _ ->
            ())
      (List.concat_map Wax_wasm.Ast_utils.expand_import_group fields)
  in
  pass1 fields;
  pass2 fields

let collect_exports cond_env diagnostics fields =
  let tbl = Hashtbl.create 16 in
  let lst = ref [] in
  let start_lst = ref [] in
  (* Combine the accumulated branch conditions ([syn], a list of conjuncts, each
     already negated for an [@else]) into one syntactic condition, kept alongside
     the solved [asm] so a standalone export narrower than its target can be
     re-emitted as a [#[export …, if <cond>]] guard. *)
  let combine syn : Wax_wasm.Ast.cond =
    match syn with [ c ] -> c | l -> Cond_and l
  in
  (* [asm]/[syn] are the branch assumption under which the fields being walked
     appear (solved / syntactic), so each standalone export is recorded with the
     condition that guards it. *)
  let rec go asm syn fields =
    List.iter
      (fun (field : (_ Src.modulefield, _) Ast.annotated) ->
        match field.desc with
        | Export { name; kind; index } ->
            (* Don't keep a meaningless location *)
            lst := (kind, index, Ast.no_loc name.desc, asm, combine syn) :: !lst;
            let k = (kind, index.Ast.desc) in
            Hashtbl.replace tbl k
              (name :: (try Hashtbl.find tbl k with Not_found -> []))
        | Start index -> start_lst := (index, asm, combine syn) :: !start_lst
        | Module_if_annotation { cond; then_fields; else_fields } ->
            let c =
              Cond.of_cond cond_env diagnostics ~location:field.info cond
            in
            go (Cond.and_ asm c) (syn @ [ cond ]) then_fields.desc;
            Option.iter
              (fun e ->
                go
                  (Cond.and_ asm (Cond.not_ c))
                  (syn @ [ Cond_not cond ]) e.Wax_utils.Ast.desc)
              else_fields
        | _ -> ())
      fields
  in
  go Cond.true_ [] fields;
  (tbl, !lst, !start_lst)

(*** Module conversion ***)

let rec module_has_conditional fields =
  List.exists
    (fun (f : (_ Src.modulefield, _) Ast.annotated) ->
      match f.desc with
      | Module_if_annotation { then_fields; else_fields; _ } ->
          module_has_conditional then_fields.desc
          || Option.fold ~none:false
               ~some:(fun e -> module_has_conditional e.Wax_utils.Ast.desc)
               else_fields
          || true
      | _ -> false)
    fields

(* A compact import group ([Import_group1]/[Import_group2]) can hold several
   memory/table imports, so expand it into individual imports before counting —
   as every other module walk does. Miscounting leaves [forbid_numeric_memory]/
   [forbid_numeric_table] off under conditionals, degrading a later numeric-
   reference diagnostic. *)
let rec count_memories fields =
  List.fold_left
    (fun n (f : (_ Src.modulefield, _) Ast.annotated) ->
      match f.desc with
      | Memory _ | Import { desc = Memory _; _ } -> n + 1
      | Module_if_annotation { then_fields; else_fields; _ } ->
          n
          + max
              (count_memories then_fields.desc)
              (Option.fold ~none:0
                 ~some:(fun e -> count_memories e.Wax_utils.Ast.desc)
                 else_fields)
      | _ -> n)
    0
    (List.concat_map Wax_wasm.Ast_utils.expand_import_group fields)

let rec count_tables fields =
  List.fold_left
    (fun n (f : (_ Src.modulefield, _) Ast.annotated) ->
      match f.desc with
      | Table _ | Import { desc = Table _; _ } -> n + 1
      | Module_if_annotation { then_fields; else_fields; _ } ->
          n
          + max
              (count_tables then_fields.desc)
              (Option.fold ~none:0
                 ~some:(fun e -> count_tables e.Wax_utils.Ast.desc)
                 else_fields)
      | _ -> n)
    0
    (List.concat_map Wax_wasm.Ast_utils.expand_import_group fields)

(* The [type <name> = fn(..)] declarations for implicit function types that were
   named because a ref-type referenced them ([type_ref_name]). Converting a
   signature can itself name further implicit types (a nested ref-type use), so
   drain [named_implicit] to a fixpoint; a dependency named while converting an
   earlier one is emitted before it. *)
let extra_type_decls ctx =
  let rec loop acc =
    match ctx.named_implicit with
    | [] -> acc
    | pending ->
        ctx.named_implicit <- [];
        let decls =
          List.rev_map
            (fun (name, ft) ->
              let name = Ast.no_loc name in
              let sub : Ast.subtype =
                {
                  typ = Func (functype ctx ft);
                  supertype = None;
                  final = true;
                  descriptor = None;
                  describes = None;
                }
              in
              Ast.no_loc (Ast.Type [| annotated name.Ast.info name sub |]))
            pending
        in
        loop (decls @ acc)
  in
  loop []

(* Merge maximal runs of consecutive single imports from the same module into
   one [import "module" { ... }] block; a lone import stays as the standalone
   [import "module" <decl>;] form. Recurses through groups and conditionals. *)
let rec group_imports fields =
  let recurse (f : (_ Ast.modulefield, _) Ast.Annot.annotated) =
    match f.desc with
    | Ast.Conditional c ->
        {
          f with
          Ast.desc =
            Ast.Conditional
              {
                c with
                then_fields =
                  {
                    c.then_fields with
                    Ast.desc = group_imports c.then_fields.Ast.desc;
                  };
                else_fields =
                  Option.map
                    (fun b ->
                      { b with Ast.Annot.desc = group_imports b.Ast.Annot.desc })
                    c.else_fields;
              };
        }
    | _ -> f
  in
  let rec merge acc = function
    | [] -> List.rev acc
    | (f : (_ Ast.modulefield, _) Ast.Annot.annotated) :: rest -> (
        match f.desc with
        | Ast.Import { module_; decl } ->
            let rec take group_acc = function
              | (g : (_ Ast.modulefield, _) Ast.Annot.annotated) :: tl
                when match g.desc with
                     | Ast.Import { module_ = m2; _ } ->
                         m2.Ast.desc = module_.desc
                     | _ -> false ->
                  let d =
                    match g.Ast.desc with
                    | Ast.Import { decl; _ } -> decl
                    | _ -> assert false
                  in
                  take (d :: group_acc) tl
              | tl -> (List.rev group_acc, tl)
            in
            let decls, tl = take [ decl ] rest in
            let field =
              match decls with
              | [ _ ] -> f
              | _ -> { f with Ast.desc = Ast.Import_group { module_; decls } }
            in
            merge (field :: acc) tl
        | _ -> merge (f :: acc) rest)
  in
  merge [] (List.map recurse fields)

let module_ ?(strict_constants = false) ?(faithful = false) ?features
    diagnostics (module_name, fields) =
  Wax_utils.Debug.timed "convert" @@ fun () ->
  try
    let forbid_numeric = module_has_conditional fields in
    (* Loads/stores reference the memory implicitly by index 0. When the module
     has a single memory that numeric reference is unambiguous (even if the
     memory itself sits in a conditional branch), so numeric memory references
     are allowed; with several memories, indices may shift across branches like
     any other field, so the general constraint stands. *)
    let forbid_numeric_memory = forbid_numeric && count_memories fields > 1 in
    let forbid_numeric_table = forbid_numeric && count_tables fields > 1 in
    let ctx =
      let common_namespace = Namespace.make () in
      {
        diagnostics;
        types =
          Sequence.make ~forbid_numeric ~diagnostics
            (Namespace.make ~kind:`Type ())
            "t";
        struct_fields = Hashtbl.create 16;
        globals =
          Sequence.make ~forbid_numeric ~diagnostics common_namespace "g";
        functions =
          Sequence.make ~forbid_numeric ~diagnostics common_namespace "f";
        memories =
          Sequence.make ~forbid_numeric:forbid_numeric_memory
            ~is_conditional:forbid_numeric ~diagnostics common_namespace "m";
        tables =
          Sequence.make ~forbid_numeric:forbid_numeric_table
            ~is_conditional:forbid_numeric ~diagnostics common_namespace "t";
        tags =
          Sequence.make ~forbid_numeric ~diagnostics (Namespace.make ()) "t";
        datas = Sequence.make ~forbid_numeric ~diagnostics common_namespace "d";
        elems = Sequence.make ~forbid_numeric ~diagnostics common_namespace "e";
        referenced_elems = Hashtbl.create 16;
        type_defs = CondTbl.make ();
        implicit_types = Hashtbl.create 16;
        named_implicit = [];
        function_types = CondTbl.make ();
        tag_types = CondTbl.make ();
        exports = Hashtbl.create 16;
        starts = Hashtbl.create 16;
        locals = Sequence.make ~diagnostics common_namespace "x";
        local_valtypes = Hashtbl.create 16;
        global_valtypes = Hashtbl.create 16;
        labels = LabelStack.make ();
        label_arities = [];
        block_params = [||];
        return_arity = 0;
        strict_constants;
        faithful;
        address_types = Hashtbl.create 8;
        multi_ref_results = Hashtbl.create 8;
        cond_env = Cond.create ();
        cond_diag = Wax_utils.Diagnostic.collector ();
        cond_asm = Cond.true_;
      }
    in
    let export_tbl, export_lst, start_lst =
      collect_exports ctx.cond_env ctx.cond_diag fields
    in
    register_names ctx export_tbl fields;
    if not forbid_numeric then elaborate_implicit_types ctx fields;
    (* Resolve each [(start …)] to its function's Wax name, keeping the branch
       condition it appeared under; rendered as a [#[start]] attribute on that
       function (guarded when the start is narrower than the function). *)
    List.iter
      (fun (index, asm, syn) ->
        let name = (idx ctx `Func index).Ast.desc in
        Hashtbl.replace ctx.starts name
          ((asm, syn)
          :: Option.value ~default:[] (Hashtbl.find_opt ctx.starts name)))
      start_lst;
    List.iter
      (fun (kind, index, name, asm, syn) ->
        let k =
          ( kind,
            (idx ctx
               (match (kind : Src.exportable) with
               | Func -> `Func
               | Memory -> `Mem
               | Table -> `Table
               | Tag -> `Tag
               | Global -> `Global)
               index)
              .desc )
        in
        let l =
          (asm, syn, name)
          ::
          (match Hashtbl.find_opt ctx.exports k with
          | None -> []
          | Some l -> l)
        in
        Hashtbl.replace ctx.exports k l)
      export_lst;
    (* Record which element segments are referenced by table.init / elem.drop /
     array.*_elem (recursing into conditional branches), so a declarative
     segment used this way is declared rather than dropped. *)
    let rec collect_field (f : (_ Src.modulefield, _) Ast.annotated) =
      match f.Ast.desc with
      | Func { instrs; _ } ->
          collect_elem_refs_instrs ctx ctx.referenced_elems instrs
      | Module_if_annotation { then_fields; else_fields; _ } ->
          List.iter collect_field then_fields.desc;
          Option.iter
            (fun e -> List.iter collect_field e.Wax_utils.Ast.desc)
            else_fields
      | _ -> ()
    in
    List.iter collect_field fields;
    let converted =
      List.concat_map (fun f -> modulefield ctx export_tbl f) fields
    in
    (* Prepend the type declarations synthesised for implicit types named by a
       ref-type reference (computed after conversion, which is what names them). *)
    let converted = extra_type_decls ctx @ converted in
    let recovered =
      Recover_match.module_ ~faithful
        (Sink_let.module_
           (Recover_loops.module_
              (Recover_trycatch.module_ (Recover_dispatch.module_ converted))))
    in
    (* A named module becomes a leading [#![module = "name"]] inner attribute. *)
    let name_annotation =
      match module_name with
      | Some nm ->
          [
            Ast.no_loc
              (Ast.Module_annotation
                 [
                   synth_attr ~location:nm.Wax_utils.Ast.info "module"
                     (Some (string_of_name nm))
                     None;
                 ]);
          ]
      | None -> []
    in
    (* Stamp a [#![feature = "…"]] inner attribute for each gated feature the
       module was seen to exercise ([Feature.used], recorded by the binary
       decoder and by validation), so the output recompiles standalone. A
       feature the module already declares with a [(@feature "…")] annotation
       was converted above; do not stamp it twice. *)
    let feature_annotations =
      match features with
      | None -> []
      | Some features ->
          let declared =
            List.filter_map
              (fun (f : (_ Src.modulefield, _) Ast.annotated) ->
                match f.desc with
                | Feature_annotation nm -> Wax_utils.Feature.of_name nm.desc
                | _ -> None)
              fields
          in
          List.filter_map
            (fun feature ->
              if List.mem feature declared then None
              else
                Some
                  (Ast.no_loc
                     (Ast.Module_annotation
                        [
                          synth_attr ~location:Wax_utils.Ast.dummy_loc "feature"
                            (Some
                               (Ast.no_loc_instr
                                  (Ast.String
                                     (None, Wax_utils.Feature.name feature))))
                            None;
                        ])))
            (Wax_utils.Feature.used features)
    in
    name_annotation @ feature_annotations @ group_imports recovered
  with
  | Numeric_ref_in_conditional location ->
      Wax_utils.Diagnostic.report diagnostics ~location ~severity:Error
        ~message:
          (Wax_utils.Message.text
             "Numeric references to module fields are not supported in a \
              module with conditional annotations; use a symbolic $name.")
        ();
      Wax_utils.Diagnostic.abort ()
  | Unresolved_reference location ->
      Wax_utils.Diagnostic.report diagnostics ~location ~severity:Error
        ~message:
          (Wax_utils.Message.text
             "This reference resolves to nothing: it is out of range or names \
              an undeclared entity.")
        ();
      Wax_utils.Diagnostic.abort ()
