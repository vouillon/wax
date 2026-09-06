let validate_refs = ref true

module Uint32 = Wax_utils.Uint32
module Uint64 = Wax_utils.Uint64
open Types.Internal
module Nz = Types.Normalized

(* The [@]-suffixed operators sequence [option] computations, short-circuiting
   on [None]: [let*@] binds, [let+@] maps, and [let>@] runs the body for its
   side effect and discards the result. (The unsuffixed [let*]/[let*!]/[let*?]
   defined further down instead thread the value stack.) *)
let ( let*@ ) = Option.bind
let ( let+@ ) o f = Option.map f o
let ( let>@ ) o f = Option.iter f o

(*** Source types and printers ***)

(* WAT types and identifiers are rendered directly into a diagnostic's styled
   printer (see {!Wax_utils.Styled_printer}), so an embedded type shares the
   message's colour theme and width — rather than being pre-rendered to a flat
   string. These helpers wrap the layout/colour primitives. *)
let sp_space pp = Wax_utils.Printer.space pp.Wax_utils.Styled_printer.printer ()

let sp_box pp f =
  Wax_utils.Printer.box pp.Wax_utils.Styled_printer.printer ~indent:1 f

let sp_type pp s =
  Wax_utils.Styled_printer.print_styled pp Wax_utils.Colors.Type s

let sp_kw pp s =
  Wax_utils.Styled_printer.print_styled pp Wax_utils.Colors.Keyword s

let sp_punct pp s =
  Wax_utils.Styled_printer.print_styled pp Wax_utils.Colors.Punctuation s

let print_string pp s =
  let len, escaped = Wax_utils.Unicode.escape_string s.Ast.desc in
  Wax_utils.Styled_printer.print_styled pp Wax_utils.Colors.String
    ~len:(Some len) escaped

let print_ident pp id =
  let s =
    if Lexer.is_valid_identifier id then "$" ^ id
    else "$\"" ^ snd (Wax_utils.Unicode.escape_string id) ^ "\""
  in
  Wax_utils.Styled_printer.print_styled pp Wax_utils.Colors.Identifier s

let print_index pp (idx : Ast.Text.idx) =
  match idx.desc with
  | Num n ->
      Wax_utils.Styled_printer.print_styled pp Wax_utils.Colors.Constant
        (Uint32.to_string n)
  | Id id -> print_ident pp id

(* Render a type as the source wrote it, naming an indexed type by its source
   reference ($foo or a number) rather than an interned canonical index. *)
let print_text_heaptype pp (ty : Ast.Text.heaptype) =
  match Ast.Text.heaptype_keyword ty with
  | Some kw -> sp_type pp kw
  | None -> (
      match ty with
      | Type idx -> print_index pp idx
      | Exact idx ->
          sp_box pp (fun () ->
              sp_punct pp "(";
              sp_kw pp "exact";
              sp_space pp;
              print_index pp idx;
              sp_punct pp ")")
      | _ -> assert false)

let print_text_valtype pp (ty : Ast.Text.valtype) =
  match ty with
  | I32 -> sp_type pp "i32"
  | I64 -> sp_type pp "i64"
  | F32 -> sp_type pp "f32"
  | F64 -> sp_type pp "f64"
  | V128 -> sp_type pp "v128"
  | Ref { nullable; typ } ->
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "ref";
          sp_space pp;
          if nullable then (
            sp_kw pp "null";
            sp_space pp);
          print_text_heaptype pp typ;
          sp_punct pp ")")

let print_text_storagetype pp (ty : Ast.Text.storagetype) =
  match ty with
  | Value v -> print_text_valtype pp v
  | Packed I8 -> sp_type pp "i8"
  | Packed I16 -> sp_type pp "i16"

let print_text_fieldtype pp ({ mut; typ } : Ast.Text.fieldtype) =
  if mut then
    sp_box pp (fun () ->
        sp_punct pp "(";
        sp_kw pp "mut";
        sp_space pp;
        print_text_storagetype pp typ;
        sp_punct pp ")")
  else print_text_storagetype pp typ

let print_text_functype pp ({ params; results } : Ast.Text.functype) =
  Array.iter
    (fun p ->
      sp_space pp;
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "param";
          sp_space pp;
          print_text_valtype pp (snd p.Ast.desc);
          sp_punct pp ")"))
    params;
  Array.iter
    (fun t ->
      sp_space pp;
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "result";
          sp_space pp;
          print_text_valtype pp t;
          sp_punct pp ")"))
    results

(* Render a composite type as its source signature, for a reference to a type
   the user did not name (an implicit [ref.func] type, the internal string
   type). *)
let print_text_comptype pp (ty : Ast.Text.comptype) =
  match ty with
  | Func ft ->
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "func";
          print_text_functype pp ft;
          sp_punct pp ")")
  | Array ft ->
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "array";
          sp_space pp;
          print_text_fieldtype pp ft;
          sp_punct pp ")")
  | Struct fields ->
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "struct";
          Array.iter
            (fun e ->
              let _, ft = e.Ast.desc in
              sp_space pp;
              sp_box pp (fun () ->
                  sp_punct pp "(";
                  sp_kw pp "field";
                  sp_space pp;
                  print_text_fieldtype pp ft;
                  sp_punct pp ")"))
            fields;
          sp_punct pp ")")
  | Cont idx ->
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "cont";
          sp_space pp;
          print_index pp idx;
          sp_punct pp ")")

(* The source rendering of a stack value: either a value type the user wrote
   (or that names a type the user declared), or — for a reference whose type has
   no source name — that referenced type's signature, shown inline. *)
type source_type =
  | Plain of Ast.Text.valtype
  | Inline_ref of Ast.Text.comptype
  (* The bottom reference type [(ref bot)]. It has no user-written form; it is
     synthesized only to render a stack value of the bottom reference type in a
     diagnostic (e.g. when such a value reaches a numeric context). *)
  | Bottom_ref

let print_source_type pp = function
  | Plain v -> print_text_valtype pp v
  | Inline_ref comptype ->
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "ref";
          sp_space pp;
          print_text_comptype pp comptype;
          sp_punct pp ")")
  | Bottom_ref ->
      sp_box pp (fun () ->
          sp_punct pp "(";
          sp_kw pp "ref";
          sp_space pp;
          sp_type pp "bot";
          sp_punct pp ")")

(* Render a source type to a plain (uncoloured) string. *)
let render_source_type source =
  String.trim
    (Wax_utils.Printer.run_string (fun p ->
         let pp =
           Wax_utils.Styled_printer.create ~printer:p
             ~theme:Wax_utils.Colors.no_color
             ~trivia:(Wax_utils.Trivia.empty ())
             ()
         in
         print_source_type pp source))

(* What the editor type sink records at each instruction span. Kept unrendered:
   the recording pass runs over the whole module, but the editor renders only
   the few entries under the cursor, so rendering is deferred to
   [render_recorded_type]. *)
type recorded_type =
  | Pushed of source_type (* a value the instruction leaves on the stack *)
  | Polymorphic (* the unknown value of an unreachable / polymorphic stack *)
  | No_result (* the instruction produces no value *)
  | Signature of source_type array * source_type array
    (* a function's (params, results), for the identifier of a call / ref.func *)
  | Subtype of
      (Ast.Text.name option * Ast.Text.subtype, Ast.location) Ast.annotated
    (* the source definition of the type a type identifier refers to *)
  | Value_type of Ast.location
(* the definition span of a value's named reference type, for go-to-type-def;
   carries no display type (a [Pushed] at the same span renders the value) *)

let render_recorded_type = function
  | Pushed source -> Some (render_source_type source)
  | Polymorphic -> Some "any"
  | No_result | Value_type _ -> None
  | Subtype e -> Some (Output.subtype_string e)
  | Signature (params, results) ->
      let group kw arr =
        if Array.length arr = 0 then None
        else
          Some
            (Printf.sprintf "(%s %s)" kw
               (String.concat " "
                  (Array.to_list (Array.map render_source_type arr))))
      in
      let parts =
        List.filter_map Fun.id [ group "param" params; group "result" results ]
      in
      Some
        (Printf.sprintf "(func%s)"
           (String.concat "" (List.map (fun s -> " " ^ s) parts)))

(* The definition span of the type a recorded entry refers to, for
   go-to-type-definition: a value's named reference type, or the type a type
   identifier names; [None] otherwise. *)
let type_def_location = function
  | Value_type l -> Some l
  | Subtype e -> (
      match fst e.Ast.desc with
      | Some (n : Ast.Text.name) -> Some n.Ast.info
      | None -> Some e.Ast.info)
  | Pushed _ | Polymorphic | No_result | Signature _ -> None

(* The rendered parameter and result types of a recorded function signature (a
   [call]/[ref.func] identifier), for signature help; [None] for any other kind. *)
let signature_labels = function
  | Signature (params, results) ->
      Some
        ( Array.to_list (Array.map render_source_type params),
          Array.to_list (Array.map render_source_type results) )
  | _ -> None

(* Editor type sink. Like [validate_refs], a module-level ref rather than a
   threaded parameter: the push chokepoints below record into it without
   carrying it through the ~130 call sites. When set (only in editor mode, via
   [f]'s [?record_types]), every value pushed onto the stack is recorded as
   [(span of the pushing instruction, configuration index, type)] — the raw
   material for WAT hover. The configuration index distinguishes entries from
   different explored configurations (conditional compilation), so a consumer can
   join a single configuration's stack results as a tuple yet keep the types a
   config-varying span takes across configurations apart. [None] on ordinary
   validation, so the recording is free. *)
let recorded_types : (Ast.location * int * recorded_type) list ref option ref =
  ref None

(* The configuration currently being validated (0 for a module without
   conditional compilation; bumped for each configuration {!Cond_explore}
   explores), tagging every recorded entry. *)
let sink_config = ref 0

(* Record [rt] at instruction span [loc], if the sink is active and [loc] is a
   real source span (not a synthesized / recovery placeholder). No rendering
   here — an ordinary validation pays nothing beyond the [!recorded_types]
   test. *)
let record loc rt =
  match (!recorded_types, loc) with
  | Some r, Some l when l.Ast.loc_start.Lexing.pos_cnum >= 0 ->
      r := (l, !sink_config, rt) :: !r
  | _ -> ()

(* A named index with a zero-width span is one error recovery synthesized in
   place — the placeholder [$_] it inserts for a missing index ([(call)] repaired
   to [(call $_)]). A diagnostic anchored solely to it (the placeholder name
   being unbound) is suppressed: the "Missing index" syntax error already stands
   there. The check is narrow on purpose — a real [$id] spans at least two
   characters, and an {e omitted} index that defaults to [0] (e.g. the implicit
   memory of [memory.copy]) is a [Num], whose unbound-ness is a genuine error —
   so only the synthetic named placeholder is caught. *)
let is_recovery_placeholder (idx : Ast.Text.idx) =
  match idx.Ast.desc with
  | Ast.Text.Id _ ->
      idx.info.Ast.loc_start.Lexing.pos_cnum
      = idx.info.Ast.loc_end.Lexing.pos_cnum
  | Ast.Text.Num _ -> false

(* Reconstruct a source type from an interned one. Used as the source type of a
   pushed value when no truer reference is available, so every concrete stack
   value carries a source type (as on the Wax side, where an inferred type
   bundles both forms). Only abstract heap types are reconstructed this way: a
   concrete [Type] reference always carries a truer source from its declaration. *)
let source_of_heaptype (h : heaptype) : Ast.Text.heaptype =
  match h with
  | Func -> Func
  | NoFunc -> NoFunc
  | Exn -> Exn
  | NoExn -> NoExn
  | Cont -> Cont
  | NoCont -> NoCont
  | Extern -> Extern
  | NoExtern -> NoExtern
  | Any -> Any
  | Eq -> Eq
  | I31 -> I31
  | Struct -> Struct
  | Array -> Array
  | None_ -> None_
  | Type _ | Exact _ -> assert false

let source_of_valtype (ty : valtype) : source_type =
  Plain
    (match ty with
    | I32 -> I32
    | I64 -> I64
    | F32 -> F32
    | F64 -> F64
    | V128 -> V128
    | Ref { nullable; typ } -> Ref { nullable; typ = source_of_heaptype typ })

(*** Diagnostics ***)

let loc_first_char (loc : Ast.location) =
  let loc_start = loc.Ast.loc_start in
  {
    loc with
    loc_end = { loc_start with Lexing.pos_cnum = loc_start.Lexing.pos_cnum + 1 };
  }

let loc_last_char (loc : Ast.location) =
  let loc_end = loc.Ast.loc_end in
  {
    loc with
    Ast.loc_start =
      { loc_end with Lexing.pos_cnum = loc_end.Lexing.pos_cnum - 1 };
  }

module Error = struct
  open Wax_utils
  module D = Diagnostic

  (* Message-building combinators (see {!Wax_utils.Message}). Prose is [text],
     joined with [++] (soft, wrap-point space) or [^^] (no space). An emphasized
     atom — [styp]/[sources] a source type, [index]/[ident] an identifier, [str]
     a string literal, [num] a numeric literal — is coloured when the theme is
     coloured and quoted ['…'] when it is not. Its text is produced by the
     [Format] [print_*] printers above and emitted as one styled atom. *)
  let text = Message.text
  let kw = Message.code
  let ( ++ ) = Message.( ++ )
  let ( ^^ ) = Message.( ^^ )

  (* Render an AST fragment ([render], drawing into the styled printer) as one
     emphasized atom: coloured when the theme is coloured, wrapped in ['…'] when
     it is not. [style] is the atom's colour — forced over the whole fragment
     (via [with_style]) so a type reads as one unit rather than syntax-
     highlighting its parens/keywords/idents in separate role colours — and it
     also decides the quoting. *)
  let styled_atom style render =
    Message.raw (fun pp ->
        let p = pp.Styled_printer.printer in
        let quote = Colors.escape_sequence pp.Styled_printer.theme style = "" in
        if quote then Printer.string p "'";
        Styled_printer.with_style pp style (fun () -> render pp);
        if quote then Printer.string p "'")

  let styp source =
    styled_atom Colors.Type (fun pp -> print_source_type pp source)

  let index idx = styled_atom Colors.Identifier (fun pp -> print_index pp idx)
  let ident id = styled_atom Colors.Identifier (fun pp -> print_ident pp id)
  let str s = styled_atom Colors.String (fun pp -> print_string pp s)
  let num s = Message.styled Colors.Constant s

  let report context ~location ~severity ?warning ?universal ?hint ?related
      message =
    (* In error-recovery mode (see [Wax_utils.Parsing.parse_recover], used by the editor
       to validate a best-effort partial AST across syntax errors) the module's
       whole-module analyses are unreliable, so suppress every warning — the same
       policy the Wax typer applies in recovery. Errors still surface, so a real
       defect in an intact region shows; the few error {e cascades} a dropped or
       auto-closed construct triggers are suppressed at their own call sites (see
       [empty_stack]/[non_empty_stack]/[leftover_values]). *)
    match severity with
    | D.Warning when D.in_recovery context -> ()
    | _ ->
        D.report context ~location ~severity ?warning ?universal ?hint ?related
          ~message ()

  let did_you_mean = function
    | [] -> None
    | suggestions ->
        Some
          (text "Did you mean"
           ++ Message.enumerate ~conj:"or" (List.map Message.ident suggestions)
          ^^ text "?")

  (* A zero-width [Id] is a placeholder to suppress the cascade from — but only
     in error-recovery mode, where the parser inserts them. Outside recovery a
     zero-width [Id] instead marks a name synthesized by [Binary_to_text] (which
     uses [no_loc]); its unbound-index error is a genuine soundness finding on a
     malformed binary and must be reported, not swallowed. *)
  let suppress_placeholder context id =
    is_recovery_placeholder id && D.in_recovery context

  let unbound_label context ~location id lst =
    if suppress_placeholder context id then ()
    else
      report context ~location ~severity:Error ?hint:(did_you_mean lst)
        (text "Unknown label:" ++ index id ++ text "is not bound.")

  let unbound_index context ~location kind id lst =
    if suppress_placeholder context id then ()
    else
      report context ~location ~severity:Error ?hint:(did_you_mean lst)
        ((text "Unknown" ++ text kind)
        ^^ (text ": index" ++ index id ++ text "is not bound."))

  let packed_array_access context ~location =
    report context ~location ~severity:Error
      (text
         "This instruction cannot be used on packed arrays. Use array.get_s or \
          array.get_u to specify sign extension.")

  let unpacked_array_access context ~location =
    report context ~location ~severity:Error
      (text "This instruction is only valid for packed arrays. Use array.get.")

  let packed_struct_access context ~location =
    report context ~location ~severity:Error
      (text
         "This instruction cannot be used on packed fields. Use struct.get_s \
          or struct.get_u to specify sign extension.")

  let unpacked_struct_access context ~location =
    report context ~location ~severity:Error
      (text "This instruction is only valid for packed fields. Use struct.get.")

  (* The caret points at the instruction that {e produced} the value still on
     the stack, not at the one consuming it (whose location is [consumer]): the
     wording makes that explicit, and a secondary caret marks the use site. *)
  let instruction_type_mismatch context ~location ~consumer ~provided_source
      ~expected_source =
    (* Mark the use site with a secondary caret, but only when it is a distinct
       location that does not enclose the producer: an implicit function or
       block result spans the whole construct, so a caret there would just be
       noise around the precise one. *)
    let encloses outer inner =
      outer.Ast.loc_start.Lexing.pos_cnum <= inner.Ast.loc_start.Lexing.pos_cnum
      && inner.Ast.loc_end.Lexing.pos_cnum <= outer.Ast.loc_end.Lexing.pos_cnum
    in
    let related =
      match consumer with
      | Some loc
        when loc.Ast.loc_start.Lexing.pos_cnum >= 0
             && not (encloses loc location) ->
          [
            {
              Wax_utils.Diagnostic.location = loc;
              message = text "expected here";
            };
          ]
      | _ -> []
    in
    report context ~location ~severity:Error ~related
      (text "Type mismatch: this produces a value of type"
       ++ styp provided_source
      ^^ text "," ++ text "but type" ++ styp expected_source
         ++ text "is expected.")

  let expected_ref_type context ~location ~src_loc ~source =
    match src_loc with
    | None ->
        report context ~location ~severity:Error
          (text "Type mismatch: expected reference type but got type"
           ++ styp source
          ^^ text ".")
    | Some location ->
        report context ~location ~severity:Error
          (text
             "Type mismatch: this instruction should return a reference type \
              but has type"
           ++ styp source
          ^^ text ".")

  let table_type_mismatch context ~location ~source idx =
    report context ~location ~severity:Error
      (text "Type mismatch: the table"
       ++ index idx
       ++ text "should contain functions but its elements have type"
       ++ styp source
      ^^ text ".")

  let elem_segment_type_mismatch context ~location ~elem_source ~table_source =
    report context ~location ~severity:Error
      ((text "Type mismatch: the element segment has type" ++ styp elem_source)
      ^^ text ","
         ++ text "which is not a subtype of the table element type"
         ++ styp table_source
      ^^ text ".")

  let duplicate_local context ~location ~prev_loc name =
    report context ~location ~severity:Error
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "previously defined here";
          };
        ]
      (text "The local" ++ ident name ++ text "is already defined.")

  let type_mismatch context ~location ~provided_source ~expected_source =
    report context ~location ~severity:Error
      (text "Type mismatch: expecting type"
       ++ styp expected_source ++ text "but got type" ++ styp provided_source
      ^^ text ".")

  let br_cast_type_mismatch context ~location =
    report context ~location ~severity:Error
      (text
         "Type mismatch: the first type must be a supertype of the second one.")

  let br_on_non_null_no_ref context ~location =
    report context ~location ~severity:Error
      (text "Type mismatch:" ++ kw "br_on_non_null"
      ++ text
           "requires the target label to end in a reference type, but it has \
            no result types.")

  let select_type_mismatch context ~location ~loc1 ~source1 ~loc2 ~source2 =
    (* Point a caret at each branch value (when its push site is known),
       labelled with its type. A placeholder location uses a negative column;
       skip those, as in [locations]. *)
    let branch_label loc source =
      match loc with
      | Some loc when loc.Ast.loc_start.Lexing.pos_cnum >= 0 ->
          Some { Wax_utils.Diagnostic.location = loc; message = styp source }
      | _ -> None
    in
    let related =
      List.filter_map Fun.id
        [ branch_label loc1 source1; branch_label loc2 source2 ]
    in
    (* When both carets are shown they carry the types; otherwise name the two
       types in the message so they are not lost. *)
    let message =
      if List.length related = 2 then
        text "Type mismatch: both branches of a"
        ++ kw "select"
        ++ text "should have the same type."
      else
        text "Type mismatch: both branches of a"
        ++ kw "select"
        ++ text "should have the same type."
        ++ text "Here, they have type"
        ++ styp source1 ++ text "and" ++ styp source2
        ^^ text "."
    in
    report context ~location ~severity:Error ~related message

  (* The stack-shape mismatches ([empty_stack], [non_empty_stack],
     [leftover_values]) are the error cascades a partial AST triggers: an
     auto-closed body ([(func (i32.const 1)] at EOF) or a dropped instruction
     leaves the operand stack the wrong height through no fault of the intact
     code. Suppress them in recovery mode — the analogue of the Wax typer
     dropping leftover Error-typed values under [with_empty_stack]. *)
  let empty_stack context ~location =
    if D.in_recovery context then ()
    else
      report context ~location ~severity:Error
        (text "Type mismatch: the stack is empty (a value is missing).")

  (* The counted variant of [empty_stack], for a pop whose caller knows how
     many values the construct takes ([pop_args]): say how many were expected
     and how many were there (the Wax typer's [short_stack]). *)
  let short_stack context kind ~location ~actual ~expected =
    let values =
      match kind with `Input -> "argument(s)" | `Output -> "returned value(s)"
    in
    if D.in_recovery context then ()
    else
      report context ~location ~severity:Error
        (text "Type mismatch: expecting"
         ++ Message.int expected ++ text values
         ++ text "from the stack, but there are"
         ++ Message.int actual
        ^^ text ".")

  let non_empty_stack context ~location render =
    if D.in_recovery context then ()
    else
      report context ~location:(loc_last_char location) ~severity:Error
        (text "Type mismatch: unexpected values left on the stack:"
        ^^ Message.raw render)

  (* Report the values still on the stack by pointing a caret at each of them.
     [location] carries the topmost value; [related] the others. *)
  let leftover_values context ~location ~related =
    if D.in_recovery context then ()
    else
      report context ~location ~severity:Error ~related
        (text
           (if related = [] then
              "Type mismatch: this value is left on the stack."
            else "Type mismatch: these values are left on the stack."))

  (* Print a list of source types, [\[a b c\]]. *)
  let print_sources pp source =
    sp_box pp (fun () ->
        sp_punct pp "[";
        Array.iteri
          (fun i s ->
            if i > 0 then sp_space pp;
            print_source_type pp s)
          source;
        sp_punct pp "]")

  let sources source =
    styled_atom Colors.Type (fun pp -> print_sources pp source)

  let argument_count_mismatch context ~location ~descr ~provided_source
      ~expected_source =
    report context ~location ~severity:Error
      (text "Type mismatch:" ++ text descr ++ text "provides type"
     ++ sources provided_source ++ text "but type" ++ sources expected_source
     ++ text "was expected.")

  (* [nth] names the mismatching position when several values are compared
     ([None] for a single value, where it would only be noise). *)
  let argument_type_mismatch context ~location ~descr ~nth ~provided_source
      ~expected_source =
    let position =
      match nth with
      | Some n -> text "for value" ++ Message.int n
      | None -> Message.empty
    in
    report context ~location ~severity:Error
      (text "Type mismatch:" ++ text descr ++ text "provides type"
     ++ styp provided_source ++ position ++ text "but type"
     ++ styp expected_source ++ text "was expected.")

  let branch_parameter_count_mismatch context ~location ~default_loc label len
      label' len' =
    report context ~location ~severity:Error
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = default_loc;
            message = text "default branch target here";
          };
        ]
      (text "Type mismatch: the default branch target"
      ++ index label ++ text "expects" ++ Message.int len
      ++ text "parameters, while branch target"
      ++ index label' ++ text "expects" ++ Message.int len'
      ++ text "parameters.")

  let memory_offset_too_large context ~location max_offset =
    report context ~location ~severity:Error
      (text "The memory offset should be less than"
       ++ num (Printf.sprintf "0x%Lx" (Uint64.to_int64 max_offset))
      ^^ text ".")

  let memory_align_too_large context ~location natural =
    report context ~location ~severity:Error
      (text "The memory alignment is larger than the natural alignment"
       ++ Message.int natural
      ^^ text ".")

  let bad_memory_align context ~location =
    report context ~location ~severity:Error
      (text "The memory alignment should be a power of two.")

  let atomic_alignment context ~location natural =
    report context ~location ~severity:Error
      (text "The alignment of an atomic access must be its natural alignment"
       ++ Message.int natural
      ^^ text ".")

  let invalid_lane_index context ~location max_lane =
    report context ~location ~severity:Error
      ((text "The lane index should be less than" ++ Message.int max_lane)
      ^^ text ".")

  (* The definition's parameters/results are passed as source types (from its
     declaration), not reconstructed from the resolved [functype] via
     [source_of_valtype]: a definition may name a concrete reference ([(ref
     $t)]/[(ref (exact $t))]), which [source_of_heaptype] cannot rebuild. *)
  let inline_function_type_mismatch context ~location ~params ~results =
    report context ~location ~severity:Error
      (text
         "The inline function type does not match the type definition, whose \
          parameters are"
       ++ sources params ++ text "and results are" ++ sources results
      ^^ text ".")

  let constant_expression_required context ~location =
    report context ~location ~severity:Error
      (text "Only constant expressions are allowed here.")

  let immutable_global context ~location idx =
    report context ~location ~severity:Error
      (text "The global" ++ index idx ++ text "should be mutable.")

  let limit_too_large context ~location kind max =
    report context ~location ~severity:Error
      (text "The" ++ text kind
       ++ text "size is too large. It should be less than"
       ++ num (Printf.sprintf "0x%Lx" (Uint64.to_int64 max))
      ^^ text ".")

  let invalid_page_size context ~location =
    report context ~location ~severity:Error
      (text "The custom page size must be 1 or 65536.")

  let branch_hint_invalid_target context ~location =
    report context ~location ~severity:Error
      (text
         "A branch hint may only prefix a conditional branch (if, br_if, or \
          br_on_*).")

  let instr_freq_invalid_target context ~location =
    report context ~location ~severity:Error
      (text
         "An instruction-frequency hint may only prefix a call or a control \
          instruction.")

  let call_targets_invalid_target context ~location =
    report context ~location ~severity:Error
      (text
         "A call-target hint may only prefix an indirect call (call_ref or \
          call_indirect).")

  let call_targets_over_100 context ~location ~total =
    report context ~location ~severity:Error
      ((text "The call-target frequencies add up to"
        ++ num (string_of_int total)
       ^^ text "%, more than 100%.")
      ++ text
           "A shortfall is how the hint says other, unlisted targets take the \
            remainder.")

  let shared_memory_without_max context ~location =
    report context ~location ~severity:Error
      (text "A shared memory must have a maximum size.")

  let limit_mismatch context ~location kind =
    report context ~location ~severity:Error
      (text "The" ++ text kind
      ++ text "maximum size should be larger than the minimal size.")

  let duplicated_export context ~location ~prev_loc name =
    report context ~location ~severity:Error
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "previously exported here";
          };
        ]
      ((text "There is already an export of name" ++ str name) ^^ text ".")

  let import_after_definition context ~location ~prev_loc kind =
    report context ~location ~severity:Error
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "first definition here";
          };
        ]
      (text "This import is after a" ++ text kind ++ text "definition.")

  let supertype_mismatch context ~location =
    report context ~location ~severity:Error
      (text "The supertype is not of the same kind as this type.")

  let invalid_subtype context ~location =
    report context ~location ~severity:Error
      (text "This type is not a valid subtype of its declared supertype.")

  let descriptor_outside_rec_group context ~location ~described =
    report context ~location ~severity:Error
      (text "The"
      ++ text (if described then "described" else "descriptor")
      ++ text "type must be in the same recursion group.")

  let descriptor_not_reciprocal context ~location ~described =
    report context ~location ~severity:Error
      (text
         (if described then
            "This descriptor does not describe the type it is attached to."
          else "The descriptor of this type does not describe it back."))

  let forward_use_of_described context ~location =
    report context ~location ~severity:Error
      (text "A described type must be declared before its descriptor.")

  let descriptor_finality_mismatch context ~location =
    report context ~location ~severity:Error
      ((text "A type and its descriptor must both be" ++ kw "final")
      ^^ text ", or neither.")

  let descriptor_not_struct context ~location ~described =
    report context ~location ~severity:Error
      (text "A"
      ++ text (if described then "described" else "descriptor")
      ++ text "type must be a struct type.")

  let not_function_type context ~location =
    report context ~location ~severity:Error
      (text "This should be a function type.")

  let exception_tag_with_results context ~location =
    report context ~location ~severity:Error
      (text "The type of an exception tag must have no results.")

  let select_result_count context ~location =
    report context ~location ~severity:Error
      (text "A typed" ++ kw "select"
      ++ text "must be annotated with exactly one result type.")

  let non_nullable_table_type context ~location =
    report context ~location ~severity:Error
      (text
         "Type mismatch: the type of the elements of this table must be \
          nullable.")

  let uninitialized_local context ~location idx =
    report context ~location ~severity:Error
      (text "The local variable" ++ index idx
      ++ text "has not been initialized.")

  (* A local that is declared but never read. Prefix its name with [_] to
     silence the warning. *)
  let unused_local context ~location name =
    report context ~location ~severity:Warning ~warning:Warning.Unused_local
      ~universal:true
      (match name with
      | Some id ->
          text "The local variable" ++ ident id ++ text "is never used."
      | None -> text "This local is never used.")

  (* A module field (a function, global, memory, table, tag, or a passive
     data/element segment) defined but never referenced, exported, or used as the
     start function. Prefix its name with [_] to silence the warning. *)
  let unused_field context ~location kind name =
    report context ~location ~severity:Warning ~warning:Warning.Unused_field
      ~universal:true
      (match name with
      | Some id -> text "The" ++ text kind ++ ident id ++ text "is never used."
      | None -> text "This" ++ text kind ++ text "is never used.")

  (* An imported field never referenced, exported, or used as the start function.
     Prefix its name with [_] to silence the warning. *)
  let unused_import context ~location kind name =
    report context ~location ~severity:Warning ~warning:Warning.Unused_import
      ~universal:true
      (match name with
      | Some id ->
          text "The imported" ++ text kind ++ ident id ++ text "is never used."
      | None -> text "This imported" ++ text kind ++ text "is never used.")

  (* A block label declared but never branched to. Prefix its name with [_] to
     silence the warning. *)
  let unused_label context ~location name =
    report context ~location ~severity:Warning ~warning:Warning.Unused_label
      ~universal:true
      (text "The label" ++ ident name ++ text "is never used.")

  (* A module-defined global declared [mut] but never the target of a
     [global.set]. An import (whose mutability is part of the linking contract)
     and an exported global (which the host may assign) are exempt, as is a name
     starting with [_]. *)
  let unnecessary_mut context ~location name =
    report context ~location ~severity:Warning ~warning:Warning.Unnecessary_mut
      ~universal:true
      ~hint:(text "Drop the 'mut' to declare it immutable.")
      (match name with
      | Some id ->
          text "The global" ++ ident id
          ++ text "is mutable but is never assigned."
      | None -> text "This global is mutable but is never assigned.")

  (* --- The correctness lint tier (shared with the Wax typer; same warnings and
     wording). Emitted while validating a WAT/WASM function body. --- *)

  let warn_lint context ~location ?hint ?related warning message =
    report context ~location ~severity:Warning ~warning ~universal:true ?hint
      ?related message

  let confusable_unicode context ~location u =
    warn_lint context ~location Warning.Confusable_unicode
      (text
         (Printf.sprintf
            "This string contains a bidirectional control character (U+%04X) \
             that can make the displayed text read differently than it runs."
            (Uchar.to_int u)))

  (* [count] is the shift count as an unsigned 64-bit value (an i32/i64 const
     with the high bit set is a large positive count, not a negative one), so
     print and reduce it unsigned — matching the Wax typer's [shift_overflow]. *)
  let shift_overflow context ~location ~width count =
    warn_lint context ~location Warning.Shift_overflow
      ~hint:
        ((text "Wasm masks the count modulo" ++ Message.int width)
        ^^ text "," ++ text "shifting by"
           ++ Message.uint64 (Int64.unsigned_rem count (Int64.of_int width))
           ++ text "instead.")
      (text "The shift count" ++ Message.uint64 count
       ++ text "is at least the operand width ("
      ^^ Message.int width ^^ text " bits).")

  let division_by_zero context ~location =
    warn_lint context ~location Warning.Constant_trap
      (text "This integer division or remainder by zero always traps.")

  let conversion_out_of_range context ~location =
    warn_lint context ~location Warning.Constant_trap
      (text
         "This conversion always traps: the constant is out of the target \
          type's range.")

  let tautological_comparison context ~location ~value =
    warn_lint context ~location Warning.Tautological_comparison
      ((text "This comparison is always" ++ Message.bool value) ^^ text ".")

  let constant_condition context ~location ~value =
    warn_lint context ~location Warning.Constant_condition
      ((text "This condition is always" ++ Message.bool value) ^^ text ".")

  let unused_result context ~location =
    warn_lint context ~location Warning.Unused_result
      (text
         "The result of this expression is discarded, and computing it has no \
          effect.")

  let dead_code context ~location ~related =
    warn_lint context ~location ~related Warning.Dead_code
      (text "This code is unreachable.")

  let redundant_operation context ~location message =
    warn_lint context ~location Warning.Redundant_operation message

  let cast_always_fails context ~location ~is_test =
    warn_lint context ~location Warning.Cast_always_fails
      (text
         (if is_test then
            "This type test is always false: the value can never have this \
             type."
          else "This cast always traps: the value can never have this type."))

  let redundant_cast context ~location ~is_test =
    warn_lint context ~location Warning.Redundant_operation
      (text
         (if is_test then
            "This type test is always true: the value already has this type."
          else "This cast is redundant: the value already has this type."))

  (* A trapping or effectful operation among the value operands of a [select],
     which evaluates both operands unconditionally. Mirrors the Wax typer's
     [eager-select] lint (a Wax [?:] compiles to a [select]). [select] points at
     the [select] instruction. *)
  let eager_select context ~location ~select =
    warn_lint context ~location Warning.Eager_select
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = select;
            message =
              text "This" ++ kw "select"
              ++ text "evaluates both of its operands.";
          };
        ]
      (text
         "This operation is evaluated even when the condition selects the \
          other operand.")

  let index_already_bound context ~location ~prev_loc kind index =
    report context ~location ~severity:Error
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "previously bound here";
          };
        ]
      (text "The" ++ text kind ++ text "index" ++ ident index.Ast.desc
     ++ text "is already bound.")

  let expected_func_type context ~location idx =
    report context ~location ~severity:Error
      (text "Type" ++ index idx ++ text "should be a function type.")

  let expected_struct_type context ~location idx =
    report context ~location ~severity:Error
      (text "Type" ++ index idx ++ text "should be a struct type.")

  let expected_array_type context ~location idx =
    report context ~location ~severity:Error
      (text "Type" ++ index idx ++ text "should be an array type.")

  let expected_cont_type context ~location idx =
    report context ~location ~severity:Error
      (text "Type" ++ index idx ++ text "should be a continuation type.")

  let stack_switching_type_mismatch context ~location ~descr =
    report context ~location ~severity:Error
      ((text "Type mismatch in this stack switching instruction:" ++ text descr)
      ^^ text ".")

  let invalid_cast_type context ~location =
    report context ~location ~severity:Error
      (text "Continuation types cannot be used in a cast instruction.")

  let type_without_descriptor context ~location =
    report context ~location ~severity:Error
      (text "This descriptor instruction requires a type that has a descriptor.")

  let feature_disabled context ~location feature =
    report context ~location ~severity:Error
      (text "This uses the"
       ++ text (Wax_utils.Feature.name feature)
       ++ text "feature, which is not enabled; pass --feature"
       ++ text (Wax_utils.Feature.name feature)
      ^^ text ".")

  let unknown_feature context ~location name =
    report context ~location ~severity:Error
      ((text "Unknown feature" ++ Message.code name)
      ^^ text ". Known features:"
         ++ text
              (String.concat ", "
                 (List.map Wax_utils.Feature.name Wax_utils.Feature.all))
      ^^ text ".")

  let feature_conflict context ~location feature =
    report context ~location ~severity:Error
      (text "This module requires the"
       ++ text (Wax_utils.Feature.name feature)
       ++ text "feature, which is disabled on the command line; drop --feature"
       ++ text (Wax_utils.Feature.name feature ^ "=off")
      ^^ text ".")

  let descriptor_allocation_required context ~location =
    report context ~location ~severity:Error
      (text
         "A type with a descriptor must be allocated with a descriptor \
          (struct.new_desc / struct.new_default_desc).")

  (* [src_loc], when known, is the offending operand's push location; the
     report is anchored there (like [expected_ref_type]) so two failing
     operands of one instruction point at themselves, not both at the
     instruction. *)
  let expected_number_or_vec context ~location ~src_loc ~source =
    match src_loc with
    | None ->
        report context ~location ~severity:Error
          (text "Type mismatch: expecting a numeric or vector type but got type"
           ++ styp source
          ^^ text ".")
    | Some location ->
        report context ~location ~severity:Error
          ((text "Type mismatch: this produces a value of type" ++ styp source)
          ^^ text ", but a numeric or vector type is expected.")

  let immutable context ~location what =
    report context ~location ~severity:Error
      (text "This" ++ text what ++ text "is immutable.")

  let not_defaultable context ~location =
    report context ~location ~severity:Error
      (text "This type has no default value for all its fields.")

  let field_index_out_of_bounds context ~location ~index ~count =
    report context ~location ~severity:Error
      (text "The field index" ++ Message.int index
      ++ text "is out of bounds: the structure has"
      ++ Message.int count ++ text "field(s).")

  let unknown_field context ~location =
    report context ~location ~severity:Error (text "There is no such field.")

  let numeric_array_required context ~location =
    report context ~location ~severity:Error
      (text "This operation requires an array of numeric elements.")

  let string_array_required context ~location =
    report context ~location ~severity:Error
      (text "A string can only build an i8 or i16 array.")

  let string_not_unicode context ~location =
    report context ~location ~severity:Error
      (text "A string building an i16 array must be a valid Unicode string.")

  let incompatible_array_element context ~location =
    report context ~location ~severity:Error
      (text "The array element type is incompatible.")

  let ref_func_inaccessible context ~location idx =
    report context ~location ~severity:Error
      ((text "The function" ++ index idx
        ++ text "is not declared as referenceable ("
       ^^ kw "ref.func")
      ^^ text ").")

  let non_constant_global context ~location idx =
    report context ~location ~severity:Error
      (text "Only an immutable global may be used in a constant expression:"
       ++ index idx
      ^^ text ".")

  let start_function_signature context ~location =
    report context ~location ~severity:Error
      (text "The start function must have no parameters and no results.")

  let multiple_start context ~location ~prev_loc =
    report context ~location ~severity:Error
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "other start function here";
          };
        ]
      (text "A module can have at most one start function.")
end

let print_instr i = Wax_utils.Printer.run_err (fun p -> Output.instr p i)

(* A diagnostics context that drops everything reported to it. Passed to a
   pre-pass that resolves references the validating pass resolves (and reports)
   again, so a broken reference is diagnosed once, by the pass that owns it. *)
let muted d = Wax_utils.Diagnostic.collector ~parent:d ()

(*** Symbol tables (sequences) ***)

module Sequence = struct
  (* A poisoned entry ([None] in [index_mapping]) claims an index for a
     definition whose own resolution failed: [last_index] still advances, so
     later definitions keep their positions and numeric references stay aligned,
     but [get]/[find] resolve it to [None] silently (no unbound-index error —
     the real error was reported at the definition site). *)
  type 'a t = {
    name : string;
    index_mapping : (int, 'a option) Hashtbl.t;
    label_mapping : (string, int) Hashtbl.t;
    mutable last_index : int;
  }

  let make name =
    {
      name;
      index_mapping = Hashtbl.create 16;
      label_mapping = Hashtbl.create 16;
      last_index = 0;
    }

  (* The index the next [register] will assign (the current length). *)
  let next_index seq = seq.last_index

  let register seq id v =
    let idx = seq.last_index in
    seq.last_index <- seq.last_index + 1;
    Hashtbl.add seq.index_mapping idx (Some v);
    Option.iter (fun id -> Hashtbl.add seq.label_mapping id.Ast.desc idx) id

  (* Claim the next index for a definition whose own resolution failed, so later
     definitions keep their positions. The entry is poisoned (see the type). *)
  let register_failed seq id =
    let idx = seq.last_index in
    seq.last_index <- seq.last_index + 1;
    Hashtbl.add seq.index_mapping idx None;
    Option.iter (fun id -> Hashtbl.add seq.label_mapping id.Ast.desc idx) id

  let get d seq (idx : Ast.Text.idx) =
    match
      match idx.desc with
      | Num n -> Hashtbl.find_opt seq.index_mapping (Uint32.to_int n)
      | Id id ->
          Option.bind
            (Hashtbl.find_opt seq.label_mapping id)
            (Hashtbl.find_opt seq.index_mapping)
    with
    | Some entry ->
        (* [Some v] is a real definition; [None] a poisoned entry, resolved
           silently. *)
        entry
    | None ->
        let lst =
          match idx.desc with
          | Num _ -> []
          | Id id ->
              Wax_utils.Spell_check.f
                (fun f -> Hashtbl.iter (fun id' _ -> f id') seq.label_mapping)
                id
        in
        Error.unbound_index d ~location:idx.info seq.name idx lst;
        None

  let get_index seq (idx : Ast.Text.idx) =
    match idx.desc with
    | Num n -> Uint32.to_int n
    | Id id -> (
        try Hashtbl.find seq.label_mapping id
        with Not_found -> assert false (* Should not happen *))

  (* Resolve to an index without reporting or raising when a name is unbound —
     for callers that only want to note a resolvable reference and leave the
     error reporting to the pass that validates the reference. *)
  let get_index_opt seq (idx : Ast.Text.idx) =
    match idx.desc with
    | Num n -> Some (Uint32.to_int n)
    | Id id -> Hashtbl.find_opt seq.label_mapping id

  (* Resolve to the value without reporting when the reference is unbound (or is
     a poisoned entry) — a silent [get], for the same kind of caller as
     [get_index_opt]. *)
  let find seq (idx : Ast.Text.idx) =
    match idx.desc with
    | Num n ->
        Option.join (Hashtbl.find_opt seq.index_mapping (Uint32.to_int n))
    | Id id ->
        Option.join
          (Option.bind
             (Hashtbl.find_opt seq.label_mapping id)
             (Hashtbl.find_opt seq.index_mapping))
end

(*** Types and the type context ***)

(* Where the reference currently being resolved is made from, for the reachability
   analysis behind [unused-field]. Lives on the type context (which every
   resolution point can reach) and is read for every index space, not just types.

   [Root] is a module-level context — an export, the start function, an import
   declaration, a global or table initializer, a segment — which runs, or is
   callable, whatever the bodies do. [Ignored] suppresses recording, for a
   resolution that is not a source reference at all: [check_type_definitions]
   sweeps every type index to check its own well-formedness, and marking those
   would make every type look used. *)
type origin =
  | Root
  | From_function of int
  | From_type of int  (** a type definition's own components *)
  | Ignored

(* A source type reference, as written. Kept unresolved (rather than as a
   canonical index) because deduplication makes canonical indices non-injective:
   two structurally equal named types share one, so a reference to either would
   mark both used. [unused_fields] maps these back to definition indices through
   [type_defs]. *)
type type_ref = By_index of int | By_name of string

type type_context = {
  types : Types.t;
  mutable last_index : int;
  (* Keyed by a source type reference (numeric index / name): the resolved
     global index, a struct's field-name-to-position map, and the source
     composite type. The last lets an error name a component (a struct field,
     an array element, a function result) as the source wrote it; keying by the
     reference (rather than the deduplicated global index) keeps it injective,
     so [$a] is named with [$a] even when a structurally-equal [$b] shares its
     global index. *)
  (* The fourth component is the source subtype definition — kept, keyed by the
     (injective) source reference so hover on a type identifier shows the type
     as written; [None] for a synthesized (implicit) function type, which has no
     source. *)
  index_mapping :
    ( Uint32.t,
      Types.ref_index
      * (string * int) list
      * Ast.Text.comptype
      * (Ast.Text.name option * Ast.Text.subtype, Ast.location) Ast.annotated
        option )
    Hashtbl.t;
  label_mapping :
    ( string,
      Types.ref_index
      * (string * int) list
      * Ast.Text.comptype
      * (Ast.Text.name option * Ast.Text.subtype, Ast.location) Ast.annotated
        option )
    Hashtbl.t;
  (* Text indices / names of poisoned type definitions: a rec group whose own
     resolution failed still advances [last_index] (so later numeric type
     references stay aligned) but registers no mapping. These sets let
     [get_type_info] resolve such a reference to [None] silently instead of
     reporting "unknown type" again — the real error was reported at the
     definition. The analogue of {!Sequence}'s poisoned entries. *)
  poisoned_index : (Uint32.t, unit) Hashtbl.t;
  poisoned_label : (string, unit) Hashtbl.t;
  (* For each type definition, keyed by its text-level index: its source index
     node (its name when it has one, else its numeric index, carrying the
     definition's location), and — for a continuation type — the source
     reference to the wrapped type. Keying by text index (rather than the
     resolved, deduplicated global index) keeps the mapping injective, so a
     check on a type is reported at the exact definition and names types as they
     appear in the source. *)
  type_defs : (int, Ast.Text.idx * Ast.Text.idx option) Hashtbl.t;
  (* For a type carrying a [descriptor] clause, keyed by its resolved global
     index: the source reference to its descriptor type. The descriptor
     instructions derive the descriptor type from the described one, so this
     recovers the descriptor's source name for error rendering (there is no
     immediate to name it by). Deduplicated types share a descriptor, so keying
     by the global index is unambiguous. *)
  descriptor_source : (Types.Id.t, Ast.Text.idx) Hashtbl.t;
  (* The enabled optional features / proposals, and which are used. *)
  features : Wax_utils.Feature.set;
  (* Where references are currently being made from (see {!origin}), and every
     type reference seen so far. Both feed the [unused-field] reachability
     analysis; nothing is recorded when the lint is off. A type reference is
     recorded here rather than in a [used_*] table because a type's liveness
     depends on the liveness of whatever names it, type definitions included. *)
  mutable origin : origin;
  mutable type_references : (origin * type_ref) list;
  (* References to a type by its *canonical* index rather than by a source name,
     which is how the implicit Wax string type is reached: [@string] interns
     [(array (mut i8))] structurally, so a module that also defines that type by
     name is deduplicated onto it and uses the definition without ever naming it.
     Resolved against every source definition sharing the canonical index — all
     of them, since deduplication makes that ambiguous and over-keeping is the
     safe direction. *)
  mutable canonical_type_references : (origin * Types.Id.t) list;
  (* Whether the [unused-field] analysis runs, so the recording above can be
     skipped entirely otherwise. Mirrors the module context's [warn_unused],
     which is not reachable from every resolution point. *)
  record_references : bool;
}

(* The source composite type a reference resolves to, named as the source wrote
   it (injective), or [None] for an unbound or sourceless reference. Does not
   report errors — callers that resolve the reference do. *)
let reference_comptype tc (idx : Ast.Text.idx) =
  let _, _, c, _ =
    match idx.desc with
    | Num x -> Hashtbl.find tc.index_mapping x
    | Id id -> Hashtbl.find tc.label_mapping id
  in
  c

(* The source function type a reference resolves to, when it names one. *)
let reference_functype tc idx =
  match reference_comptype tc idx with
  | Func ft -> ft
  | Struct _ | Array _ | Cont _ -> assert false

(* The source function type a [typeuse] denotes: the one named by its type
   reference, or its inline signature. Resolve the reference in preference to the
   inline signature, consistent with [typeuse] (which drives the corresponding
   [return_types]); for valid input the two agree, and preferring one uniformly
   keeps their arities in step when a malformed module gives both a [(type $i)]
   and a disagreeing inline signature. *)
let typeuse_functype tc (tu_idx, tu_sign) =
  match (tu_idx, tu_sign) with
  | Some idx, _ -> reference_functype tc idx
  | None, Some ft -> ft
  | _ -> assert false

(* Per-element source types for a source function type's params and results, to
   pass straight to [pop_args]/[push_results]'s [~source]. *)
let functype_sources ({ params; results } : Ast.Text.functype) =
  ( Array.map (fun p -> Plain (snd p.Ast.desc)) params,
    Array.map (fun v -> Plain v) results )

(* The source function type that the continuation type named by [idx] wraps. *)
let cont_source_functype tc idx =
  match reference_comptype tc idx with
  | Cont r -> reference_functype tc r
  | _ -> assert false

let get_type_info d ctx (idx : Ast.Text.idx) =
  let poisoned =
    match idx.desc with
    | Num x -> Hashtbl.mem ctx.poisoned_index x
    | Id id -> Hashtbl.mem ctx.poisoned_label id
  in
  let result =
    if poisoned then (* Silently: the definition site already reported. *) None
    else
      try
        match idx.desc with
        | Num x -> Some (Hashtbl.find ctx.index_mapping x)
        | Id id -> Some (Hashtbl.find ctx.label_mapping id)
      with Not_found ->
        let lst =
          match idx.desc with
          | Num _ -> []
          | Id id ->
              Wax_utils.Spell_check.f
                (fun f -> Hashtbl.iter (fun id' _ -> f id') ctx.label_mapping)
                id
        in
        Error.unbound_index d ~location:idx.info "type" idx lst;
        None
  in
  (* The single resolution point for every type reference — a typeuse, a named
     reference type wherever one may appear, a supertype or descriptor clause, an
     instruction's type immediate — so this is where one is recorded for the
     [unused-field] analysis. Resolution failures are recorded too, harmlessly:
     they name no definition. *)
  if ctx.record_references && ctx.origin <> Ignored then
    ctx.type_references <-
      ( ctx.origin,
        match idx.desc with
        | Num x -> By_index (Uint32.to_int x)
        | Id id -> By_name id )
      :: ctx.type_references;
  (* Record the referenced type's source definition, so hover over the type
     identifier shows its subtype. Guarded on the sink, so an ordinary
     validation pays nothing. *)
  (match (!recorded_types, result) with
  | Some _, Some (_, _, _, Some e) -> record (Some idx.info) (Subtype e)
  | _ -> ());
  result

(* The type context in force during the current body validation, so [push] can
   resolve a pushed value's named reference type to the type's definition for
   go-to-type-definition. Set (editor mode only) by [validate_configuration];
   like [recorded_types] it avoids threading through the push chokepoints. *)
let sink_type_context : type_context option ref = ref None

(* The source subtype entry a type reference resolves to (its definition),
   without reporting or recording — a silent [get_type_info]. *)
let lookup_subtype_entry tc (idx : Ast.Text.idx) =
  match
    match idx.desc with
    | Num x -> Hashtbl.find_opt tc.index_mapping x
    | Id id -> Hashtbl.find_opt tc.label_mapping id
  with
  | Some (_, _, _, e) -> e
  | None -> None

(* The source [comptype] a type reference resolves to. Unlike the subtype entry
   above, the source comptype is recorded for *every* mapped type, synthesized
   ones included, so a resolved index always has one. *)
let lookup_source_comptype tc (idx : Ast.Text.idx) =
  match
    match idx.desc with
    | Num x -> Hashtbl.find_opt tc.index_mapping x
    | Id id -> Hashtbl.find_opt tc.label_mapping id
  with
  | Some (_, _, ct, _) -> Some ct
  | None -> None

(* If [source] is a value of a named reference type, record its type's
   definition span at [loc] for go-to-type-definition. *)
let record_value_type_def loc source =
  match (!recorded_types, loc, !sink_type_context) with
  | Some r, Some l, Some tc when l.Ast.loc_start.Lexing.pos_cnum >= 0 -> (
      match source with
      | Plain (Ast.Text.Ref { typ = Type idx | Exact idx; _ }) -> (
          match lookup_subtype_entry tc idx with
          | Some e ->
              let def =
                match fst e.Ast.desc with
                | Some (n : Ast.Text.name) -> n.Ast.info
                | None -> e.Ast.info
              in
              r := (l, !sink_config, Value_type def) :: !r
          | None -> ())
      | _ -> ())
  | _ -> ()

(* Resolve a source type reference to how it should appear inside a rec group
   being registered: [Def id] for an already-defined type, [Rec pos] for a member
   of the group currently under construction. This is what the type-definition
   builders below produce. *)
let resolve_type_ref d ctx idx =
  let+@ r, _, _, _ = get_type_info d ctx idx in
  r

(* The canonical index of an already-defined type. A [Rec] would mean referring
   to a group still under construction, which never happens outside the
   type-definition builders. *)
let def_id : Types.ref_index -> Types.Id.t = function
  | Def id -> id
  | Rec _ -> assert false

(* Resolve a source type reference to its canonical index, for the many contexts
   that consult an *already-defined* type (function/cont/struct lookups, casts,
   …). *)
let resolve_type_index d ctx idx =
  let+@ r = resolve_type_ref d ctx idx in
  def_id r

(* Record that [feature] is used and, if it is not enabled, report it at
   [location]. Validation continues either way (the construct is still typed,
   for error recovery). *)
let require_feature d (ctx : type_context) ~location feature =
  Wax_utils.Feature.mark_used ctx.features feature;
  if not (Wax_utils.Feature.is_enabled ctx.features feature) then
    Error.feature_disabled d ~location feature

let heaptype d ctx (h : Ast.Text.heaptype) : heaptype option =
  match h with
  | Func -> Some Func
  | NoFunc -> Some NoFunc
  | Exn -> Some Exn
  | NoExn -> Some NoExn
  | Cont -> Some Cont
  | NoCont -> Some NoCont
  | Extern -> Some Extern
  | NoExtern -> Some NoExtern
  | Any -> Some Any
  | Eq -> Some Eq
  | I31 -> Some I31
  | Struct -> Some Struct
  | Array -> Some Array
  | None_ -> Some None_
  | Type idx ->
      let+@ ty = resolve_type_index d ctx idx in
      Type ty
  | Exact idx ->
      require_feature d ctx ~location:idx.info
        Wax_utils.Feature.Custom_descriptors;
      let+@ ty = resolve_type_index d ctx idx in
      Exact ty

let reftype d ctx { Ast.Text.nullable; typ } =
  let+@ typ = heaptype d ctx typ in
  { nullable; typ }

let valtype d ctx (ty : Ast.Text.valtype) =
  match ty with
  | I32 -> Some I32
  | I64 -> Some I64
  | F32 -> Some F32
  | F64 -> Some F64
  | V128 -> Some V128
  | Ref r ->
      let+@ ty = reftype d ctx r in
      Ref ty

let array_map_opt f arr =
  let exception Short_circuit in
  try
    let result =
      Array.init (Array.length arr) (fun i ->
          match f arr.(i) with Some v -> v | None -> raise Short_circuit)
    in
    Some result
  with Short_circuit -> None

let array_mapi_opt f arr =
  let exception Short_circuit in
  try
    let result =
      Array.init (Array.length arr) (fun i ->
          match f i arr.(i) with Some v -> v | None -> raise Short_circuit)
    in
    Some result
  with Short_circuit -> None

let functype d ctx { Ast.Text.params; results } =
  let*@ params =
    array_map_opt (fun p -> valtype d ctx (snd p.Ast.desc)) params
  in
  let+@ results = array_map_opt (fun ty -> valtype d ctx ty) results in
  { params; results }

let muttype f d ctx { mut; typ } =
  let+@ typ = f d ctx typ in
  { mut; typ }

let tabletype d ctx ({ limits; reftype = typ } : Ast.Text.tabletype) =
  let+@ reftype = reftype d ctx typ in
  { Types.Internal.limits = limits.desc; reftype }

let globaltype d ctx ty = muttype valtype d ctx ty

(* Type-definition builders. These produce the *normalized* representation
   ([Types.Normalized]) that {!Types.add_rectype} takes: a reference to a member
   of the group being defined is [Rec pos], anything else is [Def id]. They are
   deliberately separate from the [Internal]-producing builders above, which
   serve instruction checking where every reference is already defined. *)
let n_heaptype d ctx (h : Ast.Text.heaptype) : Nz.heaptype option =
  match h with
  | Func -> Some Nz.Func
  | NoFunc -> Some Nz.NoFunc
  | Exn -> Some Nz.Exn
  | NoExn -> Some Nz.NoExn
  | Cont -> Some Nz.Cont
  | NoCont -> Some Nz.NoCont
  | Extern -> Some Nz.Extern
  | NoExtern -> Some Nz.NoExtern
  | Any -> Some Nz.Any
  | Eq -> Some Nz.Eq
  | I31 -> Some Nz.I31
  | Struct -> Some Nz.Struct
  | Array -> Some Nz.Array
  | None_ -> Some Nz.None_
  | Type idx ->
      let+@ r = resolve_type_ref d ctx idx in
      Nz.Type r
  | Exact idx ->
      require_feature d ctx ~location:idx.info
        Wax_utils.Feature.Custom_descriptors;
      let+@ r = resolve_type_ref d ctx idx in
      Nz.Exact r

let n_reftype d ctx { Ast.Text.nullable; typ } : Nz.reftype option =
  let+@ typ = n_heaptype d ctx typ in
  { Nz.nullable; typ }

let n_valtype d ctx (ty : Ast.Text.valtype) : Nz.valtype option =
  match ty with
  | I32 -> Some Nz.I32
  | I64 -> Some Nz.I64
  | F32 -> Some Nz.F32
  | F64 -> Some Nz.F64
  | V128 -> Some Nz.V128
  | Ref r ->
      let+@ ty = n_reftype d ctx r in
      Nz.Ref ty

let n_functype d ctx { Ast.Text.params; results } : Nz.functype option =
  let*@ params =
    array_map_opt (fun p -> n_valtype d ctx (snd p.Ast.desc)) params
  in
  let+@ results = array_map_opt (fun ty -> n_valtype d ctx ty) results in
  { Nz.params; results }

let n_storagetype d ctx (ty : Ast.Text.storagetype) : Nz.storagetype option =
  match ty with
  | Value ty ->
      let+@ ty = n_valtype d ctx ty in
      Nz.Value ty
  | Packed ty -> Some (Nz.Packed ty)

let n_fieldtype d ctx ty : Nz.fieldtype option = muttype n_storagetype d ctx ty

let comptype d ctx (ty : Ast.Text.comptype) : Nz.comptype option =
  match ty with
  | Func ty ->
      let+@ ty = n_functype d ctx ty in
      Nz.Func ty
  | Struct fields ->
      let+@ fields =
        array_map_opt (fun e -> n_fieldtype d ctx (snd e.Ast.desc)) fields
      in
      Nz.Struct fields
  | Array field ->
      let+@ field = n_fieldtype d ctx field in
      Nz.Array field
  | Cont idx ->
      let+@ r = resolve_type_ref d ctx idx in
      Nz.Cont r

(* A reference is to an already-defined type when it is a [Def], or a [Rec]
   member strictly before [current] in the group (defined earlier). *)
let defined_before current (r : Types.ref_index) =
  match r with Def _ -> true | Rec pos -> pos < current

let subtype d ctx current
    ({ Ast.Text.typ; supertype; final; descriptor; describes } :
      Ast.Text.subtype) : Types.Normalized.subtype option =
  let*@ typ = comptype d ctx typ in
  let*@ supertype =
    match supertype with
    | None -> Some None
    | Some idx ->
        let+@ r = resolve_type_ref d ctx idx in
        (* A supertype must be an already-defined type: reject a self/forward
           reference to a member of this group at position [>= current]. *)
        (if not (defined_before current r) then
           let lst =
             match idx.desc with
             | Num _ -> []
             | Id id ->
                 Wax_utils.Spell_check.f
                   (fun f ->
                     Hashtbl.iter
                       (fun id' (r, _, _, _) ->
                         if defined_before current r then f id')
                       ctx.label_mapping)
                   id
           in
           Error.unbound_index d ~location:idx.info "type" idx lst);
        Some r
  in
  let resolve_opt = function
    | None -> Some None
    | Some (idx : Ast.Text.idx) ->
        require_feature d ctx ~location:idx.info
          Wax_utils.Feature.Custom_descriptors;
        let+@ r = resolve_type_ref d ctx idx in
        Some r
  in
  let*@ descriptor = resolve_opt descriptor in
  let+@ describes = resolve_opt describes in
  { Nz.typ; supertype; final; descriptor; describes }

(* Each member's components (its supertype, field and element reference types, a
   [cont]'s wrapped type, a descriptor clause) are references made *by that
   member*, so they only keep their targets alive if the member itself is: a rec
   group nothing else names is dead as a whole, cycle and all. [ctx.last_index] is
   still the group's base here — [add_type] advances it once the group resolves. *)
let rectype d ctx ty =
  let base = ctx.last_index in
  let outer = ctx.origin in
  let r =
    array_mapi_opt
      (fun i e ->
        if ctx.origin <> Ignored then ctx.origin <- From_type (base + i);
        subtype d ctx i (snd e.Ast.desc))
      ty
  in
  ctx.origin <- outer;
  r

let typeuse d ctx (idx, sign) =
  match (idx, sign) with
  | Some idx, _ -> (
      (* A typeuse always denotes a function type, so reject a reference to a
         struct/array type with a clean error rather than letting the later
         [typeuse_functype]/[reference_functype] assert. *)
      let*@ ty = resolve_type_index d ctx idx in
      match reference_comptype ctx idx with
      | Func _ -> Some ty
      | _ ->
          Error.expected_func_type d ~location:idx.info idx;
          None)
  | _, Some sign ->
      let+@ ty = n_functype d ctx sign in
      Types.add_rectype ctx.types
        [|
          {
            typ = Func ty;
            supertype = None;
            final = true;
            descriptor = None;
            describes = None;
          };
        |]
  | None, None -> assert false (* Should not happen *)

(* Intern the internal representation type of Wax strings — a mutable array of
   [i8] — and return its canonical index. [string_type_reference] is the form to
   use where a [@string] in the source actually *uses* that type, so that a
   like-typed named definition it deduplicates onto is not reported unused; plain
   [string_type] is for the up-front registration, which is not a use. *)
let string_type ctx =
  Types.add_rectype ctx.types
    [|
      {
        typ = Array { mut = true; typ = Packed I8 };
        supertype = None;
        final = true;
        descriptor = None;
        describes = None;
      };
    |]

let string_type_reference ctx =
  let id = string_type ctx in
  if ctx.record_references && ctx.origin <> Ignored then
    ctx.canonical_type_references <-
      (ctx.origin, id) :: ctx.canonical_type_references;
  id

(*** The module context ***)

(* A reference made from inside a function body, for the reachability analysis
   behind [unused-field]: which index space it targets, and which index in it. A
   reference made from a module-level context instead — an export, the start
   function, a global or table initializer, an element or data segment — is a
   *root*, recorded directly in the matching [used_*] table, because it runs (or
   becomes callable) whatever the bodies do. *)
type reference =
  | Ref_function of int
  | Ref_global of int
  | Ref_memory of int
  | Ref_table of int
  | Ref_tag of int
  | Ref_data of int
  | Ref_elem of int

type module_context = {
  diagnostics : Wax_utils.Diagnostic.context;
  types : type_context;
  subtyping_info : Types.subtyping_info;
  (* Each function carries its type's global index, the source type index it was
     declared with (when it names one, for a [ref.func]'s rendering), and its
     source signature (from its declaration, or its referenced type) — so a call
     names argument and result types from the function's own declaration rather
     than a shared (deduplicated) type index that another structurally-equal type
     may own. *)
  (* Per function: interned type, source type index (if named), signature, and
     whether [ref.func] on it yields an *exact* reference (true for a defined
     function or an exact import, false for a plain import). *)
  functions :
    (Types.Id.t * Ast.Text.idx option * Ast.Text.functype * bool) Sequence.t;
  memories : limits Sequence.t;
  tables : (Types.Internal.tabletype * source_type) Sequence.t;
  globals : (globaltype * source_type) Sequence.t;
  (* Each tag carries its type's global index and its source signature, to name
     a thrown payload's types. *)
  tags : (Types.Id.t * Ast.Text.functype) Sequence.t;
  data : unit Sequence.t;
  (* Each element segment carries its interned reference type and the source
     reference type from its declaration, to name a mismatched element type. *)
  elem : (reftype * source_type) Sequence.t;
  exports : (string, Ast.location) Hashtbl.t;
  refs : (int, unit) Hashtbl.t;
  (* Indices referenced from a *root* context, per index space: an export, the
     start function, a global or table initializer, an element or data segment.
     These seed the [unused-field] reachability analysis. An active data/element
     segment (and a declarative one) is marked at its own definition: it runs at
     instantiation, so it is a root whether or not an instruction names it. *)
  used_functions : (int, unit) Hashtbl.t;
  used_globals : (int, unit) Hashtbl.t;
  used_memories : (int, unit) Hashtbl.t;
  used_tables : (int, unit) Hashtbl.t;
  used_tags : (int, unit) Hashtbl.t;
  used_data : (int, unit) Hashtbl.t;
  used_elem : (int, unit) Hashtbl.t;
  (* Every reference made from inside a body, as (enclosing function, target).
     [unused_fields] walks these to find what each *live* function reaches; a
     reference from a dead function keeps nothing alive. Where the reference is
     made from is [types.origin] (shared with the type references, which are
     recorded on the type context because every type-resolution point can reach
     it). *)
  mutable body_references : (int * reference) list;
  (* Global indices that are the target of a [global.set] anywhere — the marks
     the [unnecessary-mut] warning checks against. Deliberately NOT filtered by
     reachability: dropping the [mut] from a global that a dead function assigns
     would not validate, so a textual assignment, live or not, is enough to keep
     the mutability. *)
  assigned_globals : (int, unit) Hashtbl.t;
  (* Each module-defined (non-import) field, as (index, source name, report
     location): the candidates the [unused-field] warning ranges over. *)
  mutable defined_functions : (int * Ast.Text.name option * Ast.location) list;
  mutable defined_globals : (int * Ast.Text.name option * Ast.location) list;
  mutable defined_memories : (int * Ast.Text.name option * Ast.location) list;
  mutable defined_tables : (int * Ast.Text.name option * Ast.location) list;
  mutable defined_tags : (int * Ast.Text.name option * Ast.location) list;
  mutable defined_data : (int * Ast.Text.name option * Ast.location) list;
  mutable defined_elem : (int * Ast.Text.name option * Ast.location) list;
  (* The module-defined globals declared [mut], in the same shape: the
     [unnecessary-mut] candidates. *)
  mutable mutable_globals : (int * Ast.Text.name option * Ast.location) list;
  (* Likewise for imports — the [unused-import] candidates. They share the index
     space (and so the [used_*] marks) with the defined ones, but are reported
     with a distinct wording. *)
  mutable imported_functions : (int * Ast.Text.name option * Ast.location) list;
  mutable imported_globals : (int * Ast.Text.name option * Ast.location) list;
  mutable imported_memories : (int * Ast.Text.name option * Ast.location) list;
  mutable imported_tables : (int * Ast.Text.name option * Ast.location) list;
  mutable imported_tags : (int * Ast.Text.name option * Ast.location) list;
  (* Whether the extra "unused" analyses run (tied to [-v]/[check], like
     [unused-local]); consulted by lints emitted during stack validation. *)
  warn_unused : bool;
}

module IntSet = Set.Make (Int)

type ctx = {
  (* Each local carries the interned type and the source type for error
     messages (reconstructed from the interned type if no source is known). *)
  locals : (valtype * source_type) Sequence.t;
  (* Each entry is a branch target: its optional label, the interned types a
     branch carries to it, their source types for error messages, and a flag set
     when a branch resolves to this frame (used to report labels never branched
     to). The flag is shared by reference, so a branch deep in a block marks the
     frame the enclosing instruction created. *)
  control_types :
    (string option * valtype array * source_type array * bool ref) list;
  return_types : valtype array;
  return_source : source_type array;
  modul : module_context;
  mutable initialized_locals : IntSet.t;
  (* Indices of locals read by a [local.get]. A local that is never read is
     reported as unused once the function body has been validated. A [ref]
     (rather than a snapshot field like [initialized_locals]) so a read inside a
     block propagates up to the function level. *)
  used_locals : IntSet.t ref;
  (* Indices of locals whose declared type failed to resolve (an unbound type
     index, already reported at the declaration). Such a local is poisoned: a
     [local.get] pushes the bottom reference and a [local.set]/[local.tee]
     accepts any operand, so a use does not cascade a second, spurious type
     mismatch against the recovery dummy type. *)
  poisoned_locals : IntSet.t;
  (* Named block labels declared in this function, each with the [bool ref] its
     control frame carries. A label whose flag is still unset once the body has
     been validated was never branched to and is reported as unused. *)
  label_decls : (Ast.Text.name * bool ref) list ref;
}

let lookup_func_type ctx idx =
  let ctx = ctx.modul in
  let*@ ty = resolve_type_index ctx.diagnostics ctx.types idx in
  let def = Types.get_subtype ctx.subtyping_info ty in
  match def.typ with
  | Func f -> Some (ty, f)
  | Struct _ | Array _ | Cont _ ->
      Error.expected_func_type ctx.diagnostics ~location:idx.info idx;
      None

let lookup_struct_type ctx idx =
  let ctx = ctx.modul in
  let*@ ty, field_map, _, _ = get_type_info ctx.diagnostics ctx.types idx in
  let ty = def_id ty in
  let def = Types.get_subtype ctx.subtyping_info ty in
  match def.typ with
  | Struct fields -> Some (ty, field_map, fields)
  | Func _ | Array _ | Cont _ ->
      Error.expected_struct_type ctx.diagnostics ~location:idx.info idx;
      None

let struct_field_index ctx idx' field_map fields =
  match idx'.Ast.desc with
  | Ast.Text.Id id -> (
      match List.assoc_opt id field_map with
      | Some n -> Some n
      | None ->
          Error.unknown_field ctx.modul.diagnostics ~location:idx'.Ast.info;
          None)
  | Ast.Text.Num n ->
      let n = Uint32.to_int n in
      if n < Array.length fields then Some n
      else (
        Error.field_index_out_of_bounds ctx.modul.diagnostics
          ~location:idx'.Ast.info ~index:n ~count:(Array.length fields);
        None)

let lookup_array_type ctx idx =
  let ctx = ctx.modul in
  let*@ ty = resolve_type_index ctx.diagnostics ctx.types idx in
  let def = Types.get_subtype ctx.subtyping_info ty in
  match def.typ with
  | Array field -> Some (ty, field)
  | Func _ | Struct _ | Cont _ ->
      Error.expected_array_type ctx.diagnostics ~location:idx.info idx;
      None

(* The descriptor type of the type at global index [ty], for the descriptor
   instructions ([struct.new_desc], [ref.get_desc], …). Reports an error and
   returns [None] when the type carries no [descriptor] clause. *)
let type_descriptor ctx ~location ty =
  match (Types.get_subtype ctx.modul.subtyping_info ty).descriptor with
  | Some desc -> Some desc
  | None ->
      Error.type_without_descriptor ctx.modul.diagnostics ~location;
      None

(* The heap type of the descriptor operand expected by a [_desc_eq] cast/branch
   whose target heap type is [target] (either [Exact x] or [Type x]). The
   operand's exactness matches the target's ([exact_1] in the spec); [y] is [x]'s
   descriptor. *)
let descriptor_operand_type ctx ~location (target : heaptype) =
  match target with
  | Exact x ->
      let+@ d = type_descriptor ctx ~location x in
      Exact d
  | Type x ->
      let+@ d = type_descriptor ctx ~location x in
      Type d
  | _ ->
      Error.invalid_cast_type ctx.modul.diagnostics ~location;
      None

(* Mark the index [idx] resolves to in [seq], whatever the enclosing context. *)
let mark_index used seq idx =
  Option.iter
    (fun i -> Hashtbl.replace used i ())
    (Sequence.get_index_opt seq idx)

(* Record the reference [idx] makes to the index space [seq], for the
   [unused-field] warning. Inside a function body it becomes an edge from that
   function; from a module-level context it is a root, marked in [used]. [mctx] is
   the module context. *)
let mark_reference mctx wrap used seq idx =
  (* Only the [unused-field] analysis consumes any of this, and [body_references]
     grows with every reference in the module, so record nothing when the lint is
     off. *)
  if mctx.warn_unused then
    Option.iter
      (fun i ->
        match mctx.types.origin with
        | From_function caller ->
            mctx.body_references <- (caller, wrap i) :: mctx.body_references
        | Ignored -> ()
        (* Only types reference types, so [From_type] never reaches an index
           space; treat it as a root rather than losing the reference. *)
        | Root | From_type _ -> Hashtbl.replace used i ())
      (Sequence.get_index_opt seq idx)

(* The parameter types of an exception [tag] and, when known, their source
   types for naming a thrown payload. [lookup_tag_type]/[lookup_tag_signature]
   are the two resolution points for every tag reference (a [throw], a [catch]
   clause, a [suspend]/[resume] handler), so they record the tag as used. *)
let lookup_tag_type ctx tag =
  let ctx = ctx.modul in
  mark_reference ctx (fun i -> Ref_tag i) ctx.used_tags ctx.tags tag;
  let*@ ty, sign = Sequence.get ctx.diagnostics ctx.tags tag in
  match (Types.get_subtype ctx.subtyping_info ty).typ with
  | Struct _ | Array _ | Cont _ ->
      Error.not_function_type ctx.diagnostics ~location:tag.info;
      None
  | Func { params; results } ->
      if results <> [||] then
        Error.exception_tag_with_results ctx.diagnostics ~location:tag.info;
      Some (params, Array.map (fun p -> Plain (snd p.Ast.desc)) sign.params)

(* Full function type of a tag, used for stack-switching suspension tags whose
   results may be non-empty (unlike exception tags). *)
let lookup_tag_signature ctx tag =
  let ctx = ctx.modul in
  mark_reference ctx (fun i -> Ref_tag i) ctx.used_tags ctx.tags tag;
  let*@ ty, sign = Sequence.get ctx.diagnostics ctx.tags tag in
  match (Types.get_subtype ctx.subtyping_info ty).typ with
  | Func ft -> Some (ft, sign)
  | Struct _ | Array _ | Cont _ ->
      Error.not_function_type ctx.diagnostics ~location:tag.info;
      None

(* Resolve a continuation type index to its own index and the function type it
   wraps. Emits an error if the type is not a continuation type. *)
let lookup_cont_type ctx idx =
  let mctx = ctx.modul in
  let*@ ty = resolve_type_index mctx.diagnostics mctx.types idx in
  match (Types.get_subtype mctx.subtyping_info ty).typ with
  | Cont ft -> (
      match (Types.get_subtype mctx.subtyping_info ft).typ with
      | Func f -> Some (ty, ft, f)
      | Struct _ | Array _ | Cont _ ->
          Error.expected_cont_type mctx.diagnostics ~location:idx.info idx;
          None)
  | Struct _ | Array _ | Func _ ->
      Error.expected_cont_type mctx.diagnostics ~location:idx.info idx;
      None

(* The continuation type referenced by a heap type, if any. *)
let cont_functype_of_heaptype ctx (h : heaptype) =
  match h with
  | Type ty | Exact ty -> (
      match (Types.get_subtype ctx.modul.subtyping_info ty).typ with
      | Cont ft -> (
          match (Types.get_subtype ctx.modul.subtyping_info ft).typ with
          | Func f -> Some f
          | Struct _ | Array _ | Cont _ -> None)
      | Func _ | Struct _ | Array _ -> None)
  | _ -> None

(* [functype_matches info ft ft'] holds when [ft] is a subtype of [ft']:
   parameters are contravariant and results covariant. *)
let functype_matches info (ft : functype) (ft' : functype) =
  Array.length ft.params = Array.length ft'.params
  && Array.length ft.results = Array.length ft'.results
  && Array.for_all Fun.id
       (Array.mapi
          (fun i p -> Types.val_subtype info ft'.params.(i) p)
          ft.params)
  && Array.for_all Fun.id
       (Array.mapi
          (fun i r -> Types.val_subtype info r ft'.results.(i))
          ft.results)

(* [result_subtype info ts ts'] holds when result type [ts] matches [ts']
   (same length, covariant element by element). *)
let result_subtype info (ts : valtype array) (ts' : valtype array) =
  Array.length ts = Array.length ts'
  && Array.for_all Fun.id
       (Array.mapi (fun i t -> Types.val_subtype info t ts'.(i)) ts)

(* [result_equivalent info ts ts'] holds when the two result types are
   equivalent, i.e. mutual subtypes (which coincides with equality in the
   single-inheritance reference-type lattice). *)
let result_equivalent info ts ts' =
  result_subtype info ts ts' && result_subtype info ts' ts

(* Source type of struct field [n] of the type that reference [idx] names, when
   the field has a (non-packed) value type. Packed fields surface as i32, so
   they get no name. Resolving through the reference (not the deduplicated
   global index) names the field as written at this very type. *)
let source_field_valtype ctx idx n : source_type =
  match reference_comptype ctx.modul.types idx with
  | Struct fields -> (
      let _, (ft : Ast.Text.fieldtype) = fields.(n).Ast.desc in
      match ft.typ with Value v -> Plain v | Packed _ -> Plain I32)
  | _ -> assert false

(* Source type of the element of the array type that reference [idx] names. *)
let source_element_valtype ctx idx : source_type =
  match reference_comptype ctx.modul.types idx with
  | Array (ft : Ast.Text.fieldtype) -> (
      match ft.typ with Value v -> Plain v | Packed _ -> Plain I32)
  | _ -> assert false

(*** The validation stack ***)

(* A stack entry is one of the two bottoms of the validation type lattice or a
   concrete value. [Bot] is the unknown value of a polymorphic (unreachable)
   stack: a subtype of every type. [Bot_ref] is the bottom reference type
   [(ref bot)], produced when a reference-eliminating instruction consumes a
   [Bot]: it is a subtype of every reference type but of no numeric or vector
   type, which is what lets [ref.as_non_null] / [br_on_null] reject a numeric
   use of their result on an otherwise polymorphic stack. [Val] pairs the
   interned type used for subtype checking with the source type the value was
   written as, mirroring the Wax side's [inferred_valtype]; the source type is
   always present, a push that does not supply one reconstructing it from the
   interned type (naming an indexed type by its canonical index). *)
type stack_entry = Bot | Bot_ref | Val of valtype * source_type

type stack =
  | Unreachable
  | Empty
  | Cons of Ast.location option * stack_entry * stack

(* Returns the popped entry, along with its push location. A pop from an
   unreachable or empty stack yields the unknown value [Bot]; an underflow
   turns the stack unreachable (as in [pop]), so one missing value is reported
   once rather than once per subsequent pop. *)
let pop_any ctx loc st =
  match st with
  | Unreachable -> (Unreachable, (Bot, None))
  | Cons (loc, ty, r) -> (r, (ty, loc))
  | Empty ->
      Error.empty_stack ctx.modul.diagnostics ~location:loc;
      (Unreachable, (Bot, None))

(* The non-null version of a popped reference's source type, for an instruction
   that re-pushes the value with the null case removed. *)
let non_null_source (source : source_type) : source_type =
  match source with
  | Plain (Ref r) -> Plain (Ref { r with nullable = false })
  | Inline_ref _ as source -> source
  | _ -> assert false

let pop ctx loc ?arity ~expected_source ty st =
  let mismatch location source =
    match location with
    | Some location ->
        Error.instruction_type_mismatch ctx.modul.diagnostics ~location
          ~consumer:(Some loc) ~provided_source:source ~expected_source
    | None ->
        Error.type_mismatch ctx.modul.diagnostics ~location:loc
          ~provided_source:source ~expected_source
  in
  match st with
  | Unreachable -> (Unreachable, ())
  | Cons (_, Bot, r) -> (r, ())
  | Cons (location, Bot_ref, r) ->
      (* [(ref bot)] is a subtype of every reference type but of no numeric or
         vector type. *)
      (match ty with Ref _ -> () | _ -> mismatch location Bottom_ref);
      (r, ())
  | Cons (location, Val (ty', source), r) ->
      let ok = Types.val_subtype ctx.modul.subtyping_info ty' ty in
      if not ok then mismatch location source;
      (r, ())
  | Empty ->
      (* With an arity context ([pop_args]) the counts are known: report how
         many values the construct takes and how many were there — the results
         of a block or function are anchored at its closing token. A lone pop
         keeps the plain report. *)
      (match arity with
      | Some (kind, current, expected) ->
          Error.short_stack ctx.modul.diagnostics kind
            ~location:
              (match kind with `Input -> loc | `Output -> loc_last_char loc)
            ~actual:(expected - current - 1)
            ~expected
      | None -> Error.empty_stack ctx.modul.diagnostics ~location:loc);
      (Unreachable, ())

(* Pop a value whose expected type has no user-written source form — a builtin,
   address, or abstract reference type — so its rendering is reconstructed. *)
let pop_known ctx loc ty =
  pop ctx loc ~expected_source:(source_of_valtype ty) ty

let push_poly loc st =
  record (Some loc) Polymorphic;
  (Cons (Some loc, Bot, st), ())

let push_bot_ref loc st =
  record loc (Pushed Bottom_ref);
  (Cons (loc, Bot_ref, st), ())

let push ~source loc ty st =
  record loc (Pushed source);
  record_value_type_def loc source;
  (Cons (loc, Val (ty, source), st), ())

(* Push a value whose type has no user-written source form, reconstructing its
   rendering from the type. *)
let push_known loc ty = push ~source:(source_of_valtype ty) loc ty

(* The source rendering of a reference to the named type [idx], used as the
   [source] form of a value an instruction pushes ([named_ref_source], non-null) or
   expects ([named_ref_null_source], the nullable form pop accepts). *)
let named_ref_source idx : source_type =
  Plain (Ref { nullable = false; typ = Type idx })

let named_ref_null_source idx : source_type =
  Plain (Ref { nullable = true; typ = Type idx })

(* The push-source of a value a concrete allocator produces at exactly type [idx]
   ([struct.new], [array.new*], [cont.new], [cont.bind]): these push an *exact*
   internal reference, so under custom-descriptors the source is rendered exact
   to match. Without the proposal exact reference types are not expressible, so it
   falls back to the plain named source (the internal type stays exact, but that
   extra precision is unobservable there). *)
(* Whether a value an ALLOCATION (or a [ref.func]) yields carries the EXACT type
   allocated. It does — but exact reference types are part of custom-descriptors,
   so without the feature it is the plain inexact reference, as before the
   proposal. The Wax typer gates its own [construction_result]/[register_function]
   the same way and the two must agree: ungated, the exact type made a [ref.test]
   against any other type look impossible, so the validator reported an
   always-false test on a downcast that can in fact succeed (two structurally
   identical rec groups are the same canonical type) while the typer stayed
   correctly silent — a lint-parity finding from the wax mutation fuzzer, first
   seen on [ref.func] and true of every allocation. The [*_desc] forms below need
   no gate: those instructions exist only under the feature. *)
let allocation_is_exact ctx =
  Wax_utils.Feature.is_enabled ctx.modul.types.features
    Wax_utils.Feature.Custom_descriptors

let exact_ref_source ctx idx : source_type =
  if
    Wax_utils.Feature.is_enabled ctx.modul.types.features
      Wax_utils.Feature.Custom_descriptors
  then Plain (Ref { nullable = false; typ = Exact idx })
  else named_ref_source idx

(* The source rendering of the descriptor of the type at global index
   [described] — the [_desc_eq] cast/branch operand (nullable), or the
   [ref.get_desc] result (non-null, via [~nullable:false]). The descriptor type
   has no immediate to name it by, so its source name is recovered from
   [descriptor_source] (recorded at its definition); [exact] matches [described]'s
   own exactness. *)
let descriptor_operand_source ?(nullable = true) tc (described : heaptype) :
    source_type =
  let build exact x =
    match Hashtbl.find_opt tc.descriptor_source x with
    | Some node ->
        Plain
          (Ref { nullable; typ = (if exact then Exact node else Type node) })
    | None ->
        (* No recorded source (a well-formed descriptor type always has one);
           fall back to the abstract struct supertype rather than a misleading
           index. *)
        Plain (Ref { nullable; typ = source_of_heaptype Struct })
  in
  match described with
  | Exact x -> build true x
  | Type x -> build false x
  | _ -> Plain (Ref { nullable; typ = source_of_heaptype Struct })

(* Source-type array for popping the prefix arguments [param_source] followed by a
   continuation operand of the type named by [x]. *)
let cont_operand_source param_source x =
  Array.append param_source [| named_ref_null_source x |]

(* Source params of the function type the continuation type [x] wraps; they are
   exactly that function type's parameters. *)
let cont_param_source ctx x =
  Array.map
    (fun p -> Plain (snd p.Ast.desc))
    (cont_source_functype ctx.modul.types x).params

let unreachable _ = (Unreachable, ())
let return v st = (st, v)

(* These operators thread the value stack through validation. [let*] sequences
   two stack transformers, passing the stack from one to the next. [let*!] and
   [let*?] guard a transformer on an [option] (typically a failed lookup that
   has already reported an error): on [None] they abandon this instruction's
   effect, [let*!] yielding the [unreachable] transformer and [let*?] yielding
   no stack effect at all (for checks run outside a transformer). *)
let ( let* ) e f st =
  let st, v = e st in
  f v st

let ( let*! ) e f = match e with Some v -> f v | None -> unreachable
let ( let*? ) e f = match e with Some v -> f v | None -> ()

let get_local ctx ?(initialize = false) i =
  let+@ l = Sequence.get ctx.modul.diagnostics ctx.locals i in
  let idx = Sequence.get_index ctx.locals i in
  if initialize then
    ctx.initialized_locals <- IntSet.add idx ctx.initialized_locals
  else begin
    ctx.used_locals := IntSet.add idx !(ctx.used_locals);
    if not (IntSet.mem idx ctx.initialized_locals) then
      Error.uninitialized_local ctx.modul.diagnostics ~location:i.info i
  end;
  l

(* Whether local [i] resolves to a poisoned local (declared with a type that did
   not resolve). Uses the same resolved index [get_local] tracks; a use of such
   a local is treated as the bottom reference to avoid cascading a second error. *)
let local_is_poisoned ctx i =
  match Sequence.get_index_opt ctx.locals i with
  | Some idx -> IntSet.mem idx ctx.poisoned_locals
  | None -> false

(* The result nullability of [extern.convert_any] / [any.convert_extern], which
   propagate the operand's nullability. The operand must be a reference in the
   [typ] hierarchy: a bottom reference satisfies it as known non-null, a
   fully-unknown [Bot] (a polymorphic, unreachable stack) is treated as non-null
   — the most precise choice, like [Bot_ref] — and a non-reference operand (a
   reported error) is treated as nullable rather than crashing. *)
let convert_operand_nullable ctx loc (entry, entry_loc) ~typ =
  match entry with
  | Bot -> false
  | Bot_ref -> false
  | Val (ty, source) -> (
      let expected = Ref { nullable = true; typ } in
      (if not (Types.val_subtype ctx.modul.subtyping_info ty expected) then
         (* As in [pop]: blame the value where it was pushed when that is
            known, with the conversion as the consumer. *)
         match entry_loc with
         | Some location ->
             Error.instruction_type_mismatch ctx.modul.diagnostics ~location
               ~consumer:(Some loc) ~provided_source:source
               ~expected_source:(source_of_valtype expected)
         | None ->
             Error.type_mismatch ctx.modul.diagnostics ~location:loc
               ~provided_source:source
               ~expected_source:(source_of_valtype expected));
      match ty with Ref { nullable; _ } -> nullable | _ -> true)

let is_defaultable ty =
  match ty with
  | I32 | I64 | F32 | F64 | V128 -> true
  | Ref { nullable; _ } -> nullable

let number_or_vec ty =
  match ty with I32 | I64 | F32 | F64 | V128 -> true | Ref _ -> false

let int_un_op_type ty (op : Ast.Text.int_un_op) =
  match op with
  | Clz | Ctz | Popcnt | ExtendS _ -> (ty, ty)
  | Trunc (sz, _) | TruncSat (sz, _) ->
      ((match sz with `F32 -> F32 | `F64 -> F64), ty)
  | Reinterpret ->
      ( (match ty with
        | I32 -> F32
        | I64 -> F64
        | _ -> assert false (* Should not happen *)),
        ty )
  | Eqz -> (ty, I32)

let int_bin_op_type ty (op : Ast.Text.int_bin_op) =
  match op with
  | Add | Sub | Mul | Div _ | Rem _ | And | Or | Xor | Shl | Shr _ | Rotl | Rotr
    ->
      ty
  | Eq | Ne | Lt _ | Gt _ | Le _ | Ge _ -> I32

let float_un_op_type ty (op : Ast.Text.float_un_op) =
  match op with
  | Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt -> ty
  | Convert (sz, _) -> ( match sz with `I32 -> I32 | `I64 -> I64)
  | Reinterpret -> (
      match ty with
      | F32 -> I32
      | F64 -> I64
      | _ -> assert false (* Should not happen *))

let float_bin_op_type ty (op : Ast.Text.float_bin_op) =
  match op with
  | Add | Sub | Mul | Div | Min | Max | CopySign -> ty
  | Eq | Ne | Lt | Gt | Le | Ge -> I32

(* Returns the interned block parameter and result types, plus their per-element
   source types (for [pop_args]/[push_results]'s [~source]). Like [typeuse], a
   type reference is resolved in preference to an inline signature; for valid
   input the two agree ([check_syntax]'s inline check), and preferring the
   reference makes it the one place a block's typeuse index is resolved (and an
   unbound one reported). *)
let blocktype ctx (ty : Ast.Text.blocktype option) =
  match ty with
  | None -> Some ([||], [||], [||], [||])
  | Some (Typeuse (Some idx, _)) ->
      let+@ _, { params; results } = lookup_func_type ctx idx in
      let param_source, result_source =
        functype_sources (reference_functype ctx.modul.types idx)
      in
      (params, results, param_source, result_source)
  | Some (Typeuse (None, Some ({ params; results } as ft))) ->
      let*@ iparams =
        array_map_opt
          (fun p ->
            valtype ctx.modul.diagnostics ctx.modul.types (snd p.Ast.desc))
          params
      in
      let+@ iresults =
        array_map_opt (valtype ctx.modul.diagnostics ctx.modul.types) results
      in
      let param_source, result_source = functype_sources ft in
      (iparams, iresults, param_source, result_source)
  | Some (Typeuse (None, None)) -> assert false (* Should not happen *)
  | Some (Valtype ty) ->
      let+@ t = valtype ctx.modul.diagnostics ctx.modul.types ty in
      ([||], [| t |], [||], [| Plain ty |])

let pop_args ctx ?(kind = `Input) loc ~source args =
  let len = Array.length args in
  let rec loop i =
    if i < 0 then return ()
    else
      let* () =
        pop ctx loc ~arity:(kind, i, len) ~expected_source:source.(i) args.(i)
      in
      loop (i - 1)
  in
  loop (len - 1)

(* [sink] (default [true]) records each pushed result at the instruction span
   [loc] for the editor type sink. A {e single} result cell also carries [loc] as
   its provenance — that value was unambiguously pushed by this instruction, so a
   "value pushed here" diagnostic (and hover) points at it; [push] does the sink
   recording in that case. Several results cannot each be that one span, so their
   cells push location [None] and the span is recorded here instead. Set
   [~sink:false] where [push_results] simulates a branch target or a block's
   entry parameters rather than pushing the instruction's own results: nothing is
   attributed to the instruction's span, cells included. *)
let push_results ?(sink = true) ~loc ~source results =
  let single = Array.length results = 1 in
  let cell_loc = if sink && single then Some loc else None in
  let rec loop i =
    if i >= Array.length results then return ()
    else begin
      if sink && not single then begin
        record (Some loc) (Pushed source.(i));
        record_value_type_def (Some loc) source.(i)
      end;
      let* () = push ~source:source.(i) cell_loc results.(i) in
      loop (i + 1)
    end
  in
  loop 0

let rec output_stack ~full pp st =
  match st with
  | Empty -> ()
  | Unreachable ->
      if full then (
        sp_space pp;
        sp_kw pp "unreachable")
  | Cons (_, ty, st) ->
      sp_space pp;
      (match ty with
      | Val (_, source) -> print_source_type pp source
      | Bot -> sp_type pp "bot"
      | Bot_ref ->
          sp_box pp (fun () ->
              sp_punct pp "(";
              sp_kw pp "ref";
              sp_space pp;
              sp_type pp "bot";
              sp_punct pp ")"));
      output_stack ~full pp st

let print_stack st =
  Wax_utils.Printer.run_err (fun p ->
      let pp =
        Wax_utils.Styled_printer.create ~printer:p
          ~theme:Wax_utils.Colors.no_color
          ~trivia:(Wax_utils.Trivia.empty ())
          ()
      in
      Wax_utils.Printer.string p "Stack:";
      output_stack ~full:true pp st);
  (st, ())

let _ = print_stack

let with_empty_stack ctx location f =
  let st, () = f Empty in
  (* The source locations of the values still on the stack, topmost first.
     Values without a usable location (a block parameter/result, or an
     error-recovery placeholder) are dropped. *)
  let rec locations = function
    | Cons (Some loc, _, st) when loc.Ast.loc_start.Lexing.pos_cnum >= 0 ->
        loc :: locations st
    | Cons (_, _, st) -> locations st
    | Empty | Unreachable -> []
  in
  match st with
  | Empty | Unreachable -> ()
  | Cons _ -> (
      match locations st with
      | location :: rest ->
          (* Point a caret right at each leftover value rather than at the
             (potentially large) enclosing construct. *)
          let related =
            List.map
              (fun location ->
                {
                  Wax_utils.Diagnostic.location;
                  message = Wax_utils.Message.empty;
                })
              rest
          in
          Error.leftover_values ctx.diagnostics ~location ~related
      | [] ->
          (* No value carries a usable location: point at the construct and
             list the values that remain, since the location alone does not
             show them. *)
          Error.non_empty_stack ctx.diagnostics ~location (fun pp ->
              output_stack ~full:false pp st))

(*** Instruction-checking helpers ***)

(* Check that a list of [provided] argument types matches a list of [expected]
   parameter types: same length, and each argument a subtype of the
   corresponding parameter. [descr] names the construct supplying the
   arguments. Reporting the two lists directly gives a far clearer message than
   simulating the comparison on the value stack. *)
let compare_types ctx ~location ~descr ~provided_source ~expected_source
    ~provided ~expected () =
  if Array.length provided <> Array.length expected then
    Error.argument_count_mismatch ctx.diagnostics ~location ~descr
      ~provided_source ~expected_source
  else
    Array.iteri
      (fun i p ->
        let e = expected.(i) in
        if not (Types.val_subtype ctx.subtyping_info p e) then
          Error.argument_type_mismatch ctx.diagnostics ~location ~descr
            ~nth:(if Array.length provided > 1 then Some (i + 1) else None)
            ~provided_source:provided_source.(i)
            ~expected_source:expected_source.(i))
      provided

let branch_target ctx (idx : Ast.Text.idx) =
  match idx.desc with
  | Num i -> (
      try
        let _, params, source, used =
          List.nth ctx.control_types (Uint32.to_int i)
        in
        used := true;
        Some (params, source)
      with Failure _ ->
        Error.unbound_label ctx.modul.diagnostics ~location:idx.Ast.info idx [];
        None)
  | Id id ->
      let rec find l id =
        match l with
        | [] ->
            let lst =
              Wax_utils.Spell_check.f
                (fun f ->
                  List.iter
                    (fun (id_opt, _, _, _) ->
                      match id_opt with Some id -> f id | None -> ())
                    ctx.control_types)
                id
            in
            Error.unbound_label ctx.modul.diagnostics ~location:idx.Ast.info idx
              lst;
            None
        | (Some id', params, source, used) :: _ when id = id' ->
            used := true;
            Some (params, source)
        | _ :: rem -> find rem id
      in
      find ctx.control_types id

(* The top of the heap-type hierarchy that [t] belongs to (one of [any], [func],
   [exn], [cont], [extern]). A cast or test pops a reference to this top type —
   the most general operand the instruction accepts — before checking against
   the precise target. *)
let top_heap_type ctx (t : heaptype) : heaptype =
  match t with
  | Any | Eq | I31 | Struct | Array | None_ -> Any
  | Func | NoFunc -> Func
  | Exn | NoExn -> Exn
  | Cont | NoCont -> Cont
  | Extern | NoExtern -> Extern
  | Type ty | Exact ty -> (
      match (Types.get_subtype ctx.modul.subtyping_info ty).typ with
      | Struct _ | Array _ -> Any
      | Func _ -> Func
      | Cont _ -> Cont)

let storage_subtype info ty ty' =
  match (ty, ty') with
  | Packed I8, Packed I8 | Packed I16, Packed I16 -> true
  | Value ty, Value ty' -> Types.val_subtype info ty ty'
  | Packed I8, Packed I16
  | Packed I16, Packed I8
  | Packed _, Value _
  | Value _, Packed _ ->
      false

let field_subtype info (ty : fieldtype) (ty' : fieldtype) =
  ty.mut = ty'.mut
  && storage_subtype info ty.typ ty'.typ
  && ((not ty.mut) || storage_subtype info ty'.typ ty.typ)

(* The reference type difference [t1 \ t2] from the spec: [t1]'s heap type, made
   non-nullable once a nullable [t2] has consumed the null case. This is the type
   that falls through a [br_on_cast] (or is sent on by [br_on_cast_fail]); the
   inline [src_diff] in those arms is the same operation on source types. *)
let diff_ref_type t1 t2 =
  { nullable = t1.nullable && not t2.nullable; typ = t1.typ }

(* Whether a branching cast from [ty1] to [ty2] is well-typed. The
   custom-descriptors proposal relaxes the pre-existing [rt2 <: rt1] to only
   requiring that [rt1] and [rt2] share a supertype — i.e. lie in the same heap
   type hierarchy — so under that feature we compare the hierarchy tops. *)
let br_cast_compatible ctx (ty1 : reftype) (ty2 : reftype) =
  if
    Wax_utils.Feature.is_enabled ctx.modul.types.features
      Wax_utils.Feature.Custom_descriptors
  then top_heap_type ctx ty1.typ = top_heap_type ctx ty2.typ
  else Types.val_subtype ctx.modul.subtyping_info (Ref ty2) (Ref ty1)

(* The target of a branching cast ([br_on_cast] and its variants) always carries
   at least the matched reference to the label, so a zero-result label cannot
   receive it. [branch_target] alone accepts it — with a polymorphic operand the
   per-value [pop_args] check below is vacuous — so reject an empty label here. *)
let branch_cast_target ctx (idx : Ast.Text.idx) ~location =
  match branch_target ctx idx with
  | None -> None
  | Some (params, source) ->
      if Array.length params = 0 then (
        Error.br_cast_type_mismatch ctx.modul.diagnostics ~location;
        None)
      else Some (params, source)

(* Run [f] on the current stack and return its result as the monad value while
   leaving the stack untouched — a peek. [Br_table] uses it to validate every
   branch target against the same incoming stack. *)
let with_current_stack f st = (st, f st)

(* Lint a [ref.cast]/[ref.test] against its operand (the top of the current
   stack). Under single-inheritance subtyping two heap types share a value only
   when one is a subtype of the other, so unrelated types make the cast always
   trap (the test always false) — unless a shared [null] slips through. When the
   operand already has the target type the cast/test is redundant. Only fires
   when unused reporting is on. *)
let lint_cast ctx ~location ~is_test (target : reftype) =
  if not ctx.modul.warn_unused then return ()
  else
    with_current_stack (fun st ->
        match st with
        | Cons (_, Val (Ref op, _), _) ->
            let info = ctx.modul.subtyping_info in
            let related =
              Types.heap_subtype info op.typ target.typ
              || Types.heap_subtype info target.typ op.typ
            in
            if (not related) && not (op.nullable && target.nullable) then
              Error.cast_always_fails ctx.modul.diagnostics ~location ~is_test
            else if Types.ref_subtype info op target then
              Error.redundant_cast ctx.modul.diagnostics ~location ~is_test
        | _ -> ())

let unpack_type (f : fieldtype) =
  match f.typ with Value v -> v | Packed _ -> I32

(* Pop [n] values of type [ty] (as [array.new_fixed] does), in time proportional
   to the operands actually present, not to [n]. Once the stack is [Unreachable]
   -- the polymorphic base, or a reachable underflow after the first empty pop
   turns it into one -- every remaining pop trivially succeeds, so stop. This
   keeps a huge immediate count (e.g. [array.new_fixed 2^31]) from making
   validation O(n). *)
let rec pop_repeat ctx loc ~expected_source ty n st =
  if n <= 0 then (st, ())
  else
    match st with
    | Unreachable -> (Unreachable, ())
    | _ ->
        let st, () = pop ctx loc ~expected_source ty st in
        pop_repeat ctx loc ~expected_source ty (n - 1) st

let address_type_to_valtype = function `I32 -> I32 | `I64 -> I64

(* Constants for max offsets *)

let max_offset_i32_exclusive = Uint64.of_string "0x1_0000_0000" (* 2^32 *)
let max_align = Uint64.of_int 16

let check_memarg ctx location limits sz { Ast.Text.offset; align } =
  if limits.address_type = `I32 then
    if Uint64.compare offset max_offset_i32_exclusive >= 0 then
      Error.memory_offset_too_large ctx.modul.diagnostics ~location
        max_offset_i32_exclusive;
  let natural_alignment =
    match sz with
    | `I8 -> 1
    | `I16 -> 2
    | `I32 | `F32 -> 4
    | `I64 | `F64 -> 8
    | `V128 -> 16
  in
  if
    Uint64.compare align max_align > 0
    || Uint64.to_int align > natural_alignment
  then
    Error.memory_align_too_large ctx.modul.diagnostics ~location
      natural_alignment
  else
    match Uint64.to_int align with
    | 1 | 2 | 4 | 8 | 16 -> ()
    | _ -> Error.bad_memory_align ctx.modul.diagnostics ~location

(* An atomic access requires exactly its natural alignment, not merely at most. *)
let check_atomic_memarg ctx location limits op { Ast.Text.offset; align } =
  if
    limits.address_type = `I32
    && Uint64.compare offset max_offset_i32_exclusive >= 0
  then
    Error.memory_offset_too_large ctx.modul.diagnostics ~location
      max_offset_i32_exclusive;
  let natural = 1 lsl Atomics.natural_align_log2 op in
  if Uint64.compare align (Uint64.of_int natural) <> 0 then
    Error.atomic_alignment ctx.modul.diagnostics ~location natural

let memory_instruction_type_and_size ty =
  match (ty : Ast.Text.num_type) with
  | NumI32 -> (I32, `I32)
  | NumF32 -> (F32, `I32)
  | NumI64 -> (I64, `I64)
  | NumF64 -> (F64, `I64)

let field_has_default (ty : fieldtype) =
  match ty.typ with
  | Packed _ -> true
  | Value ty -> (
      match ty with
      | I32 | I64 | F32 | F64 | V128 -> true
      | Ref { nullable; _ } -> nullable)

let shape_type (shape : Ast.vec_shape) =
  match shape with
  | I8x16 | I16x8 | I32x4 -> I32
  | I64x2 -> I64
  | F32x4 -> F32
  | F64x2 -> F64

let check_shape_lanes ctx location (shape : Ast.vec_shape) lane =
  let max_lane =
    match shape with
    | I8x16 -> 16
    | I16x8 -> 8
    | I32x4 | F32x4 -> 4
    | I64x2 | F64x2 -> 2
  in
  if lane >= max_lane then
    Error.invalid_lane_index ctx.modul.diagnostics ~location max_lane

(* Validate the handler clauses of a [resume]/[resume_throw] instruction. [ts2]
   is the result type of the resumed continuation. *)
let check_resume_table ctx loc ts2 clauses =
  let info = ctx.modul.subtyping_info in
  List.iter
    (fun (clause : Ast.Text.on_clause) ->
      match clause with
      | OnLabel (tag, label) -> (
          match lookup_tag_signature ctx tag with
          | None -> ()
          | Some ({ params = ts3; results = ts4 }, _) -> (
              match branch_target ctx label with
              | None -> ()
              | Some (ts', _) ->
                  let n = Array.length ts' in
                  let mismatch () =
                    Error.stack_switching_type_mismatch ctx.modul.diagnostics
                      ~location:label.info
                      ~descr:
                        "this handler must take the tag's parameters followed \
                         by a continuation of the remaining result type"
                  in
                  (* The handler label receives the tag's parameters followed by
                     a continuation of type [cont (ts4 -> ts2)]. *)
                  if n <> Array.length ts3 + 1 then mismatch ()
                  else begin
                    Array.iteri
                      (fun i t ->
                        if not (Types.val_subtype info t ts'.(i)) then
                          mismatch ())
                      ts3;
                    match ts'.(n - 1) with
                    | Ref { typ = ht; _ } -> (
                        match cont_functype_of_heaptype ctx ht with
                        | Some ft' ->
                            if
                              not
                                (functype_matches info
                                   { params = ts4; results = ts2 }
                                   ft')
                            then mismatch ()
                        | None -> mismatch ())
                    | _ -> mismatch ()
                  end))
      | OnSwitch tag -> (
          match lookup_tag_signature ctx tag with
          | None -> ()
          | Some ({ params = ts3; results = ts4 }, _) ->
              (* A switch handler tag has type [] -> [t*] (no parameters). The
                 canonical stack-switching rule reifies the current continuation
                 as [cont [t2*] -> [t*]] and runs it to this [resume] boundary,
                 whose continuation results are [ts2]; for that to be consistent
                 [t*] must *equal* [ts2] (equivalence, not merely subtyping). A
                 subtype would let a continuation whose completion actually
                 produces [ts2] be observed by a peer at the narrower tag type
                 [t*] — an unchecked narrowing. This matches V8
                 (IsEquivalentTypeVec) and the spec author's fix; the older
                 written subtyping rule is unsound. *)
              if Array.length ts3 <> 0 then
                Error.stack_switching_type_mismatch ctx.modul.diagnostics
                  ~location:loc
                  ~descr:"the tag of a 'switch' handler must take no parameters"
              else if not (result_equivalent info ts4 ts2) then
                Error.stack_switching_type_mismatch ctx.modul.diagnostics
                  ~location:loc
                  ~descr:
                    "the results of a 'switch' handler's tag must match the \
                     resumed continuation's results"))
    clauses

(* Look up an entry in a module-level index space, reporting an unbound-index
   error (via {!Sequence.get}) when the reference does not resolve. Each [get_*]
   is the single resolution point for every reference to that space — a
   [global.get]/[global.set], a [call]/[return_call]/[ref.func], a memory/table
   access, a segment operand — whether in a body or a constant expression, so
   noting the resolved index here records the field as used. *)
let get_memory ctx idx =
  mark_reference ctx.modul
    (fun i -> Ref_memory i)
    ctx.modul.used_memories ctx.modul.memories idx;
  Sequence.get ctx.modul.diagnostics ctx.modul.memories idx

let get_table ctx idx =
  mark_reference ctx.modul
    (fun i -> Ref_table i)
    ctx.modul.used_tables ctx.modul.tables idx;
  Sequence.get ctx.modul.diagnostics ctx.modul.tables idx

let get_global ctx idx =
  mark_reference ctx.modul
    (fun i -> Ref_global i)
    ctx.modul.used_globals ctx.modul.globals idx;
  Sequence.get ctx.modul.diagnostics ctx.modul.globals idx

let get_function ctx idx =
  mark_reference ctx.modul
    (fun i -> Ref_function i)
    ctx.modul.used_functions ctx.modul.functions idx;
  Sequence.get ctx.modul.diagnostics ctx.modul.functions idx

let get_data ctx idx =
  mark_reference ctx.modul
    (fun i -> Ref_data i)
    ctx.modul.used_data ctx.modul.data idx;
  Sequence.get ctx.modul.diagnostics ctx.modul.data idx

let get_elem ctx idx =
  mark_reference ctx.modul
    (fun i -> Ref_elem i)
    ctx.modul.used_elem ctx.modul.elem idx;
  Sequence.get ctx.modul.diagnostics ctx.modul.elem idx

(* Pop a memory/table address operand, whose width follows the address type. *)
let pop_address ctx loc limits =
  pop_known ctx loc (address_type_to_valtype limits.address_type)

(*** The instruction validator ***)

(* The usage flag to give a block form's control frame(s). A named label is also
   recorded in [ctx.label_decls] so an un-branched-to one can be reported once
   the body is validated; the same flag is shared across an [if]'s two arms and a
   [try]'s several bodies, which reuse one source label. *)
let track_label ctx label =
  let used = ref false in
  Option.iter
    (fun l -> ctx.label_decls := (l, used) :: !(ctx.label_decls))
    label;
  used

(* Branch-hinting proposal: a hint is advisory and has no stack effect, but it is
   only meaningful on a conditional branch — [if], [br_if] or a [br_on_*], reached
   through a folded head. Reject it anywhere else, matching the Wax typer; the
   text and binary front ends both attach a hint wherever it was written and leave
   the placement to be diagnosed here. *)
let rec is_branch_hint_target (d : _ Ast.Text.instr_desc) =
  match d with
  | If _ | Br_if _ | Br_on_null _ | Br_on_non_null _ | Br_on_cast _
  | Br_on_cast_fail _ | Br_on_cast_desc_eq _ | Br_on_cast_desc_eq_fail _ ->
      true
  | Folded (b, _) -> is_branch_hint_target b.desc
  | _ -> false

(* Compilation-hints proposal: an instruction frequency guides inlining, loop
   unrolling and block deferral, so the proposal expects it on a call or a control
   instruction. Anything else it defines as ignored; reject it instead, so a
   toolchain emitting a useless hint hears about it. *)
let rec is_instr_freq_target (d : _ Ast.Text.instr_desc) =
  match d with
  | Call _ | CallRef _ | CallIndirect _ | ReturnCall _ | ReturnCallRef _
  | ReturnCallIndirect _ | Block _ | Loop _ | If _ | TryTable _ | Try _ ->
      true
  | _ -> is_branch_hint_target d

(* A call target only means anything where the callee is not already known. *)
and is_call_targets_target (d : _ Ast.Text.instr_desc) =
  match d with
  | CallRef _ | CallIndirect _ | ReturnCallRef _ | ReturnCallIndirect _ -> true
  | Folded (b, _) -> is_call_targets_target b.desc
  | _ -> false

let check_hints ctx (i : _ Ast.Text.instr) =
  let hints = i.hints in
  (match hints.Hints.branch with
  | Some h when not (is_branch_hint_target i.desc) ->
      Error.branch_hint_invalid_target ctx.modul.diagnostics
        ~location:h.Hints.loc
  | _ -> ());
  (match hints.Hints.freq with
  | Some h when not (is_instr_freq_target i.desc) ->
      Error.instr_freq_invalid_target ctx.modul.diagnostics
        ~location:h.Hints.loc
  | _ -> ());
  match hints.Hints.targets with
  | None -> ()
  | Some h ->
      if not (is_call_targets_target i.desc) then
        Error.call_targets_invalid_target ctx.modul.diagnostics
          ~location:h.Hints.loc;
      (* Resolve each target so an unbound name is reported, but *without* marking
         the function used: naming one in advisory metadata is not a use, so it
         must not keep an otherwise-dead function out of the unused-field lint. *)
      List.iter
        (fun (idx, _) ->
          ignore (Sequence.get ctx.modul.diagnostics ctx.modul.functions idx))
        h.Hints.value;
      (* The proposal requires the listed frequencies to total at most 100%. *)
      let total =
        List.fold_left (fun acc (_, pct) -> acc + pct) 0 h.Hints.value
      in
      if total > 100 then
        Error.call_targets_over_100 ctx.modul.diagnostics ~location:h.Hints.loc
          ~total

let rec instruction_core ctx (i : _ Ast.Text.instr) =
  if false then print_instr i;
  let loc = i.info in
  check_hints ctx i;
  match i.desc with
  | Block { label; typ; block = b } ->
      let*! params, results, param_source, result_source = blocktype ctx typ in
      let* () = pop_args ctx (loc_first_char loc) ~source:param_source params in
      let used = track_label ctx label in
      block ctx loc label ~used ~param_source ~result_source
        ~br_source:result_source ~params ~results ~br_params:results b.desc;
      push_results ~loc ~source:result_source results
  | Loop { label; typ; block = b } ->
      let*! params, results, param_source, result_source = blocktype ctx typ in
      let* () = pop_args ctx (loc_first_char loc) ~source:param_source params in
      let used = track_label ctx label in
      block ctx loc label ~used ~param_source ~result_source
        ~br_source:param_source ~params ~results ~br_params:params b.desc;
      push_results ~loc ~source:result_source results
  | If { label; typ; if_block; else_block } ->
      let*! params, results, param_source, result_source = blocktype ctx typ in
      let loc_start = loc_first_char loc in
      let* () = pop_known ctx loc_start I32 in
      let* () = pop_args ctx loc_start ~source:param_source params in
      let used = track_label ctx label in
      (* Anchor each arm's stack-shape reports (a missing result, leftover
         values) at that arm, not at the whole [if] — otherwise the two arms'
         reports are indistinguishable. A synthesized arm (an omitted [else])
         has no span of its own; fall back to the instruction's. *)
      let arm_loc (b : (_, Ast.location) Ast.annotated) =
        if b.Ast.info.loc_start.Lexing.pos_cnum >= 0 then b.Ast.info else loc
      in
      block ctx (arm_loc if_block) label ~used ~param_source ~result_source
        ~br_source:result_source ~params ~results ~br_params:results
        if_block.desc;
      block ctx (arm_loc else_block) label ~used ~param_source ~result_source
        ~br_source:result_source ~params ~results ~br_params:results
        else_block.desc;
      push_results ~loc ~source:result_source results
  | TryTable { label; typ; block = b; catches } ->
      let*! params, results, param_source, result_source = blocktype ctx typ in
      let* () = pop_args ctx (loc_first_char loc) ~source:param_source params in
      let used = track_label ctx label in
      block ctx loc label ~used ~param_source ~result_source
        ~br_source:result_source ~params ~results ~br_params:results b.desc;
      List.iter
        (fun (catch : Ast.Text.catch) ->
          match catch with
          | Catch (tag, label) ->
              let*? args, arg_source = lookup_tag_type ctx tag in
              let*? params, param_source = branch_target ctx label in
              compare_types ctx.modul ~location:tag.info
                ~descr:"this exception handler" ~provided_source:arg_source
                ~expected_source:param_source ~provided:args ~expected:params ()
          | CatchRef (tag, label) ->
              let*? args, arg_source = lookup_tag_type ctx tag in
              let*? params, param_source = branch_target ctx label in
              let provided =
                Array.append args [| Ref { nullable = false; typ = Exn } |]
              in
              let provided_source =
                Array.append arg_source
                  [| Plain (Ref { nullable = false; typ = Exn }) |]
              in
              compare_types ctx.modul ~location:tag.info
                ~descr:"this exception handler" ~provided_source
                ~expected_source:param_source ~provided ~expected:params ()
          | CatchAll label ->
              Option.iter
                (fun (params, param_source) ->
                  compare_types ctx.modul ~location:label.info
                    ~descr:"this exception handler" ~provided_source:[||]
                    ~expected_source:param_source ~provided:[||]
                    ~expected:params ())
                (branch_target ctx label)
          | CatchAllRef label ->
              Option.iter
                (fun (params, param_source) ->
                  compare_types ctx.modul ~location:label.info
                    ~descr:"this exception handler"
                    ~provided_source:
                      [| Plain (Ref { nullable = false; typ = Exn }) |]
                    ~expected_source:param_source
                    ~provided:[| Ref { nullable = false; typ = Exn } |]
                    ~expected:params ())
                (branch_target ctx label))
        catches;
      push_results ~loc ~source:result_source results
  | Try { label; typ; block = b; catches; catch_all } ->
      let*! params, results, param_source, result_source = blocktype ctx typ in
      let* () = pop_args ctx (loc_first_char loc) ~source:param_source params in
      let used = track_label ctx label in
      block ctx loc label ~used ~param_source ~result_source
        ~br_source:result_source ~params ~results ~br_params:results b.desc;
      List.iter
        (fun (tag, b) ->
          let*? params', param_source = lookup_tag_type ctx tag in
          block ctx loc label ~used ~param_source ~result_source
            ~br_source:result_source ~params:params' ~results ~br_params:results
            b.Ast.desc)
        catches;
      Option.iter
        (fun b ->
          block ctx loc label ~used ~param_source ~result_source
            ~br_source:result_source ~params ~results ~br_params:results
            b.Ast.desc)
        catch_all;
      push_results ~loc ~source:result_source results
  | Unreachable -> unreachable
  | Nop -> return ()
  | Throw idx ->
      let*! params, param_source = lookup_tag_type ctx idx in
      let* () = pop_args ctx loc ~source:param_source params in
      unreachable
  | ThrowRef ->
      let* () = pop_known ctx loc (Ref { nullable = true; typ = Exn }) in
      unreachable
  | ContNew x ->
      let*! ty, ft, _ = lookup_cont_type ctx x in
      let func_source =
        match reference_comptype ctx.modul.types x with
        | Cont r -> named_ref_null_source r
        | _ -> assert false
      in
      let* () =
        pop ctx loc ~expected_source:func_source
          (Ref { nullable = true; typ = Type ft })
      in
      push ~source:(exact_ref_source ctx x) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | ContBind (x, y) ->
      let*! xty, _, ftx = lookup_cont_type ctx x in
      let*! yty, _, fty = lookup_cont_type ctx y in
      let n1 = Array.length ftx.params in
      let n1' = Array.length fty.params in
      if n1 < n1' then (
        Error.stack_switching_type_mismatch ctx.modul.diagnostics ~location:loc
          ~descr:
            "the resulting continuation takes more parameters than the \
             original one";
        unreachable)
      else begin
        let ts11 = Array.sub ftx.params 0 (n1 - n1') in
        let ts12 = Array.sub ftx.params (n1 - n1') n1' in
        if
          not
            (functype_matches ctx.modul.subtyping_info
               { params = ts12; results = ftx.results }
               fty)
        then (
          Error.stack_switching_type_mismatch ctx.modul.diagnostics
            ~location:loc
            ~descr:
              "the bound parameters and results do not match between the two \
               continuation types";
          unreachable)
        else begin
          let* () =
            pop_args ctx loc
              ~source:
                (cont_operand_source
                   (Array.sub (cont_param_source ctx x) 0 (n1 - n1'))
                   x)
              (Array.append ts11 [| Ref { nullable = true; typ = Type xty } |])
          in
          push ~source:(exact_ref_source ctx y) (Some loc)
            (Ref
               {
                 nullable = false;
                 typ = (if allocation_is_exact ctx then Exact yty else Type yty);
               })
        end
      end
  | Suspend x ->
      let*! { params = ts1; results = ts2 }, sign =
        lookup_tag_signature ctx x
      in
      let param_source, result_source = functype_sources sign in
      let* () = pop_args ctx loc ~source:param_source ts1 in
      push_results ~loc ~source:result_source ts2
  | Resume (x, clauses) ->
      let*! xty, _, ftx = lookup_cont_type ctx x in
      check_resume_table ctx loc ftx.results clauses;
      let _, result_source =
        functype_sources (cont_source_functype ctx.modul.types x)
      in
      let* () =
        pop_args ctx loc
          ~source:(cont_operand_source (cont_param_source ctx x) x)
          (Array.append ftx.params
             [| Ref { nullable = true; typ = Type xty } |])
      in
      push_results ~loc ~source:result_source ftx.results
  | ResumeThrow (x, y, clauses) ->
      let*! xty, _, ftx = lookup_cont_type ctx x in
      let*! { params = ts0; _ }, sign = lookup_tag_signature ctx y in
      check_resume_table ctx loc ftx.results clauses;
      let _, result_source =
        functype_sources (cont_source_functype ctx.modul.types x)
      in
      let* () =
        pop_args ctx loc
          ~source:(cont_operand_source (fst (functype_sources sign)) x)
          (Array.append ts0 [| Ref { nullable = true; typ = Type xty } |])
      in
      push_results ~loc ~source:result_source ftx.results
  | ResumeThrowRef (x, clauses) ->
      let*! xty, _, ftx = lookup_cont_type ctx x in
      check_resume_table ctx loc ftx.results clauses;
      let _, result_source =
        functype_sources (cont_source_functype ctx.modul.types x)
      in
      let* () =
        pop_args ctx loc
          ~source:
            [|
              Plain (Ref { nullable = true; typ = Exn });
              named_ref_null_source x;
            |]
          [|
            Ref { nullable = true; typ = Exn };
            Ref { nullable = true; typ = Type xty };
          |]
      in
      push_results ~loc ~source:result_source ftx.results
  | Switch (x, y) ->
      let*! xty, _, ftx = lookup_cont_type ctx x in
      let ts11 = ftx.params in
      let n = Array.length ts11 in
      let inner =
        match if n = 0 then None else Some ts11.(n - 1) with
        | Some (Ref { typ = ht; _ }) -> cont_functype_of_heaptype ctx ht
        | _ -> None
      in
      let*! inner_ft =
        match inner with
        | Some _ -> inner
        | None ->
            Error.stack_switching_type_mismatch ctx.modul.diagnostics
              ~location:loc
              ~descr:
                "the continuation's last parameter must itself be a \
                 continuation type";
            None
      in
      let*! { params = ts31; results = t }, _ = lookup_tag_signature ctx y in
      let info = ctx.modul.subtyping_info in
      if
        Array.length ts31 <> 0
        || (not (result_subtype info ftx.results t))
        || not (result_subtype info t inner_ft.results)
      then (
        Error.stack_switching_type_mismatch ctx.modul.diagnostics ~location:loc
          ~descr:
            "the 'switch' tag must take no parameters and its results must \
             match the two continuation types";
        unreachable)
      else begin
        (* The inner continuation is named by [x]'s last parameter, so its
           parameters' source types are that continuation's source params. *)
        let ts21 = inner_ft.params in
        let ts21_text =
          (* [inner] is [Some] only when [x]'s last parameter is a concrete
             continuation reference, so its source form is [(ref $idx)] or
             [(ref (exact $idx))] — [cont_functype_of_heaptype] accepts both, so
             the exactness does not change which type's params are looked up. *)
          match (cont_param_source ctx x).(n - 1) with
          | Plain (Ref { typ = Type idx | Exact idx; _ }) ->
              cont_param_source ctx idx
          | _ -> assert false
        in
        let ts11' = Array.sub ts11 0 (n - 1) in
        let ts11'_text = Array.sub (cont_param_source ctx x) 0 (n - 1) in
        let* () =
          pop_args ctx loc
            ~source:(cont_operand_source ts11'_text x)
            (Array.append ts11' [| Ref { nullable = true; typ = Type xty } |])
        in
        push_results ~loc ~source:ts21_text ts21
      end
  | Br idx ->
      let*! params, param_source = branch_target ctx idx in
      let* () = pop_args ctx loc ~source:param_source params in
      unreachable
  | Br_if idx ->
      let* () = pop_known ctx loc I32 in
      let*! params, param_source = branch_target ctx idx in
      let* () = pop_args ctx loc ~source:param_source params in
      push_results ~sink:false ~loc ~source:param_source params
  | Br_table (lst, idx) ->
      let* () = pop_known ctx loc I32 in
      let*! params, _ = branch_target ctx idx in
      let len = Array.length params in
      let* () =
        with_current_stack (fun st ->
            (* Check each DISTINCT target once: the check is purely per-target,
               so a target repeated in the list — spelled by depth or by a
               label name resolving to that same depth — would only repeat an
               identical report. Unresolved targets are not deduplicated; each
               occurrence reports its own unbound label at its own span. *)
            let seen = Hashtbl.create 8 in
            let repeated (idx' : Ast.Text.idx) =
              let depth =
                match idx'.desc with
                | Num i -> Some (Uint32.to_int i)
                | Id id ->
                    let rec find n = function
                      | [] -> None
                      | (Some id', _, _, _) :: _ when id = id' -> Some n
                      | _ :: rem -> find (n + 1) rem
                    in
                    find 0 ctx.control_types
              in
              match depth with
              | None -> false
              | Some d ->
                  Hashtbl.mem seen d
                  ||
                  (Hashtbl.add seen d ();
                   false)
            in
            (* Two DISTINCT targets can still impose the SAME types on the same
               values, and then their reports are anchored identically too — a
               present value's report points at where that value was pushed, not
               at the label — so the second would print as one repeated
               [line:col: message]. Key the value check on the requirement, not
               the target: distinct types still report, once each. *)
            let checked = ref [] in
            let requirement_checked params =
              let same p =
                Array.length p = Array.length params
                && Array.for_all2
                     (fun a b ->
                       Types.val_subtype ctx.modul.subtyping_info a b
                       && Types.val_subtype ctx.modul.subtyping_info b a)
                     p params
              in
              List.exists same !checked
              ||
              (checked := params :: !checked;
               false)
            in
            List.iter
              (fun idx' ->
                if not (repeated idx') then
                  let*? params, param_source = branch_target ctx idx' in
                  let len' = Array.length params in
                  if len <> len' then
                    Error.branch_parameter_count_mismatch ctx.modul.diagnostics
                      ~location:idx'.Ast.info ~default_loc:idx.Ast.info idx len
                      idx' len'
                    (* Blame the LABEL, not the instruction, as the arity report
                       above already does: the requirement is that target's, and
                       two targets demanding the same missing value would
                       otherwise print as one repeated [line:col: message]. *)
                  else if not (requirement_checked params) then
                    ignore
                      (pop_args ctx idx'.Ast.info ~source:param_source params st))
              (* In source order — the default target is written last — so the
                 per-label reports come out in the order they are read. *)
              (lst @ [ idx ]))
      in
      unreachable
  | Br_on_null idx -> (
      let* ty, loc' = pop_any ctx loc in
      (* The branch carries the label's parameters; the value falls through with
         its null case removed ([(ref bot)] when the operand was a bottom). *)
      let fallthrough push_top =
        let*! params, param_source = branch_target ctx idx in
        let* () = pop_args ctx loc ~source:param_source params in
        let* () = push_results ~sink:false ~loc ~source:param_source params in
        push_top
      in
      match ty with
      | Bot | Bot_ref -> fallthrough (push_bot_ref (Some loc))
      | Val (Ref { nullable = _; typ }, source) ->
          fallthrough
            (push ~source:(non_null_source source) (Some loc)
               (Ref { nullable = false; typ }))
      | Val (_, source) ->
          Error.expected_ref_type ctx.modul.diagnostics ~location:loc
            ~src_loc:loc' ~source;
          unreachable)
  | Br_on_non_null idx -> (
      let* ty, loc' = pop_any ctx loc in
      (* The branch carries the label's parameters ending in the non-null
         reference ([(ref bot)] for a bottom operand); the value is consumed on
         fall-through. *)
      let to_branch push_ref =
        let* () = push_ref in
        let*! params, param_source = branch_target ctx idx in
        (* [br_on_non_null] requires the target label to be [t* (ref ht)]: the
           pushed non-null reference is consumed by that trailing type. An empty
           label has no such type, so [pop_args] would silently accept it. *)
        if Array.length params = 0 then (
          Error.br_on_non_null_no_ref ctx.modul.diagnostics ~location:loc;
          unreachable)
        else
          let* () = pop_args ctx loc ~source:param_source params in
          let* () = push_results ~sink:false ~loc ~source:param_source params in
          let* _ = pop_any ctx loc in
          return ()
      in
      match ty with
      | Bot | Bot_ref -> to_branch (push_bot_ref None)
      | Val (Ref { nullable = _; typ }, source) ->
          to_branch
            (push ~source:(non_null_source source) None
               (Ref { nullable = false; typ }))
      | Val (_, source) ->
          Error.expected_ref_type ctx.modul.diagnostics ~location:loc
            ~src_loc:loc' ~source;
          unreachable)
  | Br_on_cast (idx, ty1, ty2) ->
      let src_ty1 = Plain (Ast.Text.Ref ty1)
      and src_ty2 = Plain (Ast.Text.Ref ty2) in
      (* The value that falls through has [ty1]'s heap type, non-null once a
         nullable [ty2] has consumed the null case. *)
      let src_diff =
        Plain
          (Ast.Text.Ref
             { nullable = ty1.nullable && not ty2.nullable; typ = ty1.typ })
      in
      let*! ty1 = reftype ctx.modul.diagnostics ctx.modul.types ty1 in
      let*! ty2 = reftype ctx.modul.diagnostics ctx.modul.types ty2 in
      (match (top_heap_type ctx ty1.typ, top_heap_type ctx ty2.typ) with
      | Cont, _ | _, Cont ->
          Error.invalid_cast_type ctx.modul.diagnostics ~location:loc
      | _ -> ());
      if not (br_cast_compatible ctx ty1 ty2) then
        Error.br_cast_type_mismatch ctx.modul.diagnostics ~location:loc;
      let* () = pop ctx loc ~expected_source:src_ty1 (Ref ty1) in
      let* () = push ~source:src_ty2 None (Ref ty2) in
      let*! params, param_source = branch_cast_target ctx idx ~location:loc in
      let* () = pop_args ctx loc ~source:param_source params in
      let* () = push_results ~sink:false ~loc ~source:param_source params in
      let* _ = pop_any ctx loc in
      push ~source:src_diff (Some loc) (Ref (diff_ref_type ty1 ty2))
  | Br_on_cast_fail (idx, ty1, ty2) ->
      let src_ty1 = Plain (Ast.Text.Ref ty1)
      and src_ty2 = Plain (Ast.Text.Ref ty2) in
      (* The value sent to the branch has [ty1]'s heap type, non-null once a
         nullable [ty2] has consumed the null case. *)
      let src_diff =
        Plain
          (Ast.Text.Ref
             { nullable = ty1.nullable && not ty2.nullable; typ = ty1.typ })
      in
      let*! ty1 = reftype ctx.modul.diagnostics ctx.modul.types ty1 in
      let*! ty2 = reftype ctx.modul.diagnostics ctx.modul.types ty2 in
      (match (top_heap_type ctx ty1.typ, top_heap_type ctx ty2.typ) with
      | Cont, _ | _, Cont ->
          Error.invalid_cast_type ctx.modul.diagnostics ~location:loc
      | _ -> ());
      if not (br_cast_compatible ctx ty1 ty2) then
        Error.br_cast_type_mismatch ctx.modul.diagnostics ~location:loc;
      let* () = pop ctx loc ~expected_source:src_ty1 (Ref ty1) in
      let* () = push ~source:src_diff None (Ref (diff_ref_type ty1 ty2)) in
      let*! params, param_source = branch_cast_target ctx idx ~location:loc in
      let* () = pop_args ctx loc ~source:param_source params in
      let* () = push_results ~sink:false ~loc ~source:param_source params in
      let* _ = pop_any ctx loc in
      push ~source:src_ty2 (Some loc) (Ref ty2)
  | Br_on_cast_desc_eq (idx, ty1, ty2) ->
      (* As [br_on_cast], preceded by consuming a descriptor operand whose
         exactness matches the target [ty2]. *)
      let src_ty1 = Plain (Ast.Text.Ref ty1)
      and src_ty2 = Plain (Ast.Text.Ref ty2) in
      let src_diff =
        Plain
          (Ast.Text.Ref
             { nullable = ty1.nullable && not ty2.nullable; typ = ty1.typ })
      in
      let*! ty1 = reftype ctx.modul.diagnostics ctx.modul.types ty1 in
      let*! ty2 = reftype ctx.modul.diagnostics ctx.modul.types ty2 in
      (match (top_heap_type ctx ty1.typ, top_heap_type ctx ty2.typ) with
      | Cont, _ | _, Cont ->
          Error.invalid_cast_type ctx.modul.diagnostics ~location:loc
      | _ -> ());
      if not (br_cast_compatible ctx ty1 ty2) then
        Error.br_cast_type_mismatch ctx.modul.diagnostics ~location:loc;
      let*! desc_ht = descriptor_operand_type ctx ~location:loc ty2.typ in
      let* () =
        pop ctx loc
          ~expected_source:(descriptor_operand_source ctx.modul.types ty2.typ)
          (Ref { nullable = true; typ = desc_ht })
      in
      let* () = pop ctx loc ~expected_source:src_ty1 (Ref ty1) in
      let* () = push ~source:src_ty2 None (Ref ty2) in
      let*! params, param_source = branch_cast_target ctx idx ~location:loc in
      let* () = pop_args ctx loc ~source:param_source params in
      let* () = push_results ~sink:false ~loc ~source:param_source params in
      let* _ = pop_any ctx loc in
      push ~source:src_diff (Some loc) (Ref (diff_ref_type ty1 ty2))
  | Br_on_cast_desc_eq_fail (idx, ty1, ty2) ->
      let src_ty1 = Plain (Ast.Text.Ref ty1)
      and src_ty2 = Plain (Ast.Text.Ref ty2) in
      let src_diff =
        Plain
          (Ast.Text.Ref
             { nullable = ty1.nullable && not ty2.nullable; typ = ty1.typ })
      in
      let*! ty1 = reftype ctx.modul.diagnostics ctx.modul.types ty1 in
      let*! ty2 = reftype ctx.modul.diagnostics ctx.modul.types ty2 in
      (match (top_heap_type ctx ty1.typ, top_heap_type ctx ty2.typ) with
      | Cont, _ | _, Cont ->
          Error.invalid_cast_type ctx.modul.diagnostics ~location:loc
      | _ -> ());
      if not (br_cast_compatible ctx ty1 ty2) then
        Error.br_cast_type_mismatch ctx.modul.diagnostics ~location:loc;
      let*! desc_ht = descriptor_operand_type ctx ~location:loc ty2.typ in
      let* () =
        pop ctx loc
          ~expected_source:(descriptor_operand_source ctx.modul.types ty2.typ)
          (Ref { nullable = true; typ = desc_ht })
      in
      let* () = pop ctx loc ~expected_source:src_ty1 (Ref ty1) in
      let* () = push ~source:src_diff None (Ref (diff_ref_type ty1 ty2)) in
      let*! params, param_source = branch_cast_target ctx idx ~location:loc in
      let* () = pop_args ctx loc ~source:param_source params in
      let* () = push_results ~sink:false ~loc ~source:param_source params in
      let* _ = pop_any ctx loc in
      push ~source:src_ty2 (Some loc) (Ref ty2)
  | Return ->
      let* () =
        pop_args ctx ~kind:`Output loc ~source:ctx.return_source
          ctx.return_types
      in
      unreachable
  | Call idx -> (
      let*! ty, _, sign, _ = get_function ctx idx in
      match (Types.get_subtype ctx.modul.subtyping_info ty).typ with
      | Struct _ | Array _ | Cont _ ->
          Error.expected_func_type ctx.modul.diagnostics ~location:loc idx;
          unreachable
      | Func { params; results } ->
          let param_source, result_source = functype_sources sign in
          (* Give the callee identifier the function's signature on hover. *)
          record (Some idx.info) (Signature (param_source, result_source));
          let* () = pop_args ctx loc ~source:param_source params in
          push_results ~loc ~source:result_source results)
  | CallRef idx ->
      let*! type_idx, { params; results } = lookup_func_type ctx idx in
      let param_source, result_source =
        functype_sources (reference_functype ctx.modul.types idx)
      in
      let* () =
        pop ctx loc
          ~expected_source:(named_ref_null_source idx)
          (Ref { nullable = true; typ = Type type_idx })
      in
      let* () = pop_args ctx loc ~source:param_source params in
      push_results ~loc ~source:result_source results
  | CallIndirect (idx, tu) -> (
      let*! typ, table_source = get_table ctx idx in
      let*! ty = typeuse ctx.modul.diagnostics ctx.modul.types tu in
      if
        not
          (Types.val_subtype ctx.modul.subtyping_info (Ref typ.reftype)
             (Ref { nullable = true; typ = Func }))
      then (
        Error.table_type_mismatch ctx.modul.diagnostics ~location:loc
          ~source:table_source idx;
        unreachable)
      else
        match (Types.get_subtype ctx.modul.subtyping_info ty).typ with
        | Struct _ | Array _ | Cont _ ->
            Error.expected_func_type ctx.modul.diagnostics ~location:loc idx;
            unreachable
        | Func { params; results } ->
            let param_source, result_source =
              functype_sources (typeuse_functype ctx.modul.types tu)
            in
            let* () = pop_address ctx loc typ.limits in
            let* () = pop_args ctx loc ~source:param_source params in
            push_results ~loc ~source:result_source results)
  | ReturnCall idx -> (
      let*! ty, _, sign, _ = get_function ctx idx in
      match (Types.get_subtype ctx.modul.subtyping_info ty).typ with
      | Struct _ | Array _ | Cont _ ->
          Error.expected_func_type ctx.modul.diagnostics ~location:loc idx;
          unreachable
      | Func { params; results } ->
          let param_source, result_source = functype_sources sign in
          record (Some idx.info) (Signature (param_source, result_source));
          let* () = pop_args ctx loc ~source:param_source params in
          compare_types ctx.modul ~location:idx.info ~descr:"this tail call"
            ~provided_source:result_source ~expected_source:ctx.return_source
            ~provided:results ~expected:ctx.return_types ();
          unreachable)
  | ReturnCallRef idx ->
      let*! type_idx, { params; results } = lookup_func_type ctx idx in
      let param_source, result_source =
        functype_sources (reference_functype ctx.modul.types idx)
      in
      let* () =
        pop ctx loc
          ~expected_source:(named_ref_null_source idx)
          (Ref { nullable = true; typ = Type type_idx })
      in
      let* () = pop_args ctx loc ~source:param_source params in
      compare_types ctx.modul ~location:idx.info ~descr:"this tail call"
        ~provided_source:result_source ~expected_source:ctx.return_source
        ~provided:results ~expected:ctx.return_types ();
      unreachable
  | ReturnCallIndirect (idx, tu) -> (
      let*! typ, table_source = get_table ctx idx in
      let*! ty = typeuse ctx.modul.diagnostics ctx.modul.types tu in
      if
        not
          (Types.val_subtype ctx.modul.subtyping_info (Ref typ.reftype)
             (Ref { nullable = true; typ = Func }))
      then (
        Error.table_type_mismatch ctx.modul.diagnostics ~location:loc
          ~source:table_source idx;
        unreachable)
      else
        match (Types.get_subtype ctx.modul.subtyping_info ty).typ with
        | Struct _ | Array _ | Cont _ ->
            Error.expected_func_type ctx.modul.diagnostics ~location:loc idx;
            unreachable
        | Func { params; results } ->
            let param_source, result_source =
              functype_sources (typeuse_functype ctx.modul.types tu)
            in
            let* () = pop_address ctx loc typ.limits in
            let* () = pop_args ctx loc ~source:param_source params in
            (* Anchor at the typeuse's type index (the callee type as written)
               when there is one; an inline-only typeuse keeps the whole
               instruction. *)
            compare_types ctx.modul
              ~location:
                (match fst tu with Some tidx -> tidx.Ast.info | None -> loc)
              ~descr:"this tail call" ~provided_source:result_source
              ~expected_source:ctx.return_source ~provided:results
              ~expected:ctx.return_types ();
            unreachable)
  | Drop ->
      let* _ = pop_any ctx loc in
      return ()
  | Select None -> (
      let* () = pop_known ctx loc I32 in
      let* ty1, loc1 = pop_any ctx loc in
      let* ty2, loc2 = pop_any ctx loc in
      (* A bare [select] forbids reference operands; the bottom reference, like
         any reference, is rejected here. Each operand reduces to its value
         ([None] when unknown), so the cases below mirror the operand stack.
         Each report is anchored at its operand's push location (when known),
         so the two operands' reports stay distinguishable. *)
      let as_operand src_loc = function
        | Bot -> None
        | Bot_ref ->
            Error.expected_number_or_vec ctx.modul.diagnostics ~location:loc
              ~src_loc ~source:Bottom_ref;
            None
        | Val (ty, source) -> Some (ty, source)
      in
      match (as_operand loc1 ty1, as_operand loc2 ty2) with
      | None, None -> push_poly loc
      | Some (ty1, source1), Some (ty2, source2) ->
          if not (number_or_vec ty1) then
            Error.expected_number_or_vec ctx.modul.diagnostics ~location:loc
              ~src_loc:loc1 ~source:source1;
          if not (number_or_vec ty2) then
            Error.expected_number_or_vec ctx.modul.diagnostics ~location:loc
              ~src_loc:loc2 ~source:source2;
          if ty1 <> ty2 then
            Error.select_type_mismatch ctx.modul.diagnostics ~location:loc ~loc1
              ~source1 ~loc2 ~source2;
          push ~source:source1 (Some loc) ty1
      | Some (ty, source), None ->
          if not (number_or_vec ty) then
            Error.expected_number_or_vec ctx.modul.diagnostics ~location:loc
              ~src_loc:loc1 ~source;
          push ~source (Some loc) ty
      | None, Some (ty, source) ->
          if not (number_or_vec ty) then
            Error.expected_number_or_vec ctx.modul.diagnostics ~location:loc
              ~src_loc:loc2 ~source;
          push ~source (Some loc) ty)
  | Select (Some lst) -> (
      match lst with
      | [ typ ] ->
          let src_typ = Plain typ in
          let*! typ = valtype ctx.modul.diagnostics ctx.modul.types typ in
          let* () = pop_known ctx loc I32 in
          let* () = pop ctx loc ~expected_source:src_typ typ in
          let* () = pop ctx loc ~expected_source:src_typ typ in
          push ~source:src_typ (Some loc) typ
      | _ ->
          Error.select_result_count ctx.modul.diagnostics ~location:loc;
          pop_known ctx loc I32)
  | LocalGet i ->
      let*! ty, source = get_local ctx i in
      (* A poisoned local (unresolved declared type) pushes the bottom reference
         rather than the recovery dummy, so a consumer does not report a second
         mismatch against it. *)
      if local_is_poisoned ctx i then push_bot_ref (Some loc)
      else push ~source (Some loc) ty
  | LocalSet i ->
      let*! ty, source = get_local ~initialize:true ctx i in
      (* Give the identifier the local's type, so hover over [$x] shows it even
         though [local.set] itself leaves nothing on the stack. *)
      record (Some i.info) (Pushed source);
      if local_is_poisoned ctx i then
        let* _ = pop_any ctx loc in
        return ()
      else pop ctx loc ~expected_source:source ty
  | LocalTee i ->
      let*! ty, source = get_local ~initialize:true ctx i in
      record (Some i.info) (Pushed source);
      if local_is_poisoned ctx i then
        let* _ = pop_any ctx loc in
        push_bot_ref (Some loc)
      else
        let* () = pop ctx loc ~expected_source:source ty in
        push ~source (Some loc) ty
  | GlobalGet idx ->
      let*! ty, source = get_global ctx idx in
      push ~source (Some loc) ty.typ
  | GlobalSet idx ->
      let*! ty, source = get_global ctx idx in
      (* The single [global.set] site, so it is also where a mutable global is
         recorded as actually assigned (for [unnecessary-mut]). *)
      mark_index ctx.modul.assigned_globals ctx.modul.globals idx;
      record (Some idx.info) (Pushed source);
      if not ty.mut then
        Error.immutable_global ctx.modul.diagnostics ~location:loc idx;
      pop ctx loc ~expected_source:source ty.typ
  | Load (idx, memarg, ty) ->
      let*! limits = get_memory ctx idx in
      let ty, sz = memory_instruction_type_and_size ty in
      check_memarg ctx loc limits sz memarg;
      let* () = pop_address ctx loc limits in
      push ~source:(source_of_valtype ty) (Some loc) ty
  | LoadS (idx, memarg, ty, sz, _) ->
      let*! limits = get_memory ctx idx in
      let ty = match ty with `I32 -> I32 | `I64 -> I64 in
      check_memarg ctx loc limits
        (sz :> [ `I8 | `I16 | `I32 | `I64 | `V128 ])
        memarg;
      let* () = pop_address ctx loc limits in
      push ~source:(source_of_valtype ty) (Some loc) ty
  | Store (idx, memarg, ty) ->
      let*! limits = get_memory ctx idx in
      let ty, sz = memory_instruction_type_and_size ty in
      check_memarg ctx loc limits sz memarg;
      let* () = pop_known ctx loc ty in
      let* () = pop_address ctx loc limits in
      return ()
  | StoreS (idx, memarg, ty, sz) ->
      let*! limits = get_memory ctx idx in
      let ty = match ty with `I32 -> I32 | `I64 -> I64 in
      check_memarg ctx loc limits
        (sz :> [ `I8 | `I16 | `I32 | `I64 | `V128 ])
        memarg;
      let* () = pop_known ctx loc ty in
      pop_address ctx loc limits
  | Atomic (idx, op, memarg) ->
      let*! limits = get_memory ctx idx in
      check_atomic_memarg ctx loc limits op memarg;
      let vt = function `I32 -> I32 | `I64 -> I64 in
      let operands, results = Atomics.signature op in
      (* Operands sit above the address, topmost last, so pop in reverse. *)
      let* () =
        List.fold_left
          (fun acc t ->
            let* () = acc in
            pop_known ctx loc (vt t))
          (return ()) (List.rev operands)
      in
      let* () = pop_address ctx loc limits in
      List.fold_left
        (fun acc t ->
          let* () = acc in
          push_known (Some loc) (vt t))
        (return ()) results
  | AtomicFence -> return ()
  | MemorySize idx ->
      let*! limits = get_memory ctx idx in
      let ty = address_type_to_valtype limits.address_type in
      push ~source:(source_of_valtype ty) (Some loc) ty
  | MemoryGrow idx ->
      let*! limits = get_memory ctx idx in
      let addr_ty = address_type_to_valtype limits.address_type in
      let* () = pop_known ctx loc addr_ty in
      push ~source:(source_of_valtype addr_ty) (Some loc) addr_ty
  | MemoryFill idx ->
      let*! limits = get_memory ctx idx in
      let addr_ty = address_type_to_valtype limits.address_type in
      let* () = pop_known ctx loc addr_ty in
      let* () = pop_known ctx loc I32 in
      pop_known ctx loc addr_ty
  | MemoryCopy (idx, idx') ->
      let*! limits = get_memory ctx idx in
      let*! limits' = get_memory ctx idx' in
      (* The length operand uses the smaller of the two address types: i32 if
         either memory is 32-bit, i64 only if both are 64-bit. *)
      let address_type =
        match (limits.address_type, limits'.address_type) with
        | `I32, _ | _, `I32 -> `I32
        | `I64, `I64 -> `I64
      in
      let addr_ty = address_type_to_valtype limits.address_type in
      let addr_ty' = address_type_to_valtype limits'.address_type in
      let addr_ty'' = address_type_to_valtype address_type in
      let* () = pop_known ctx loc addr_ty'' in
      let* () = pop_known ctx loc addr_ty' in
      pop_known ctx loc addr_ty
  | MemoryInit (idx, idx') ->
      let*! limits = get_memory ctx idx in
      ignore (get_data ctx idx');
      let addr_ty = address_type_to_valtype limits.address_type in
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      pop_known ctx loc addr_ty
  | DataDrop idx ->
      ignore (get_data ctx idx);
      return ()
  | VecBinOp _ ->
      let* () = pop_known ctx loc V128 in
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) V128
  | VecConst _ -> push_known (Some loc) V128
  | VecUnOp _ ->
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) V128
  | VecTest _ ->
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) I32
  | VecShift _ ->
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) V128
  | VecBitmask _ ->
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) I32
  | VecTernOp _ ->
      let* () = pop_known ctx loc V128 in
      let* () = pop_known ctx loc V128 in
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) V128
  | VecBitselect ->
      let* () = pop_known ctx loc V128 in
      let* () = pop_known ctx loc V128 in
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) V128
  | VecSplat shape ->
      let ty = shape_type shape in
      let* () = pop_known ctx loc ty in
      push_known (Some loc) V128
  | VecLoad (idx, sz, memarg) ->
      let*! limits = get_memory ctx idx in
      check_memarg ctx loc limits
        (match sz with
        | Load128 -> `V128
        | Load8x8S | Load8x8U | Load16x4S | Load16x4U | Load32x2S | Load32x2U
        | Load64Zero ->
            `I64
        | Load32Zero -> `I32)
        memarg;
      let* () = pop_address ctx loc limits in
      push_known (Some loc) V128
  | VecStore (idx, memarg) ->
      let*! limits = get_memory ctx idx in
      check_memarg ctx loc limits `V128 memarg;
      let* () = pop_known ctx loc V128 in
      let* () = pop_address ctx loc limits in
      return ()
  | VecLoadLane (idx, op, mem, lane) ->
      let*! limits = get_memory ctx idx in
      check_memarg ctx loc limits
        (op :> [ `I8 | `I16 | `I32 | `I64 | `F32 | `F64 | `V128 ])
        mem;
      let sz = match op with `I8 -> 1 | `I16 -> 2 | `I32 -> 4 | `I64 -> 8 in
      if lane >= 16 / sz then
        Error.invalid_lane_index ctx.modul.diagnostics ~location:loc (16 / sz);
      let* () = pop_known ctx loc V128 in
      let* () = pop_address ctx loc limits in
      push_known (Some loc) V128
  | VecStoreLane (idx, op, mem, lane) ->
      let*! limits = get_memory ctx idx in
      check_memarg ctx loc limits
        (op :> [ `I8 | `I16 | `I32 | `I64 | `F32 | `F64 | `V128 ])
        mem;
      let sz = match op with `I8 -> 1 | `I16 -> 2 | `I32 -> 4 | `I64 -> 8 in
      if lane >= 16 / sz then
        Error.invalid_lane_index ctx.modul.diagnostics ~location:loc (16 / sz);
      let* () = pop_known ctx loc V128 in
      let* () = pop_address ctx loc limits in
      return ()
  | VecLoadSplat (idx, op, mem) ->
      let*! limits = get_memory ctx idx in
      check_memarg ctx loc limits
        (op :> [ `I8 | `I16 | `I32 | `I64 | `F32 | `F64 | `V128 ])
        mem;
      let* () = pop_address ctx loc limits in
      push_known (Some loc) V128
  | VecExtract (shape, _, lane) ->
      check_shape_lanes ctx loc shape lane;
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) (shape_type shape)
  | VecReplace (shape, lane) ->
      check_shape_lanes ctx loc shape lane;
      let* () = pop_known ctx loc (shape_type shape) in
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) V128
  | VecShuffle lanes ->
      if not (String.for_all (fun l -> Char.code l < 32) lanes) then
        Error.invalid_lane_index ctx.modul.diagnostics ~location:loc 32;
      let* () = pop_known ctx loc V128 in
      let* () = pop_known ctx loc V128 in
      push_known (Some loc) V128
  | TableGet idx ->
      let*! typ, source = get_table ctx idx in
      let addr_ty = address_type_to_valtype typ.limits.address_type in
      let* () = pop_known ctx loc addr_ty in
      push ~source (Some loc) (Ref typ.reftype)
  | TableSet idx ->
      let*! typ, source = get_table ctx idx in
      let addr_ty = address_type_to_valtype typ.limits.address_type in
      let* () = pop ctx loc ~expected_source:source (Ref typ.reftype) in
      pop_known ctx loc addr_ty
  | TableSize idx ->
      let*! typ, _ = get_table ctx idx in
      push_known (Some loc) (address_type_to_valtype typ.limits.address_type)
  | TableGrow idx ->
      let*! typ, source = get_table ctx idx in
      let addr_ty = address_type_to_valtype typ.limits.address_type in
      let* () = pop_known ctx loc addr_ty in
      let* () = pop ctx loc ~expected_source:source (Ref typ.reftype) in
      push_known (Some loc) addr_ty
  | TableFill idx ->
      let*! typ, source = get_table ctx idx in
      let addr_ty = address_type_to_valtype typ.limits.address_type in
      let* () = pop_known ctx loc addr_ty in
      let* () = pop ctx loc ~expected_source:source (Ref typ.reftype) in
      pop_known ctx loc addr_ty
  | TableCopy (idx, idx') ->
      let*! ty, dst_source = get_table ctx idx in
      let*! ty', src_source = get_table ctx idx' in
      if
        not
          (Types.val_subtype ctx.modul.subtyping_info (Ref ty'.reftype)
             (Ref ty.reftype))
      then
        Error.type_mismatch ctx.modul.diagnostics ~location:loc
          ~provided_source:src_source ~expected_source:dst_source;
      (* The length operand uses the smaller of the two address types: i32 if
         either table is 32-bit, i64 only if both are 64-bit. *)
      let address_type =
        match (ty.limits.address_type, ty'.limits.address_type) with
        | `I32, _ | _, `I32 -> `I32
        | `I64, `I64 -> `I64
      in
      let addr_ty = address_type_to_valtype ty.limits.address_type in
      let addr_ty' = address_type_to_valtype ty'.limits.address_type in
      let addr_ty'' = address_type_to_valtype address_type in
      let* () = pop_known ctx loc addr_ty'' in
      let* () = pop_known ctx loc addr_ty' in
      pop_known ctx loc addr_ty
  | TableInit (idx, idx') ->
      let*! tabletype, table_source = get_table ctx idx in
      let*! typ, elem_source = get_elem ctx idx' in
      if
        not
          (Types.val_subtype ctx.modul.subtyping_info (Ref typ)
             (Ref tabletype.reftype))
      then
        Error.type_mismatch ctx.modul.diagnostics ~location:loc
          ~provided_source:elem_source ~expected_source:table_source;
      let addr_ty = address_type_to_valtype tabletype.limits.address_type in
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      pop_known ctx loc addr_ty
  | ElemDrop idx ->
      let*! _ = get_elem ctx idx in
      return ()
  | RefNull typ ->
      let source = Plain Ast.Text.(Ref { nullable = true; typ }) in
      let*! typ = heaptype ctx.modul.diagnostics ctx.modul.types typ in
      push ~source (Some loc) (Ref { nullable = true; typ })
  | RefFunc idx ->
      let*! i, type_idx, sign, exact = get_function ctx idx in
      let param_source, result_source = functype_sources sign in
      record (Some idx.info) (Signature (param_source, result_source));
      if
        not
          ((not !validate_refs)
          || Hashtbl.mem ctx.modul.refs
               (Sequence.get_index ctx.modul.functions idx))
      then Error.ref_func_inaccessible ctx.modul.diagnostics ~location:loc idx;
      (* Name the function's type when it was declared with a named type,
         otherwise show the signature inline (a numeric index would be
         meaningless, as the interned index space is deduplicated). *)
      let source =
        match type_idx with
        | Some ({ desc = Id _; _ } as idx) ->
            (* Match the pushed internal type's exactness (below) so the source
               rendering agrees with it — but only when the exactness is
               expressible ([exact_ref_source] renders exact under
               custom-descriptors, plain otherwise). *)
            if exact then exact_ref_source ctx idx else named_ref_source idx
        | _ -> Inline_ref (Func sign)
      in
      push ~source (Some loc)
        (Ref { nullable = false; typ = (if exact then Exact i else Type i) })
  | RefIsNull -> (
      let* ty, loc' = pop_any ctx loc in
      match ty with
      | Bot | Bot_ref | Val (Ref _, _) -> push_known (Some loc) I32
      | Val (_, source) ->
          Error.expected_ref_type ctx.modul.diagnostics ~location:loc
            ~src_loc:loc' ~source;
          unreachable)
  | RefAsNonNull -> (
      let* ty, loc' = pop_any ctx loc in
      match ty with
      | Bot | Bot_ref -> push_bot_ref (Some loc)
      | Val (Ref ty, source) ->
          push ~source:(non_null_source source) (Some loc)
            (Ref { ty with nullable = false })
      | Val (_, source) ->
          Error.expected_ref_type ctx.modul.diagnostics ~location:loc
            ~src_loc:loc' ~source;
          unreachable)
  | RefEq ->
      let* () = pop_known ctx loc (Ref { nullable = true; typ = Eq }) in
      let* () = pop_known ctx loc (Ref { nullable = true; typ = Eq }) in
      push_known (Some loc) I32
  | RefTest ty ->
      let*! ty = reftype ctx.modul.diagnostics ctx.modul.types ty in
      (match top_heap_type ctx ty.typ with
      | Cont -> Error.invalid_cast_type ctx.modul.diagnostics ~location:loc
      | _ -> ());
      let* () = lint_cast ctx ~location:loc ~is_test:true ty in
      let* () =
        pop_known ctx loc
          (Ref { nullable = true; typ = top_heap_type ctx ty.typ })
      in
      push_known (Some loc) I32
  | RefCast ty ->
      let source = Plain Ast.Text.(Ref ty) in
      let*! ty = reftype ctx.modul.diagnostics ctx.modul.types ty in
      (match top_heap_type ctx ty.typ with
      | Cont -> Error.invalid_cast_type ctx.modul.diagnostics ~location:loc
      | _ -> ());
      let* () = lint_cast ctx ~location:loc ~is_test:false ty in
      let* () =
        pop_known ctx loc
          (Ref { nullable = true; typ = top_heap_type ctx ty.typ })
      in
      push ~source (Some loc) (Ref ty)
  | RefCastDescEq ty ->
      let source = Plain Ast.Text.(Ref ty) in
      let*! ty = reftype ctx.modul.diagnostics ctx.modul.types ty in
      (* The descriptor operand (top of stack); its exactness matches the target
         [ty]. *)
      let*! desc_ht = descriptor_operand_type ctx ~location:loc ty.typ in
      let* () =
        pop ctx loc
          ~expected_source:(descriptor_operand_source ctx.modul.types ty.typ)
          (Ref { nullable = true; typ = desc_ht })
      in
      let* () =
        pop_known ctx loc
          (Ref { nullable = true; typ = top_heap_type ctx ty.typ })
      in
      push ~source (Some loc) (Ref ty)
  | RefGetDesc idx ->
      let*! ty, _, _ = lookup_struct_type ctx idx in
      let*! desc = type_descriptor ctx ~location:i.info ty in
      let* entry, _ = pop_any ctx loc in
      (* [exact_1] is shared between the operand type [(ref null (exact_1 idx))]
         and the result [(ref (exact_1 desc))]: the descriptor is exact exactly
         when the operand is a subtype of the *exact* operand type. A subtype
         [(ref (exact $c))] with [$c <: idx] is NOT — its descriptor is [$c]'s,
         not [idx]'s — so the result is inexact there. A polymorphic operand
         (unreachable) fits either; take the most precise, exact. Validate the
         operand is a reference to [idx] (a subtype or null) either way. *)
      let exact =
        match entry with
        | Bot | Bot_ref -> true
        | Val (ty', source) ->
            if
              not
                (Types.val_subtype ctx.modul.subtyping_info ty'
                   (Ref { nullable = true; typ = Type ty }))
            then
              Error.type_mismatch ctx.modul.diagnostics ~location:loc
                ~provided_source:source
                ~expected_source:(named_ref_null_source idx);
            Types.val_subtype ctx.modul.subtyping_info ty'
              (Ref { nullable = true; typ = Exact ty })
      in
      push
        ~source:
          (descriptor_operand_source ~nullable:false ctx.modul.types
             (if exact then Exact ty else Type ty))
        (Some loc)
        (Ref
           { nullable = false; typ = (if exact then Exact desc else Type desc) })
  | StructNew idx ->
      let*! ty, _, fields = lookup_struct_type ctx idx in
      if
        Option.is_some
          (Types.get_subtype ctx.modul.subtyping_info ty).descriptor
      then
        Error.descriptor_allocation_required ctx.modul.diagnostics
          ~location:i.info;
      let* () =
        pop_args ctx loc
          ~source:
            (Array.init (Array.length fields) (source_field_valtype ctx idx))
          (Array.map
             (fun (f : fieldtype) ->
               match f.typ with Value v -> v | Packed _ -> I32)
             fields)
      in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | StructNewDefault idx ->
      let*! ty, _, fields = lookup_struct_type ctx idx in
      if not (Array.for_all field_has_default fields) then
        Error.not_defaultable ctx.modul.diagnostics ~location:i.info;
      if
        Option.is_some
          (Types.get_subtype ctx.modul.subtyping_info ty).descriptor
      then
        Error.descriptor_allocation_required ctx.modul.diagnostics
          ~location:i.info;
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | StructNewDesc idx ->
      let*! ty, _, fields = lookup_struct_type ctx idx in
      let*! desc = type_descriptor ctx ~location:i.info ty in
      (* The descriptor operand is on top of the field values. *)
      let* () =
        pop ctx loc
          ~expected_source:
            (descriptor_operand_source ctx.modul.types (Exact ty))
          (Ref { nullable = true; typ = Exact desc })
      in
      let* () =
        pop_args ctx loc
          ~source:
            (Array.init (Array.length fields) (source_field_valtype ctx idx))
          (Array.map
             (fun (f : fieldtype) ->
               match f.typ with Value v -> v | Packed _ -> I32)
             fields)
      in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref { nullable = false; typ = Exact ty })
  | StructNewDefaultDesc idx ->
      let*! ty, _, fields = lookup_struct_type ctx idx in
      if not (Array.for_all field_has_default fields) then
        Error.not_defaultable ctx.modul.diagnostics ~location:i.info;
      let*! desc = type_descriptor ctx ~location:i.info ty in
      let* () =
        pop ctx loc
          ~expected_source:
            (descriptor_operand_source ctx.modul.types (Exact ty))
          (Ref { nullable = true; typ = Exact desc })
      in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref { nullable = false; typ = Exact ty })
  | StructGet (signage, idx, idx') ->
      let*! ty, field_map, fields = lookup_struct_type ctx idx in
      let* () =
        pop ctx loc
          ~expected_source:(named_ref_null_source idx)
          (Ref { nullable = true; typ = Type ty })
      in
      let*! n = struct_field_index ctx idx' field_map fields in
      (match fields.(n).typ with
      | Packed _ ->
          if signage = None then
            Error.packed_struct_access ctx.modul.diagnostics ~location:i.info
      | Value _ ->
          if signage <> None then
            Error.unpacked_struct_access ctx.modul.diagnostics ~location:i.info);
      push
        ~source:(source_field_valtype ctx idx n)
        (Some loc)
        (unpack_type fields.(n))
  | StructSet (idx, idx') ->
      let*! ty, field_map, fields = lookup_struct_type ctx idx in
      let*! n = struct_field_index ctx idx' field_map fields in
      if not fields.(n).mut then
        Error.immutable ctx.modul.diagnostics ~location:i.info "field";
      let* () =
        pop ctx loc
          ~expected_source:(source_field_valtype ctx idx n)
          (unpack_type fields.(n))
      in
      pop ctx loc
        ~expected_source:(named_ref_null_source idx)
        (Ref { nullable = true; typ = Type ty })
  | ArrayNew idx ->
      let*! ty, field = lookup_array_type ctx idx in
      let* () = pop_known ctx loc I32 in
      let* () =
        pop ctx loc
          ~expected_source:(source_element_valtype ctx idx)
          (unpack_type field)
      in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | ArrayNewDefault idx ->
      let*! ty, field = lookup_array_type ctx idx in
      if not (field_has_default field) then
        Error.not_defaultable ctx.modul.diagnostics ~location:i.info;
      let* () = pop_known ctx loc I32 in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | ArrayNewFixed (idx, n) ->
      let*! ty, field = lookup_array_type ctx idx in
      let* () =
        pop_repeat ctx loc
          ~expected_source:(source_element_valtype ctx idx)
          (unpack_type field) (Uint32.to_int n)
      in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | ArrayNewData (idx, idx') ->
      let*! ty, field = lookup_array_type ctx idx in
      ignore (get_data ctx idx');
      (match field.typ with
      | Packed _ | Value (I32 | I64 | F32 | F64 | V128) -> ()
      | Value (Ref _) ->
          Error.numeric_array_required ctx.modul.diagnostics ~location:i.info);
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | ArrayNewElem (idx, idx') ->
      let*! ty, field = lookup_array_type ctx idx in
      let*! ty', _ = get_elem ctx idx' in
      (match field.typ with
      | Value ty when Types.val_subtype ctx.modul.subtyping_info (Ref ty') ty ->
          ()
      | _ ->
          Error.incompatible_array_element ctx.modul.diagnostics
            ~location:i.info);
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | ArrayGet (signage, idx) ->
      let*! ty, field = lookup_array_type ctx idx in
      (match field.typ with
      | Packed _ ->
          if signage = None then
            Error.packed_array_access ctx.modul.diagnostics ~location:i.info
      | Value _ ->
          if signage <> None then
            Error.unpacked_array_access ctx.modul.diagnostics ~location:i.info);
      let* () = pop_known ctx loc I32 in
      let* () =
        pop ctx loc
          ~expected_source:(named_ref_null_source idx)
          (Ref { nullable = true; typ = Type ty })
      in
      push
        ~source:(source_element_valtype ctx idx)
        (Some loc) (unpack_type field)
  | ArraySet idx ->
      let*! ty, field = lookup_array_type ctx idx in
      if not field.mut then
        Error.immutable ctx.modul.diagnostics ~location:i.info "array";
      let* () =
        pop ctx loc
          ~expected_source:(source_element_valtype ctx idx)
          (unpack_type field)
      in
      let* () = pop_known ctx loc I32 in
      pop ctx loc
        ~expected_source:(named_ref_null_source idx)
        (Ref { nullable = true; typ = Type ty })
  | ArrayLen ->
      let* () = pop_known ctx loc (Ref { nullable = true; typ = Array }) in
      push_known (Some loc) I32
  | ArrayFill idx ->
      let*! ty, field = lookup_array_type ctx idx in
      if not field.mut then
        Error.immutable ctx.modul.diagnostics ~location:i.info "array";
      let* () = pop_known ctx loc I32 in
      let* () =
        pop ctx loc
          ~expected_source:(source_element_valtype ctx idx)
          (unpack_type field)
      in
      let* () = pop_known ctx loc I32 in
      pop ctx loc
        ~expected_source:(named_ref_null_source idx)
        (Ref { nullable = true; typ = Type ty })
  | ArrayCopy (idx1, idx2) ->
      let*! ty1, field1 = lookup_array_type ctx idx1 in
      let*! ty2, field2 = lookup_array_type ctx idx2 in
      if not field1.mut then
        Error.immutable ctx.modul.diagnostics ~location:i.info "array";
      if not (storage_subtype ctx.modul.subtyping_info field1.typ field2.typ)
      then
        Error.incompatible_array_element ctx.modul.diagnostics ~location:i.info;
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      let* () =
        pop ctx loc
          ~expected_source:(named_ref_null_source idx2)
          (Ref { nullable = true; typ = Type ty2 })
      in
      let* () = pop_known ctx loc I32 in
      pop ctx loc
        ~expected_source:(named_ref_null_source idx1)
        (Ref { nullable = true; typ = Type ty1 })
  | ArrayInitData (idx, idx') ->
      let*! ty, field = lookup_array_type ctx idx in
      ignore (get_data ctx idx');
      if not field.mut then
        Error.immutable ctx.modul.diagnostics ~location:i.info "array";
      (match field.typ with
      | Packed _ | Value (I32 | I64 | F32 | F64 | V128) -> ()
      | Value (Ref _) ->
          Error.numeric_array_required ctx.modul.diagnostics ~location:i.info);
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      pop ctx loc
        ~expected_source:(named_ref_null_source idx)
        (Ref { nullable = true; typ = Type ty })
  | ArrayInitElem (idx, idx') ->
      let*! ty, field = lookup_array_type ctx idx in
      let*! ty', _ = get_elem ctx idx' in
      if not field.mut then
        Error.immutable ctx.modul.diagnostics ~location:i.info "array";
      (match field.typ with
      | Value ty when Types.val_subtype ctx.modul.subtyping_info (Ref ty') ty ->
          ()
      | _ ->
          Error.incompatible_array_element ctx.modul.diagnostics
            ~location:i.info);
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      pop ctx loc
        ~expected_source:(named_ref_null_source idx)
        (Ref { nullable = true; typ = Type ty })
  | RefI31 ->
      let* () = pop_known ctx loc I32 in
      push_known (Some loc) (Ref { nullable = false; typ = I31 })
  | I31Get _ ->
      let* () = pop_known ctx loc (Ref { nullable = true; typ = I31 }) in
      push_known (Some loc) I32
  | Const (I32 _) -> push_known (Some loc) I32
  | Const (I64 _) -> push_known (Some loc) I64
  | Const (F32 _) -> push_known (Some loc) F32
  | Const (F64 _) -> push_known (Some loc) F64
  | UnOp (I32 op) ->
      let expected, returned = int_un_op_type I32 op in
      let* () = pop_known ctx loc expected in
      push_known (Some loc) returned
  | UnOp (I64 op) ->
      let expected, returned = int_un_op_type I64 op in
      let* () = pop_known ctx loc expected in
      push_known (Some loc) returned
  | UnOp (F32 op) ->
      let expected = float_un_op_type F32 op in
      let* () = pop_known ctx loc expected in
      push_known (Some loc) F32
  | UnOp (F64 op) ->
      let expected = float_un_op_type F64 op in
      let* () = pop_known ctx loc expected in
      push_known (Some loc) F64
  | BinOp (I32 op) ->
      let* () = pop_known ctx loc I32 in
      let* () = pop_known ctx loc I32 in
      push_known (Some loc) (int_bin_op_type I32 op)
  | BinOp (I64 op) ->
      let* () = pop_known ctx loc I64 in
      let* () = pop_known ctx loc I64 in
      push_known (Some loc) (int_bin_op_type I64 op)
  | BinOp (F32 op) ->
      let* () = pop_known ctx loc F32 in
      let* () = pop_known ctx loc F32 in
      push_known (Some loc) (float_bin_op_type F32 op)
  | BinOp (F64 op) ->
      let* () = pop_known ctx loc F64 in
      let* () = pop_known ctx loc F64 in
      push_known (Some loc) (float_bin_op_type F64 op)
  | Add128 | Sub128 ->
      let* () = pop_known ctx loc I64 in
      let* () = pop_known ctx loc I64 in
      let* () = pop_known ctx loc I64 in
      let* () = pop_known ctx loc I64 in
      let* () = push_known (Some loc) I64 in
      push_known (Some loc) I64
  | MulWide _ ->
      let* () = pop_known ctx loc I64 in
      let* () = pop_known ctx loc I64 in
      let* () = push_known (Some loc) I64 in
      push_known (Some loc) I64
  | I32WrapI64 ->
      let* () = pop_known ctx loc I64 in
      push_known (Some loc) I32
  | I64ExtendI32 _ ->
      let* () = pop_known ctx loc I32 in
      push_known (Some loc) I64
  | F32DemoteF64 ->
      let* () = pop_known ctx loc F64 in
      push_known (Some loc) F32
  | F64PromoteF32 ->
      let* () = pop_known ctx loc F32 in
      push_known (Some loc) F64
  | ExternConvertAny ->
      let* tt = pop_any ctx loc in
      let nullable = convert_operand_nullable ctx loc tt ~typ:Any in
      push_known (Some loc) (Ref { nullable; typ = Extern })
  | AnyConvertExtern ->
      let* tt = pop_any ctx loc in
      let nullable = convert_operand_nullable ctx loc tt ~typ:Extern in
      push_known (Some loc) (Ref { nullable; typ = Any })
  | Folded (i, l) ->
      let* () = instructions ctx l in
      instruction ctx i
  | String (Some idx, s) ->
      let*! ty, field = lookup_array_type ctx idx in
      (match field.typ with
      | Packed I8 -> ()
      | Packed I16 ->
          let s = Wax_utils.Ast.concat_desc s in
          if not (String.is_valid_utf_8 s) then
            Error.string_not_unicode ctx.modul.diagnostics ~location:i.info
      | Value _ ->
          Error.string_array_required ctx.modul.diagnostics ~location:i.info);
      push ~source:(exact_ref_source ctx idx) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact ty else Type ty);
           })
  | String (None, _) ->
      let i = string_type_reference ctx.modul.types in
      let comptype = Ast.Text.Array { mut = true; typ = Packed I8 } in
      push ~source:(Inline_ref comptype) (Some loc)
        (Ref
           {
             nullable = false;
             typ = (if allocation_is_exact ctx then Exact i else Type i);
           })
  | Char _ -> push_known (Some loc) I32
  (* Conditional annotations are spliced out by [specialize] before a
     configuration is validated, so none can remain at this point. *)
  | If_annotation _ -> assert false

(* Wraps {!instruction_core} to feed the editor type sink (§ [recorded_types]).
   Two adjustments, both no-ops when the sink is off:
   - a folded instruction [(op … operands)] reads as one unit, so the type its
     head produces is relocated from the operator token to the whole folded
     span; nested operands keep their own (smaller) folded spans, so hovering an
     operand still shows its own type;
   - an instruction that leaves nothing on the stack ([drop], [local.set],
     [nop], [br], a call to a void function, …) records a void marker at its
     span, so hover shows nothing there rather than falling through to the
     enclosing instruction's type. *)
and instruction ctx i st =
  match !recorded_types with
  | None -> instruction_core ctx i st
  | Some r -> (
      match i.desc with
      | Folded (head, _) ->
          let st', () = instruction_core ctx i st in
          (* The head is validated last, so its entries are at the front. Pop
             them off the operator span and re-record them at the folded span,
             keeping each entry's configuration index. *)
          let rec take acc =
            match !r with
            | (l0, cfg, t) :: tl when l0 = head.info ->
                r := tl;
                take ((cfg, t) :: acc)
            | _ -> acc
          in
          List.iter (fun (cfg, t) -> r := (i.info, cfg, t) :: !r) (take []);
          (st', ())
      | _ ->
          let before = !r in
          let st', () = instruction_core ctx i st in
          let produced =
            (not (!r == before))
            && match !r with (l0, _, _) :: _ -> l0 = i.info | [] -> false
          in
          if not produced then r := (i.info, !sink_config, No_result) :: !r;
          (st', ()))

and instructions ctx l =
  match l with
  | [] -> return ()
  | i :: r ->
      let* () = instruction ctx i in
      instructions ctx r

and block ctx loc label ~used ~param_source ~result_source ~br_source ~params
    ~results ~br_params block =
  with_empty_stack ctx.modul loc
    (let* () = push_results ~sink:false ~loc ~source:param_source params in
     let* () =
       instructions
         {
           ctx with
           control_types =
             (Option.map (fun l -> l.Ast.desc) label, br_params, br_source, used)
             :: ctx.control_types;
         }
         block
     in
     pop_args ctx ~kind:`Output loc ~source:result_source results)

(*** Constant expressions ***)

let rec check_constant_instruction ctx (i : _ Ast.Text.instr) =
  match i.desc with
  | GlobalGet idx ->
      (* Resolved silently: an unbound global is reported by the stack
         validation of this same expression (via [get_global]). *)
      let*? ty, _ = Sequence.find ctx.globals idx in
      if ty.mut then
        Error.non_constant_global ctx.diagnostics ~location:idx.info idx
  | RefFunc i ->
      (* Record the referenced function by INDEX, not by its type: a ref.func in
         a body is valid only if that SAME function occurs outside any body, so
         keying by type would wrongly accept any other same-typed function.
         Resolved silently: an unbound function is reported by the stack
         validation (via [get_function]). *)
      let*? _ = Sequence.find ctx.functions i in
      Hashtbl.replace ctx.refs (Sequence.get_index ctx.functions i) ()
  | RefNull _ | StructNew _ | StructNewDefault _ | StructNewDesc _
  | StructNewDefaultDesc _ | ArrayNew _ | ArrayNewDefault _ | ArrayNewFixed _
  (* [cont.new] allocates a fresh continuation from a (constant) function
     reference, so it is itself a constant expression. The stack-switching spec
     and reference tools do not list it yet; this tracks the open spec PR. *)
  | ContNew _ | RefI31 | Const _
  | BinOp (I32 (Add | Sub | Mul) | I64 (Add | Sub | Mul))
  | ExternConvertAny | AnyConvertExtern | VecConst _ | String _ | Char _ ->
      ()
  | Folded (i, l) ->
      check_constant_instruction ctx i;
      check_constant_instructions ctx l
  | Block _ | Loop _ | If _ | TryTable _ | Try _ | Unreachable | Nop | Throw _
  | ThrowRef | ContBind _ | Suspend _ | Resume _ | ResumeThrow _
  | ResumeThrowRef _ | Switch _ | Br _ | Br_if _ | Br_table _ | Br_on_null _
  | Br_on_non_null _ | Br_on_cast _ | Br_on_cast_fail _ | Br_on_cast_desc_eq _
  | Br_on_cast_desc_eq_fail _ | Return | Call _ | CallRef _ | CallIndirect _
  | ReturnCall _ | ReturnCallRef _ | ReturnCallIndirect _ | Drop | Select _
  | LocalGet _ | LocalSet _ | LocalTee _ | GlobalSet _ | Load _ | LoadS _
  | Store _ | StoreS _ | Atomic _ | AtomicFence | MemorySize _ | MemoryGrow _
  | MemoryFill _ | MemoryCopy _ | MemoryInit _ | DataDrop _ | TableGet _
  | TableSet _ | TableSize _ | TableGrow _ | TableFill _ | TableCopy _
  | TableInit _ | ElemDrop _ | RefIsNull | RefAsNonNull | RefEq | RefTest _
  | RefCast _ | RefCastDescEq _ | RefGetDesc _ | StructGet _ | StructSet _
  | ArrayNewData _ | ArrayNewElem _ | ArrayGet _ | ArraySet _ | ArrayLen
  | ArrayFill _ | ArrayCopy _ | ArrayInitData _ | ArrayInitElem _ | I31Get _
  | UnOp _ | Add128 | Sub128 | MulWide _
  | BinOp
      ( F32 _ | F64 _
      | I32
          ( Div _ | Rem _ | And | Or | Xor | Shl | Shr _ | Rotl | Rotr | Eq | Ne
          | Lt _ | Gt _ | Le _ | Ge _ )
      | I64
          ( Div _ | Rem _ | And | Or | Xor | Shl | Shr _ | Rotl | Rotr | Eq | Ne
          | Lt _ | Gt _ | Le _ | Ge _ ) )
  | I32WrapI64 | I64ExtendI32 _ | F32DemoteF64 | F64PromoteF32 | VecBitselect
  | VecUnOp _ | VecBinOp _ | VecTest _ | VecShift _ | VecBitmask _ | VecLoad _
  | VecStore _ | VecLoadLane _ | VecStoreLane _ | VecLoadSplat _ | VecExtract _
  | VecReplace _ | VecSplat _ | VecShuffle _ | VecTernOp _ ->
      Error.constant_expression_required ctx.diagnostics ~location:i.info
  (* Spliced out by [specialize] before validation; cannot occur here. *)
  | If_annotation _ -> assert false

and check_constant_instructions ctx l =
  List.iter (fun i -> check_constant_instruction ctx i) l

(* Forward reference to [lint_body] (defined below), so [constant_expression] can
   lint a constant expression with the same walk used for function bodies. *)
let lint_constant_expr = ref (fun _ _ -> ())

let constant_expression ctx ~location ~expected_source ty expr =
  check_constant_instructions ctx expr;
  with_empty_stack ctx location
    (let ctx =
       {
         locals = Sequence.make "local";
         control_types = [];
         return_types = [||];
         return_source = [||];
         modul = ctx;
         initialized_locals = IntSet.empty;
         used_locals = ref IntSet.empty;
         poisoned_locals = IntSet.empty;
         label_decls = ref [];
       }
     in
     let* () = instructions ctx expr in
     (* Lint the constant expression too (a data/elem offset, a global or field
        initializer): the Wax typer lints these, so without this the wat/wasm
        side misses a redundant [0 + 42] offset the Wax side reports. Via a
        forward reference, as [lint_body] is defined below. *)
     if ctx.modul.warn_unused then !lint_constant_expr ctx expr;
     pop ctx location ~expected_source ty)

(*** Type registration and the module environment ***)

let add_type d ctx ty =
  Array.iteri
    (fun i e ->
      let label, (sub : Ast.Text.subtype) = e.Ast.desc in
      (* These forward references are placeholders during the rec group's own
         resolution and are replaced (or dropped) below; the composite type is
         not consulted meanwhile, but carrying it keeps the field total. *)
      Hashtbl.replace ctx.index_mapping
        (Uint32.of_int (ctx.last_index + i))
        (Types.Rec i, [], sub.typ, Some e);
      Option.iter
        (fun label ->
          Hashtbl.replace ctx.label_mapping label.Ast.desc
            (Types.Rec i, [], sub.typ, Some e))
        label)
    ty;
  match rectype d ctx ty with
  | None ->
      (* Resolution of this rec group failed. Drop the placeholder mappings but
         poison these text indices / names, and still advance [last_index]: later
         type definitions keep their positions and numeric references stay
         aligned, while a reference to a poisoned member resolves to [None]
         silently (the real error was reported by [rectype]). *)
      Array.iteri
        (fun i e ->
          let label = fst e.Ast.desc in
          let idx = Uint32.of_int (ctx.last_index + i) in
          Hashtbl.remove ctx.index_mapping idx;
          Hashtbl.replace ctx.poisoned_index idx ();
          Option.iter
            (fun label ->
              Hashtbl.remove ctx.label_mapping label.Ast.desc;
              Hashtbl.replace ctx.poisoned_label label.Ast.desc ())
            label)
        ty;
      ctx.last_index <- ctx.last_index + Array.length ty
  | Some ty' ->
      (* Well-formedness of [descriptor] / [describes] clauses, which must link
         two struct types within the same recursion group. In [ty'] a [Rec]
         reference names a member of this group; a [Def] denotes an
         already-defined type outside it. *)
      Array.iteri
        (fun i (sub : Types.Normalized.subtype) ->
          let location = ty.(i).Ast.info in
          (match sub.descriptor with
          | None -> ()
          | Some (Def _) ->
              Error.descriptor_outside_rec_group d ~location ~described:false
          | Some (Rec pos) -> (
              (* This type is described by [ty'.(pos)]; that descriptor must
                 describe this type back, and share its finality: an open type
                 whose descriptor is final (or the reverse) could never be
                 extended, since a subtype would need a descriptor extending a
                 final one. Reported here only, on the described type, so the
                 reciprocal pair yields a single error. *)
              match ty'.(pos).describes with
              | Some (Rec o) when o = i ->
                  if sub.final <> ty'.(pos).final then
                    Error.descriptor_finality_mismatch d ~location
              | _ ->
                  Error.descriptor_not_reciprocal d ~location ~described:false));
          (match sub.describes with
          | None -> ()
          | Some (Def _) ->
              Error.descriptor_outside_rec_group d ~location ~described:true
          | Some (Rec pos) -> (
              if pos >= i then Error.forward_use_of_described d ~location;
              (* This type is the descriptor of [ty'.(pos)], which must name this
                 type as its descriptor. *)
              match ty'.(pos).descriptor with
              | Some (Rec dd) when dd = i -> ()
              | _ -> Error.descriptor_not_reciprocal d ~location ~described:true
              ));
          if
            (sub.descriptor <> None || sub.describes <> None)
            && match sub.typ with Struct _ -> false | _ -> true
          then
            Error.descriptor_not_struct d ~location
              ~described:(sub.describes <> None))
        ty';
      let i' = Types.add_rectype ctx.types ty' in
      Array.iteri
        (fun i e ->
          let label, typ = e.Ast.desc in
          let fields =
            match (typ : Ast.Text.subtype).typ with
            | Struct fields ->
                Array.mapi
                  (fun i e ->
                    match fst e.Ast.desc with
                    | Some id -> Some (id.Ast.desc, i)
                    | None -> None)
                  fields
                |> Array.to_list |> List.filter_map Fun.id
            | _ -> []
          in
          Hashtbl.replace ctx.index_mapping
            (Uint32.of_int (ctx.last_index + i))
            (Types.Def (Types.Id.add i' i), fields, typ.typ, Some e);
          let def_idx =
            let desc =
              match label with
              | Some l -> Ast.Text.Id l.Ast.desc
              | None -> Ast.Text.Num (Uint32.of_int (ctx.last_index + i))
            in
            { Ast.desc; info = e.Ast.info }
          in
          let cont_ref =
            match (typ : Ast.Text.subtype).typ with
            | Cont r -> Some r
            | Func _ | Struct _ | Array _ -> None
          in
          Hashtbl.replace ctx.type_defs (ctx.last_index + i) (def_idx, cont_ref);
          Option.iter
            (fun node ->
              Hashtbl.replace ctx.descriptor_source (Types.Id.add i' i) node)
            (typ : Ast.Text.subtype).descriptor;
          Option.iter
            (fun label ->
              Hashtbl.replace ctx.label_mapping label.Ast.desc
                (Types.Def (Types.Id.add i' i), fields, typ.typ, Some e))
            label)
        ty;
      ctx.last_index <- ctx.last_index + Array.length ty

let register_exports ctx lst =
  List.iter
    (fun (name : Ast.Text.name) ->
      match Hashtbl.find_opt ctx.exports name.desc with
      | Some prev_loc ->
          Error.duplicated_export ctx.diagnostics ~location:name.info ~prev_loc
            name
      | None -> Hashtbl.add ctx.exports name.desc name.info)
    lst

let limits ctx kind
    {
      Ast.desc = { mi; ma; address_type; page_size_log2; shared };
      info = location;
    } max_fn =
  (match page_size_log2 with
  | None | Some (0 | 16) -> ()
  | Some _ -> Error.invalid_page_size ctx.diagnostics ~location);
  (* A shared memory must declare a maximum size. *)
  if shared && ma = None then
    Error.shared_memory_without_max ctx.diagnostics ~location;
  let max = max_fn address_type page_size_log2 in
  match ma with
  | None ->
      if Uint64.compare mi max > 0 then
        Error.limit_too_large ctx.diagnostics ~location kind max
  | Some ma ->
      if Uint64.compare mi ma > 0 then
        Error.limit_mismatch ctx.diagnostics ~location kind;
      if Uint64.compare ma max > 0 then
        Error.limit_too_large ctx.diagnostics ~location kind max

(* The maximum number of pages: [min(2^bits - 1, 2^(bits - p))] where [bits] is
   32 (i32) or 64 (i64) and [2^p] is the page size (default 2^16). The byte span
   gives the [2^(bits - p)] term; the [2^bits - 1] cap bounds the page index
   itself (so e.g. a page size of 1 allows 2^32 - 1 pages, not 2^32). With the
   default page size this is the familiar 65536 / 2^48 pages. *)
let max_memory_size address_type page_size_log2 =
  let p = match page_size_log2 with None -> 16 | Some p -> p in
  let bits, index_max =
    match address_type with
    | `I32 -> (32, Uint64.of_string "0xffff_ffff")
    | `I64 -> (64, Uint64.of_string "0xffff_ffff_ffff_ffff")
  in
  let e = bits - p in
  let by_page =
    if e >= 64 then index_max
    else if e <= 0 then Uint64.zero
    else Uint64.of_int64 (Int64.shift_left 1L e)
  in
  if Uint64.compare index_max by_page <= 0 then index_max else by_page

let max_table_size address_type _page_size_log2 =
  match address_type with
  | `I32 -> Uint64.of_string "0xffff_ffff"
  | `I64 -> Uint64.of_string "0xffff_ffff_ffff_ffff"

(* Collect the implicit function types denoted by inline signatures (function
   and tag definitions, imports, block types and [call_indirect]). Following
   the text format, such a type reuses a structurally-equal type if one already
   exists, and is otherwise appended to the end of the type index space, where
   it can be referred to by index. We must do this before resolving any type
   reference so that those indices are bound, and before computing the
   subtyping information so that it covers every type. Relies on
   {!Types.add_rectype} deduplicating: a [typeuse] encountered later during
   validation then resolves to the type collected here instead of growing the
   type table. Diagnostics are muted: a signature that does not resolve is
   skipped here and reported by the pass that owns the construct (an import or
   tag by [build_initial_env], a function by [functions], a block type or
   [call_indirect] by the body validation). *)
let collect_implicit_types d ctx fields =
  let d = muted d in
  let collect sign =
    let>@ ft = n_functype d ctx sign in
    let before = Types.last_index ctx.types in
    let idx =
      Types.add_rectype ctx.types
        [|
          {
            typ = Func ft;
            supertype = None;
            final = true;
            descriptor = None;
            describes = None;
          };
        |]
    in
    if Types.last_index ctx.types > before then (
      Hashtbl.replace ctx.index_mapping
        (Uint32.of_int ctx.last_index)
        (Types.Def idx, [], Func sign, None);
      ctx.last_index <- ctx.last_index + 1)
  in
  let collect_instr (i : _ Ast.Text.instr) =
    match i.desc with
    | Block { typ = Some (Typeuse (None, Some ft)); _ }
    | Loop { typ = Some (Typeuse (None, Some ft)); _ }
    | If { typ = Some (Typeuse (None, Some ft)); _ }
    | Try { typ = Some (Typeuse (None, Some ft)); _ }
    | TryTable { typ = Some (Typeuse (None, Some ft)); _ } ->
        collect ft
    | CallIndirect (_, (None, Some ft)) | ReturnCallIndirect (_, (None, Some ft))
      ->
        collect ft
    | If_annotation _ ->
        (* Spliced out by [specialize] before validation; cannot occur here. *)
        assert false
    | _ -> ()
  in
  (* The canonical walk descends into every nesting instruction, branch hints
     included, so inline types buried there are interned like any other. *)
  let collect_instrs l = List.iter (Ast_utils.iter_instr collect_instr) l in
  (* A defined function's own signature and the inline block types in its body are
     references *it* makes, so attribute them to it — otherwise interning them here
     would make a dead function's types look externally referenced, and the Wax
     typer (which resolves them per function) would disagree. The counter mirrors
     the function-index allocation of [build_initial_env] over this same expanded
     list. An import's or tag's signature stays a root: neither is reached through
     a function. *)
  let index = ref 0 in
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      (match field.desc with
      | Func _ -> ctx.origin <- From_function !index
      | _ -> ());
      (match field.desc with
      | Import { desc = Func { typ = None, Some sign; _ }; _ }
      | Import { desc = Tag (None, Some sign); _ }
      | Func { typ = None, Some sign; _ }
      | Tag { typ = None, Some sign; _ } ->
          collect sign
      | _ -> ());
      (match field.desc with
      | Func { instrs; _ } -> collect_instrs instrs
      | _ -> ());
      ctx.origin <- Root;
      match field.desc with
      | Import { desc = Func _; _ } | Func _ -> incr index
      | _ -> ())
    (List.concat_map Ast_utils.expand_import_group fields)

let build_initial_env ctx fields =
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Import { id; desc; exports; module_ = _; name = _ } -> (
          register_exports ctx exports;
          (* Record the import as an [unused-import] candidate; an inline export
             re-exports it, so mark it used. *)
          let location =
            match id with Some id -> id.Ast.info | None -> field.info
          in
          let mark used idx =
            if exports <> [] then Hashtbl.replace used idx ()
          in
          match desc with
          | Func { exact; typ = tu } -> (
              let idx = Sequence.next_index ctx.functions in
              match typeuse ctx.diagnostics ctx.types tu with
              | None ->
                  (* The typeuse did not resolve (reported above). Claim the
                     index anyway so later functions stay aligned; skip the
                     [unused-import] candidate for a definition that failed. *)
                  Sequence.register_failed ctx.functions id
              | Some ty ->
                  Sequence.register ctx.functions id
                    (ty, fst tu, typeuse_functype ctx.types tu, exact);
                  ctx.imported_functions <-
                    (idx, id, location) :: ctx.imported_functions;
                  mark ctx.used_functions idx)
          | Memory lim ->
              limits ctx "memory" lim max_memory_size;
              let idx = Sequence.next_index ctx.memories in
              Sequence.register ctx.memories id lim.desc;
              ctx.imported_memories <-
                (idx, id, location) :: ctx.imported_memories;
              mark ctx.used_memories idx
          | Table typ -> (
              limits ctx "table" typ.limits max_table_size;
              let idx = Sequence.next_index ctx.tables in
              let src = Plain (Ast.Text.Ref typ.reftype) in
              match tabletype ctx.diagnostics ctx.types typ with
              | None -> Sequence.register_failed ctx.tables id
              | Some typ ->
                  Sequence.register ctx.tables id (typ, src);
                  ctx.imported_tables <-
                    (idx, id, location) :: ctx.imported_tables;
                  mark ctx.used_tables idx)
          | Global ty -> (
              let idx = Sequence.next_index ctx.globals in
              let src = Plain ty.typ in
              match globaltype ctx.diagnostics ctx.types ty with
              | None -> Sequence.register_failed ctx.globals id
              | Some ty ->
                  Sequence.register ctx.globals id (ty, src);
                  ctx.imported_globals <-
                    (idx, id, location) :: ctx.imported_globals;
                  mark ctx.used_globals idx)
          | Tag tu -> (
              let idx = Sequence.next_index ctx.tags in
              match typeuse ctx.diagnostics ctx.types tu with
              | None -> Sequence.register_failed ctx.tags id
              | Some ty ->
                  let sign = typeuse_functype ctx.types tu in
                  (* A tag's function type is deliberately not required to have
                     empty results: the stack-switching proposal uses tags with
                     result types (for [suspend] / [resume]), so the
                     exception-handling restriction to no results is not
                     enforced. *)
                  Sequence.register ctx.tags id (ty, sign);
                  ctx.imported_tags <- (idx, id, location) :: ctx.imported_tags;
                  mark ctx.used_tags idx))
      | Func { id; typ; exports; instrs = _; locals = _; priority = _ } -> (
          (* A function's own signature is a reference *it* makes, so attribute it
             to the index this definition is about to claim rather than letting a
             dead function's type look externally referenced. *)
          ctx.types.origin <- From_function (Sequence.next_index ctx.functions);
          (* Resolved with muted diagnostics: the [functions] pass resolves
             this typeuse again and owns its errors. *)
          let resolved = typeuse (muted ctx.diagnostics) ctx.types typ in
          ctx.types.origin <- Root;
          match resolved with
          | None ->
              (* The typeuse did not resolve. Claim the index (later functions
                 stay aligned) but do not record an [unused-field] candidate. *)
              Sequence.register_failed ctx.functions id
          | Some ty ->
              let sign = typeuse_functype ctx.types typ in
              (* A module-defined function has exactly its declared type, so a
                 reference to it is exact — but exact reference types are part of
                 custom-descriptors, so without the feature it is the plain
                 inexact reference, as before the proposal. See
                 [allocation_is_exact]: the Wax typer gates the same decision, and
                 the two must agree. *)
              let exact =
                Wax_utils.Feature.is_enabled ctx.types.features
                  Wax_utils.Feature.Custom_descriptors
              in
              let idx = Sequence.next_index ctx.functions in
              Sequence.register ctx.functions id (ty, fst typ, sign, exact);
              (* Record it as an [unused-field] candidate; an inline export makes
                 it externally reachable, so mark it used. *)
              let location =
                match id with Some id -> id.Ast.info | None -> field.info
              in
              ctx.defined_functions <-
                (idx, id, location) :: ctx.defined_functions;
              if exports <> [] then Hashtbl.replace ctx.used_functions idx ())
      | Tag { id; typ; exports } -> (
          let idx = Sequence.next_index ctx.tags in
          match typeuse ctx.diagnostics ctx.types typ with
          | None -> Sequence.register_failed ctx.tags id
          | Some ty ->
              let sign = typeuse_functype ctx.types typ in
              (* A tag's function type is deliberately not required to have empty
                 results: the stack-switching proposal uses tags with result
                 types (for [suspend] / [resume]), so the exception-handling
                 restriction to no results is not enforced. *)
              register_exports ctx exports;
              Sequence.register ctx.tags id (ty, sign);
              let location =
                match id with Some id -> id.Ast.info | None -> field.info
              in
              ctx.defined_tags <- (idx, id, location) :: ctx.defined_tags;
              if exports <> [] then Hashtbl.replace ctx.used_tags idx ())
      | _ -> ())
    (List.concat_map Ast_utils.expand_import_group fields)

let check_type_definitions ctx =
  (* This sweeps every type index to check the definition's own well-formedness,
     re-resolving each one; those resolutions are not source references, so
     recording them would make every type look used. *)
  ctx.types.origin <- Ignored;
  for i = 0 to ctx.types.last_index - 1 do
    let def_idx, cont_ref =
      Option.value
        ~default:(Ast.no_loc (Ast.Text.Num (Uint32.of_int i)), None)
        (Hashtbl.find_opt ctx.types.type_defs i)
    in
    let location = def_idx.Ast.info in
    let>@ gidx, _, _, _ =
      get_type_info ctx.diagnostics ctx.types
        (Ast.no_loc (Ast.Text.Num (Uint32.of_int i)))
    in
    let ty = Types.get_subtype ctx.subtyping_info (def_id gidx) in
    (* A continuation type must wrap a function type. *)
    (match ty.typ with
    | Cont ft -> (
        match (Types.get_subtype ctx.subtyping_info ft).typ with
        | Func _ -> ()
        | Struct _ | Array _ | Cont _ ->
            (* Name the wrapped type as the source wrote it: the resolved index
               [ft] is canonical, so identical types would otherwise be
               indistinguishable. A [Cont] type is only ever registered by
               [add_type], which records its wrapped-type source, so [cont_ref]
               is necessarily [Some] here. *)
            let wrapped =
              match cont_ref with Some r -> r | None -> assert false
            in
            Error.expected_func_type ctx.diagnostics ~location wrapped)
    | Func _ | Struct _ | Array _ -> ());
    let*? j = ty.supertype in
    let ty' = Types.get_subtype ctx.subtyping_info j in
    let invalid () = Error.invalid_subtype ctx.diagnostics ~location in
    if ty'.final then invalid ()
    else begin
      (match (ty.typ, ty'.typ) with
      | Func { params; results }, Func { params = params'; results = results' }
        ->
          if
            Array.length params <> Array.length params'
            || Array.length results <> Array.length results'
            || not
                 (Array.for_all2
                    (fun p p' -> Types.val_subtype ctx.subtyping_info p' p)
                    params params'
                 && Array.for_all2
                      (fun r r' -> Types.val_subtype ctx.subtyping_info r r')
                      results results')
          then invalid ()
      | Struct fields, Struct fields' ->
          if
            Array.length fields' > Array.length fields
            || not
                 (Array.for_all2
                    (field_subtype ctx.subtyping_info)
                    (Array.sub fields 0 (Array.length fields'))
                    fields')
          then invalid ()
      | Array field, Array field' ->
          if not (field_subtype ctx.subtyping_info field field') then invalid ()
      | Cont ft, Cont ft' ->
          if not (Types.heap_subtype ctx.subtyping_info (Type ft) (Type ft'))
          then invalid ()
      | Func _, (Struct _ | Array _ | Cont _)
      | Struct _, (Func _ | Array _ | Cont _)
      | Array _, (Func _ | Struct _ | Cont _)
      | Cont _, (Func _ | Struct _ | Array _) ->
          Error.supertype_mismatch ctx.diagnostics ~location);
      (* A subtype has a descriptor iff its supertype does, and the subtype's
         descriptor must be a subtype of the supertype's. *)
      (match (ty.descriptor, ty'.descriptor) with
      | None, None -> ()
      | Some ds, Some dp ->
          if not (Types.heap_subtype ctx.subtyping_info (Type ds) (Type dp))
          then invalid ()
      | Some _, None | None, Some _ -> invalid ());
      (* A subtype has a described type iff its supertype does, and the
         subtype's described type must be a subtype of the supertype's. *)
      match (ty.describes, ty'.describes) with
      | None, None -> ()
      | Some os, Some op ->
          if not (Types.heap_subtype ctx.subtyping_info (Type os) (Type op))
          then invalid ()
      | Some _, None | None, Some _ -> invalid ()
    end
  done;
  ctx.types.origin <- Root

(*** Module-field validation passes ***)

let tables_and_memories ctx fields =
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      (* As for a function or global, record the definition as an [unused-field]
         candidate, with an inline export marking it externally reachable. *)
      let report_location id =
        match id with Some id -> id.Ast.info | None -> field.info
      in
      match field.desc with
      | Memory { id; limits = lim; init = _; exports } ->
          limits ctx "memory" lim max_memory_size;
          let idx = Sequence.next_index ctx.memories in
          Sequence.register ctx.memories id lim.desc;
          ctx.defined_memories <-
            (idx, id, report_location id) :: ctx.defined_memories;
          if exports <> [] then Hashtbl.replace ctx.used_memories idx ();
          register_exports ctx exports
      | Table { id; typ; init; exports } -> (
          limits ctx "table" typ.limits max_table_size;
          let idx = Sequence.next_index ctx.tables in
          let src = Plain (Ast.Text.Ref typ.reftype) in
          match tabletype ctx.diagnostics ctx.types typ with
          | None -> Sequence.register_failed ctx.tables id
          | Some typ ->
              (match init with
              | Init_default ->
                  if not typ.reftype.nullable then
                    Error.non_nullable_table_type ctx.diagnostics
                      ~location:field.info (*ZZZ*)
              | Init_expr e ->
                  constant_expression ctx ~location:field.info
                    ~expected_source:src (Ref typ.reftype) e
              | Init_segment _ -> ());
              Sequence.register ctx.tables id (typ, src);
              ctx.defined_tables <-
                (idx, id, report_location id) :: ctx.defined_tables;
              if exports <> [] then Hashtbl.replace ctx.used_tables idx ();
              register_exports ctx exports)
      | _ -> ())
    fields

let globals ctx fields =
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Global { id; typ; init; exports } -> (
          let src = Plain typ.typ in
          match globaltype ctx.diagnostics ctx.types typ with
          | None -> Sequence.register_failed ctx.globals id
          | Some typ ->
              constant_expression ctx ~location:field.info ~expected_source:src
                typ.typ init;
              let idx = Sequence.next_index ctx.globals in
              Sequence.register ctx.globals id (typ, src);
              (* Record it as an [unused-field] candidate; an inline export makes
                 it externally reachable, so mark it used. *)
              let location =
                match id with Some id -> id.Ast.info | None -> field.info
              in
              ctx.defined_globals <- (idx, id, location) :: ctx.defined_globals;
              (* A [mut] global is also an [unnecessary-mut] candidate. *)
              if typ.mut then
                ctx.mutable_globals <-
                  (idx, id, location) :: ctx.mutable_globals;
              if exports <> [] then begin
                Hashtbl.replace ctx.used_globals idx ();
                (* An exported global is assignable by the host, so it counts as
                   assigned for [unnecessary-mut]. *)
                Hashtbl.replace ctx.assigned_globals idx ()
              end;
              register_exports ctx exports)
      | String_global { id; typ; init } ->
          (* A named array type is honoured (and must be an i8/i16 array, like
             any string); with none, the global takes the default [<string>]
             ([mut i8]) type. *)
          let ty, src =
            match typ with
            | None ->
                ( string_type_reference ctx.types,
                  Inline_ref (Ast.Text.Array { mut = true; typ = Packed I8 }) )
            | Some idx -> (
                match resolve_type_index ctx.diagnostics ctx.types idx with
                | None ->
                    ( string_type_reference ctx.types,
                      Inline_ref
                        (Ast.Text.Array { mut = true; typ = Packed I8 }) )
                | Some ty ->
                    (match (Types.get_subtype ctx.subtyping_info ty).typ with
                    | Array { typ = Packed I8; _ } -> ()
                    | Array { typ = Packed I16; _ } ->
                        let s = Wax_utils.Ast.concat_desc init in
                        if not (String.is_valid_utf_8 s) then
                          Error.string_not_unicode ctx.diagnostics
                            ~location:idx.info
                    | Array { typ = Value _; _ } ->
                        Error.string_array_required ctx.diagnostics
                          ~location:idx.info
                    | _ ->
                        Error.expected_array_type ctx.diagnostics
                          ~location:idx.info idx);
                    (ty, named_ref_source idx))
          in
          let typ =
            { mut = false; typ = Ref { nullable = false; typ = Type ty } }
          in
          Sequence.register ctx.globals (Some id) (typ, src)
      | _ -> ())
    fields

let segments ctx fields =
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      (* An active or declarative segment runs at instantiation, so it is used
         whatever the bodies do; only a passive one is an [unused-field]
         candidate, reachable solely through [memory.init]/[table.init] and
         [data.drop]/[elem.drop]. *)
      match field.desc with
      | Memory { init; _ } ->
          let*? _ = init in
          (* The implicit segment of a memory's inline data is active. *)
          Hashtbl.replace ctx.used_data (Sequence.next_index ctx.data) ();
          Sequence.register ctx.data None ()
      | Data { id; init = _; mode } ->
          let idx = Sequence.next_index ctx.data in
          let location =
            match id with Some id -> id.Ast.info | None -> field.info
          in
          (match mode with
          | Passive ->
              ctx.defined_data <- (idx, id, location) :: ctx.defined_data
          | Active (i, e) ->
              Hashtbl.replace ctx.used_data idx ();
              mark_reference ctx
                (fun i -> Ref_memory i)
                ctx.used_memories ctx.memories i;
              let*? limits = Sequence.get ctx.diagnostics ctx.memories i in
              let aty = address_type_to_valtype limits.address_type in
              constant_expression ctx ~location:field.info
                ~expected_source:(source_of_valtype aty) aty e);
          Sequence.register ctx.data id ()
      | Table { typ; init; _ } -> (
          match init with
          | Init_default | Init_expr _ -> ()
          | Init_segment lst -> (
              let src = Plain (Ast.Text.Ref typ.reftype) in
              (* The implicit segment of a table's inline element list is
                 active. *)
              Hashtbl.replace ctx.used_elem (Sequence.next_index ctx.elem) ();
              match reftype ctx.diagnostics ctx.types typ.reftype with
              | None -> Sequence.register_failed ctx.elem None
              | Some typ ->
                  List.iter
                    (fun e ->
                      constant_expression ctx ~location:field.info
                        ~expected_source:src (Ref typ) e)
                    lst;
                  Sequence.register ctx.elem None (typ, src)))
      | Elem { id; typ; init; mode } -> (
          let elem_source = Plain (Ast.Text.Ref typ) in
          let idx = Sequence.next_index ctx.elem in
          let location =
            match id with Some id -> id.Ast.info | None -> field.info
          in
          match reftype ctx.diagnostics ctx.types typ with
          | None -> Sequence.register_failed ctx.elem id
          | Some typ ->
              (match mode with
              | Passive ->
                  ctx.defined_elem <- (idx, id, location) :: ctx.defined_elem
              | Declare -> Hashtbl.replace ctx.used_elem idx ()
              | Active (i, e) ->
                  Hashtbl.replace ctx.used_elem idx ();
                  mark_reference ctx
                    (fun i -> Ref_table i)
                    ctx.used_tables ctx.tables i;
                  let*? tabletype, table_source =
                    Sequence.get ctx.diagnostics ctx.tables i
                  in
                  if
                    not
                      (Types.val_subtype ctx.subtyping_info (Ref typ)
                         (Ref tabletype.reftype))
                  then
                    Error.elem_segment_type_mismatch ctx.diagnostics
                      ~location:field.info ~elem_source ~table_source;
                  let aty =
                    address_type_to_valtype tabletype.limits.address_type
                  in
                  constant_expression ctx ~location:field.info
                    ~expected_source:(source_of_valtype aty) aty e);
              (* A DECLARATIVE segment installs nothing and runs nothing: it
                 exists so that a [ref.func] elsewhere validates, so the
                 references in its init expressions are not roots. The function
                 is reachable exactly when that other [ref.func] is — otherwise a
                 function only its own dead body takes a reference of would look
                 live here while the Wax typer, whose surface leaves the segment
                 implicit, correctly reports it dead (a lint-parity finding from
                 the wasm-smith campaign). An ACTIVE segment does install into a
                 table, and a PASSIVE one can be [table.init]ed, so both keep
                 rooting theirs. *)
              let outer = ctx.types.origin in
              if mode = Declare then ctx.types.origin <- Ignored;
              List.iter
                (fun e ->
                  constant_expression ctx ~location:field.info
                    ~expected_source:elem_source (Ref typ) e)
                init;
              ctx.types.origin <- outer;
              Sequence.register ctx.elem id (typ, elem_source))
      | _ -> ())
    fields

(* An exported function is referenceable by [ref.func] (it is in the module's
   [refs] set), like a function named in a global or element segment. Record
   exported functions by index BEFORE bodies are validated — the dedicated
   [exports] pass runs after [functions], too late for the [ref.func] check.
   Both a standalone export field and an inline export on a function count; in a
   binary all exports are standalone (the export section), inline being WAT
   sugar. Function indices are counted positionally, imports first (their order
   is enforced by [check_import_order]), matching how [build_initial_env]
   registers them. *)
let declared_func_exports ctx fields =
  let fi = ref 0 in
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Import { desc = Func _; exports; _ } ->
          if exports <> [] then Hashtbl.replace ctx.refs !fi ();
          incr fi
      | Import _ -> ()
      | Func { exports; _ } ->
          if exports <> [] then Hashtbl.replace ctx.refs !fi ();
          incr fi
      | Export { kind = Func; index; _ } ->
          Option.iter
            (fun i -> Hashtbl.replace ctx.refs i ())
            (Sequence.get_index_opt ctx.functions index)
      | _ -> ())
    (List.concat_map Ast_utils.expand_import_group fields)

(*** Correctness lints over a function body (see {!Wax_utils.Warning}) ***)

(* A constant operand tracked while linting. Crossing any non-constant
   instruction clears the stack, so its entries mirror the most recent run of
   constants on the real operand stack — the top is a binary operator's right
   operand (its last-pushed value). Folded operands flatten into the same push
   sequence, so folded and flat forms are handled alike. *)
(* A value tracked on the lint stack: a known integer/float constant, a bare
   [local.get]/[global.get] read (tracked by resolved index so two reads of the
   same variable can be recognised as identical operands), or some other value
   produced with no side effect and no trap ([LPure]). Constants and reads are
   also pure. Anything else clears the stack. *)
type lint_val =
  | LInt of int64
  | LFloat of float
  | LLocal of int
  | LGlobal of int
  | LPure

let lint_int_value s =
  let s = String.concat "" (String.split_on_char '_' s) in
  match Int64.of_string_opt s with
  | Some _ as r -> r
  (* An unsigned decimal past [2^63] (e.g. a shift count of [18446744073709551615]
     = -1) overflows a signed parse; read it unsigned so it is still tracked. *)
  | None -> Int64.of_string_opt ("0u" ^ s)

let lint_float_value s =
  let s = String.concat "" (String.split_on_char '_' s) in
  let body =
    if String.length s > 0 && (s.[0] = '+' || s.[0] = '-') then
      String.sub s 1 (String.length s - 1)
    else s
  in
  if String.length body >= 3 && String.equal (String.sub body 0 3) "nan" then
    Some Float.nan
  else float_of_string_opt s

(* Round an [f64] to the nearest representable [f32] (the [f32.demote_f64] the
   runtime applies), via the single-precision bit layout. *)
let round_to_f32 f = Int32.float_of_bits (Int32.bits_of_float f)

(* Whether a trapping (toward-zero) float-to-integer conversion of [f] to the
   given target/signage would trap: NaN/infinite, or out of range. *)
let float_conversion_traps target signage f =
  if not (Float.is_finite f) then true
  else
    let t = Float.trunc f in
    let pow2 n = Float.ldexp 1. n in
    match (target, signage) with
    | `I32, Ast.Signed -> t < -.pow2 31 || t >= pow2 31
    | `I32, Ast.Unsigned -> t < 0. || t >= pow2 32
    | `I64, Ast.Signed -> t < -.pow2 63 || t >= pow2 63
    | `I64, Ast.Unsigned -> t < 0. || t >= pow2 64

(* Report the constant-operand lints (shift count, division/remainder by zero,
   out-of-range trapping conversion, tautological unsigned comparison, constant
   condition, discarded constant) and dead code over a function body. *)
let lint_body ctx instrs =
  let diagnostics = ctx.modul.diagnostics in
  (* The number of field operands of a [struct.new] on the type at [idx], or
     [None] if the index does not resolve to a struct type. Looks the type up
     silently (the body has already been validated, so a bad index has already
     been reported — re-reporting here would duplicate the diagnostic). *)
  let struct_arity idx =
    let m = ctx.modul in
    match
      try
        match idx.Ast.desc with
        | Ast.Text.Num x -> Some (Hashtbl.find m.types.index_mapping x)
        | Ast.Text.Id id -> Some (Hashtbl.find m.types.label_mapping id)
      with Not_found -> None
    with
    | Some (gidx, _, _, _) -> (
        match (Types.get_subtype m.subtyping_info (def_id gidx)).typ with
        | Struct fields -> Some (Array.length fields)
        | Func _ | Array _ | Cont _ -> None)
    | None -> None
  in
  (* Two operands that are the same bare local/global read (with nothing impure
     in between — an assignment would have cleared the stack). *)
  let same_read a b =
    match (a, b) with
    | LLocal i, LLocal j | LGlobal i, LGlobal j -> i = j
    | _ -> false
  in
  let check_int_binop (op : _ Ast.Text.instr) (o : Ast.int_bin_op) width st =
    let taut value =
      Error.tautological_comparison diagnostics ~location:op.info ~value
    in
    let no_effect () =
      Error.redundant_operation diagnostics ~location:op.info
        (Wax_utils.Message.text "This operation has no effect on its result.")
    in
    let always v =
      Error.redundant_operation diagnostics ~location:op.info
        Wax_utils.Message.(
          (text "This operation always yields" ++ int64 v) ^^ text ".")
    in
    (* [st] is [right :: left :: _]. The absorbing and identical-operand cases
       require both operands tracked (so the whole expression is effect-free): a
       constant on one side plus a second entry ([_ :: _]) for the other. The
       no-effect identity cases do not — see their note below. *)
    match (o, st) with
    | (Shl | Shr _), LInt n :: _
      when Int64.unsigned_compare n (Int64.of_int width) >= 0 ->
        Error.shift_overflow diagnostics ~location:op.info ~width n
    | (Div _ | Rem _), LInt 0L :: _ ->
        Error.division_by_zero diagnostics ~location:op.info
    (* An unsigned comparison against a constant zero, on either side. *)
    | Lt Ast.Unsigned, LInt 0L :: _ -> taut false (* a <u 0 *)
    | Ge Ast.Unsigned, LInt 0L :: _ -> taut true (* a >=u 0 *)
    | Gt Ast.Unsigned, _ :: LInt 0L :: _ -> taut false (* 0 >u a *)
    | Le Ast.Unsigned, _ :: LInt 0L :: _ -> taut true (* 0 <=u a *)
    (* Two identical integer operands: [a == a]/[a <= a]/[a >= a] hold, the
       strict and inequality forms do not. All comparisons here are integer (the
       float ones are a different opcode), so there is no NaN caveat. *)
    | (Eq | Le _ | Ge _), a :: b :: _ when same_read a b -> taut true
    | (Ne | Lt _ | Gt _), a :: b :: _ when same_read a b -> taut false
    (* Arithmetic identities: the result is the other operand unchanged. Unlike
       the absorbing cases below, the *identity* constant makes the operation a
       no-op whatever the other operand is — traps and effects of that operand
       are preserved either way — so an identity on the top of the stack fires
       even when the other operand is not tracked (an impure producer, e.g. a
       call, that cleared the stack). This matches the Wax linter, which reports
       these structurally. A left-identity ([0 + x]) still needs the top (its
       [x]) tracked to be seen at all. *)
    | Add, (LInt 0L :: _ | _ :: LInt 0L :: _) -> no_effect () (* x + 0 *)
    | (Sub | Shl | Shr _ | Rotl | Rotr), LInt 0L :: _ ->
        no_effect () (* x - 0, x << 0, … *)
    | Mul, (LInt 1L :: _ | _ :: LInt 1L :: _) -> no_effect () (* x * 1 *)
    | Div _, LInt 1L :: _ -> no_effect () (* x / 1 *)
    | (Or | Xor), (LInt 0L :: _ | _ :: LInt 0L :: _) ->
        no_effect () (* x | 0, x ^ 0 *)
    | (And | Or), a :: b :: _ when same_read a b ->
        no_effect () (* x & x, x | x *)
    (* Absorbing operands: the result is a constant, independent of the other. *)
    | Mul, (LInt 0L :: _ :: _ | _ :: LInt 0L :: _) -> always 0L (* x * 0 *)
    | And, (LInt 0L :: _ :: _ | _ :: LInt 0L :: _) -> always 0L (* x & 0 *)
    | Rem _, LInt 1L :: _ :: _ -> always 0L (* x % 1 *)
    | (Sub | Xor), a :: b :: _ when same_read a b ->
        always 0L (* x - x, x ^ x *)
    | _ -> ()
  in
  (* Check the operator [op] against the constant stack [st] (top = right
     operand / condition). *)
  let check_op (op : _ Ast.Text.instr) st =
    match op.desc with
    | BinOp (I32 o) -> check_int_binop op o 32 st
    | BinOp (I64 o) -> check_int_binop op o 64 st
    | UnOp (I32 (Trunc (_, sign))) -> (
        match st with
        | LFloat f :: _ when float_conversion_traps `I32 sign f ->
            Error.conversion_out_of_range diagnostics ~location:op.info
        | _ -> ())
    | UnOp (I64 (Trunc (_, sign))) -> (
        match st with
        | LFloat f :: _ when float_conversion_traps `I64 sign f ->
            Error.conversion_out_of_range diagnostics ~location:op.info
        | _ -> ())
    | Br_if _ | If _ | Select _ -> (
        match st with
        | LInt n :: _ ->
            Error.constant_condition diagnostics ~location:op.info
              ~value:(n <> 0L)
        | _ -> ())
    | Drop -> (
        match st with
        | (LInt _ | LFloat _ | LLocal _ | LGlobal _ | LPure) :: _ ->
            Error.unused_result diagnostics ~location:op.info
        | _ -> ())
    (* A self-assignment [x = x]: the value written is a fresh read of the same
       variable, with nothing impure in between (which would have cleared it). *)
    | LocalSet idx -> (
        match (st, Sequence.get_index_opt ctx.locals idx) with
        | LLocal j :: _, Some i when i = j ->
            Error.redundant_operation diagnostics ~location:op.info
              (Wax_utils.Message.text
                 "This assignment writes the local back to itself.")
        | _ -> ())
    | GlobalSet idx -> (
        match (st, Sequence.get_index_opt ctx.modul.globals idx) with
        | LGlobal j :: _, Some i when i = j ->
            Error.redundant_operation diagnostics ~location:op.info
              (Wax_utils.Message.text
                 "This assignment writes the global back to itself.")
        | _ -> ())
    | _ -> ()
  in
  (* An instruction after which control does not fall through. *)
  let rec is_diverging (i : _ Ast.Text.instr) =
    match i.desc with
    | Br _ | Br_table _ | Return | Unreachable | ReturnCall _ | ReturnCallRef _
    | ReturnCallIndirect _ | Throw _ | ThrowRef ->
        true
    | Folded (op, _) -> is_diverging op
    | _ -> false
  in
  (* How an instruction affects the lint's purity tracking. The match is
     exhaustive so a newly added instruction must be classified rather than
     silently defaulting. *)
  let classify (d : _ Ast.Text.instr_desc) =
    match d with
    (* Effect-free, non-trapping operators. Every value on the lint stack is
       pure by construction (impure/unhandled producers clear it), so the
       results are pure exactly when the stack is deep enough for the operands —
       [Pure (consumed, produced)] pops [consumed] operands and pushes [produced]
       pure values. *)
    | Const _ | LocalGet _ | GlobalGet _ | RefNull _ | RefFunc _ | MemorySize _
    | TableSize _ | VecConst _ | StructNewDefault _ ->
        `Pure (0, 1)
    | UnOp (I32 (Trunc _) | I64 (Trunc _)) ->
        `Impure (* trapping float→int conversion *)
    (* [struct.new_default] with a descriptor takes just the descriptor
       operand, so its arity is fixed at 1 like the other unary pure ops. *)
    | UnOp _ | I32WrapI64 | I64ExtendI32 _ | F32DemoteF64 | F64PromoteF32
    | ExternConvertAny | AnyConvertExtern | RefIsNull | RefTest _ | RefI31
    | VecUnOp _ | VecTest _ | VecBitmask _ | VecExtract _ | VecSplat _
    | ArrayNewDefault _ | StructNewDefaultDesc _ ->
        `Pure (1, 1)
    | BinOp (I32 (Div _ | Rem _) | I64 (Div _ | Rem _)) ->
        `Impure (* integer division/remainder may trap *)
    | BinOp _ | RefEq | VecBinOp _ | VecShift _ | VecReplace _ | VecShuffle _
    | ArrayNew _ ->
        `Pure (2, 1)
    | Select _ | VecTernOp _ | VecBitselect -> `Pure (3, 1)
    (* Wide integer arithmetic: pure, but produces a two-limb result. *)
    | Add128 | Sub128 -> `Pure (4, 2)
    | MulWide _ -> `Pure (2, 2)
    (* Allocations are effect-free and non-trapping (a dropped allocation is
       dead code): [array.new_fixed] takes its element count as an explicit
       immediate — unlike [struct.new], whose arity comes from the type — and
       [struct.new_default]/[array.new]/[array.new_default] above have a fixed
       arity too. *)
    | ArrayNewFixed (_, n) -> `Pure (Uint32.to_int n, 1)
    (* [struct.new] takes one operand per field; the arity comes from the type,
       looked up the same way folding does. [struct.new_desc] adds a descriptor
       operand. An unresolvable type falls through to [`Unhandled]. *)
    | StructNew idx -> (
        match struct_arity idx with
        | Some n -> `Pure (n, 1)
        | None -> `Unhandled)
    | StructNewDesc idx -> (
        match struct_arity idx with
        | Some n -> `Pure (n + 1, 1)
        | None -> `Unhandled)
    (* [nop] neither pops nor pushes, so it leaves the tracked stack unchanged
       rather than clearing it. *)
    | Nop -> `Neutral
    (* Has a side effect, transfers control, or may trap — never pure. *)
    | Unreachable | Throw _ | ThrowRef | Br _ | Br_if _ | Br_table _
    | Br_on_null _ | Br_on_non_null _ | Br_on_cast _ | Br_on_cast_fail _
    | Br_on_cast_desc_eq _ | Br_on_cast_desc_eq_fail _ | Return | Call _
    | CallRef _ | CallIndirect _ | ReturnCall _ | ReturnCallRef _
    | ReturnCallIndirect _ | ContNew _ | ContBind _ | Suspend _ | Resume _
    | ResumeThrow _ | ResumeThrowRef _ | Switch _ | LocalSet _ | LocalTee _
    | GlobalSet _ | Load _ | LoadS _ | Store _ | StoreS _ | Atomic _
    | AtomicFence | MemoryGrow _ | MemoryFill _ | MemoryCopy _ | MemoryInit _
    | DataDrop _ | TableGet _ | TableSet _ | TableGrow _ | TableFill _
    | TableCopy _ | TableInit _ | ElemDrop _ | RefAsNonNull | RefCast _
    | RefCastDescEq _ | RefGetDesc _ | StructGet _ | StructSet _
    | ArrayNewData _ | ArrayNewElem _ | ArrayGet _ | ArraySet _ | ArrayLen
    | ArrayFill _ | ArrayCopy _ | ArrayInitData _ | ArrayInitElem _ | I31Get _
    | VecLoad _ | VecStore _ | VecLoadLane _ | VecStoreLane _ | VecLoadSplat _
      ->
        `Impure
    (* Possibly pure, but not modelled here; clears the stack conservatively,
       kept distinct from [`Impure] to flag as future work. The block forms
       would need a whole-body purity analysis (and reasoning about branches
       escaping the block) to be treated as a value producer; [Drop]/[Folded]
       are handled structurally in [step]; the rest are Wax extensions. *)
    | Block _ | Loop _ | If _ | TryTable _ | Try _ | Drop | Folded _ | String _
    | Char _ | If_annotation _ ->
        `Unhandled
  in
  let rec drop_n n l =
    if n <= 0 then l else match l with [] -> [] | _ :: t -> drop_n (n - 1) t
  in
  let rec walk instrs =
    (* Dead code: after the first unconditional divergence, the next statement
       (if any) can never be reached. Reported once, at that statement. *)
    let rec dead = function
      | a :: (b :: _ as rest) ->
          if is_diverging a then
            Error.dead_code diagnostics ~location:b.info
              ~related:
                [
                  {
                    Wax_utils.Diagnostic.location = a.info;
                    message =
                      Wax_utils.Message.text "Control never returns from here.";
                  };
                ]
          else dead rest
      | _ -> ()
    in
    dead instrs;
    ignore (List.fold_left step [] instrs : lint_val list)
  and step st (i : _ Ast.Text.instr) =
    match i.desc with
    | Const (I32 s) | Const (I64 s) -> (
        match lint_int_value s with Some n -> LInt n :: st | None -> [])
    | Const (F32 s) | Const (F64 s) -> (
        match lint_float_value s with Some f -> LFloat f :: st | None -> [])
    (* A bare read is pure; track its resolved index so a comparison of two reads
       of the same variable is recognised as identical operands. *)
    | LocalGet idx -> (
        match Sequence.get_index_opt ctx.locals idx with
        | Some i -> LLocal i :: st
        | None -> LPure :: st)
    | GlobalGet idx -> (
        match Sequence.get_index_opt ctx.modul.globals idx with
        | Some i -> LGlobal i :: st
        | None -> LPure :: st)
    | Folded (op, operands) ->
        (* Folded form wraps every instruction, even a leaf constant, as
           [Folded (Const n, [])]. Flatten to "operands then head": process the
           operands, then the head as if it were the next flat instruction (so a
           folded constant pushes, and a folded operator checks and clears). *)
        let st' = List.fold_left step st operands in
        step st' op
    (* Propagate a constant float through a demote/promote so a trapping
       conversion of an out-of-f32-range constant ([<big> as f32 as i32_u]) is
       still caught: [f32.demote_f64] rounds to f32, [f64.promote_f32] is exact. *)
    | F32DemoteF64 -> (
        match st with
        | LFloat f :: rest -> LFloat (round_to_f32 f) :: rest
        | _ :: rest -> LPure :: rest
        | [] -> [])
    | F64PromoteF32 -> (
        match st with
        | (LFloat _ as v) :: rest -> v :: rest
        | _ :: rest -> LPure :: rest
        | [] -> [])
    | _ -> (
        check_op i st;
        recurse i;
        (* A pure operator whose operands are all pure yields pure results (so a
           later [drop] of one is flagged too); [local.get]/[global.get] and
           other zero-arity producers push a pure marker; anything else clears. *)
        match classify i.desc with
        | `Pure (consumed, produced) when List.length st >= consumed ->
            List.init produced (fun _ -> LPure) @ drop_n consumed st
        | `Neutral -> st
        | `Pure _ | `Impure | `Unhandled -> [])
  and recurse (i : _ Ast.Text.instr) =
    match i.desc with
    | Block { block; _ } | Loop { block; _ } | TryTable { block; _ } ->
        walk block.desc
    | If { if_block; else_block; _ } ->
        walk if_block.desc;
        walk else_block.desc
    | Try { block; catches; catch_all; _ } ->
        walk block.desc;
        List.iter (fun (_, b) -> walk b.Ast.desc) catches;
        Option.iter (fun b -> walk b.Ast.desc) catch_all
    | _ -> ()
  in
  (* The [eager-select] lint. A [select] evaluates both of its value operands,
     so a trapping or effectful operation among them runs even when the
     condition picks the other one (the footgun behind Wax's [?:]). Reuses
     [classify]'s purity table: a hazard is any [`Impure] operator except the
     casts already covered by other lints. Only handles the folded form, where
     each value operand is a distinct operand subtree — an unfolded [select]
     leaves its operands on the flat stream, out of reach here. *)
  let is_control (d : _ Ast.Text.instr_desc) =
    match d with
    | Block _ | Loop _ | If _ | TryTable _ | Try _ | Select _ | Br _ | Br_if _
    | Br_table _ | Br_on_null _ | Br_on_non_null _ | Br_on_cast _
    | Br_on_cast_fail _ | Br_on_cast_desc_eq _ | Br_on_cast_desc_eq_fail _
    | Return | Folded _ ->
        true
    | _ -> false
  in
  let is_eager_hazard (d : _ Ast.Text.instr_desc) =
    match d with
    (* Plain casts / trapping numeric conversions are reported by
       [cast-always-fails] and [constant-trap]; exclude them so the hazard set
       matches the Wax typer's [find_eager_hazard]. *)
    | UnOp (I32 (Trunc _) | I64 (Trunc _)) | RefCast _ -> false
    | _ -> ( match classify d with `Impure -> true | _ -> false)
  in
  (* The location of a hazard reached on the eagerly-evaluated spine of a
     [select] value operand, descending through pure operators but stopping at
     any nested control construct. *)
  let rec has_hazard (i : _ Ast.Text.instr) =
    match i.desc with
    | Folded (op, operands) ->
        if is_control op.desc then None
        else if is_eager_hazard op.desc then Some op.info
        else List.find_map has_hazard operands
    | d ->
        if (not (is_control d)) && is_eager_hazard d then Some i.info else None
  in
  let rec sel_walk (i : _ Ast.Text.instr) =
    (match i.desc with
    | Folded (({ desc = Select _; _ } as sel), [ v1; v2; _cond ]) ->
        List.iter
          (fun operand ->
            match has_hazard operand with
            | Some location ->
                Error.eager_select diagnostics ~location ~select:sel.info
            | None -> ())
          [ v1; v2 ]
    | _ -> ());
    match i.desc with
    | Folded (op, operands) ->
        List.iter sel_walk operands;
        sel_walk op
    | Block { block; _ } | Loop { block; _ } | TryTable { block; _ } ->
        List.iter sel_walk block.desc
    | If { if_block; else_block; _ } ->
        List.iter sel_walk if_block.desc;
        List.iter sel_walk else_block.desc
    | Try { block; catches; catch_all; _ } ->
        List.iter sel_walk block.desc;
        List.iter (fun (_, b) -> List.iter sel_walk b.Ast.desc) catches;
        Option.iter (fun b -> List.iter sel_walk b.Ast.desc) catch_all
    | _ -> ()
  in
  walk instrs;
  List.iter sel_walk instrs

(* Wire the forward reference used by [constant_expression] above. *)
let () = lint_constant_expr := lint_body

let functions ?(warn_unused = true) ctx fields =
  (* The index of the function about to be validated. [build_initial_env] hands
     out one function index per import-of-a-function and per [Func] field, in the
     order of this same expanded field list (a failed definition still claims its
     index), so counting them here stays aligned with it. *)
  let index = ref 0 in
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Import { desc = Func _; _ } -> incr index
      | Func { id = _; typ; locals = locs; instrs; exports; priority = _ } ->
          (* Claimed before anything can fail below, so a definition whose type
             does not resolve still advances the counter, as it does there. *)
          let self = !index in
          incr index;
          (* Attribute everything this definition resolves — its signature and
             local types as much as its body — to the function itself, so nothing
             a dead function names looks externally referenced. Reset once the
             whole pass is done (an early return below would skip a per-field
             reset, and the next [Func] sets it again anyway). *)
          ctx.types.origin <- From_function self;
          let>@ func_typ =
            let*@ typ = typeuse ctx.diagnostics ctx.types typ in
            match (Types.get_subtype ctx.subtyping_info typ).typ with
            | Func typ -> Some typ
            | _ ->
                Error.not_function_type ctx.diagnostics ~location:field.info;
                None
          in
          let return_types = func_typ.results in
          let return_source =
            snd (functype_sources (typeuse_functype ctx.types typ))
          in
          let locals = Sequence.make "local" in
          let initialized_locals = ref IntSet.empty in
          let i = ref 0 in
          (match typ with
          | _, Some { params; _ } ->
              Array.iter
                (fun p ->
                  let id, typ = p.Ast.desc in
                  initialized_locals := IntSet.add !i !initialized_locals;
                  incr i;
                  (* Resolved with muted diagnostics: this re-resolution only
                     runs when the typeuse above already resolved, so a broken
                     param type here was already reported — by [typeuse] for an
                     inline-only signature, by [check_syntax]'s inline check
                     when a named type is also given. *)
                  let interned =
                    match valtype (muted ctx.diagnostics) ctx.types typ with
                    | None ->
                        (* Dummy value *) Ref { nullable = false; typ = None_ }
                    | Some typ' -> typ'
                  in
                  Sequence.register locals id (interned, Plain typ))
                params
          | _ ->
              (* No inline parameter list: take the parameters' source types
                 from the referenced function type's definition. *)
              let param_source =
                fst (functype_sources (typeuse_functype ctx.types typ))
              in
              Array.iteri
                (fun j typ ->
                  initialized_locals := IntSet.add !i !initialized_locals;
                  incr i;
                  let source = param_source.(j) in
                  Sequence.register locals None (typ, source))
                func_typ.params);
          (* The locals declared by the function (not its parameters), recorded
             as (index, optional name, declaration location) so an unread one
             can be reported as unused after the body is validated. *)
          let declared_locals = ref [] in
          let poisoned_locals = ref IntSet.empty in
          List.iter
            (fun e ->
              let id, typ = e.Ast.desc in
              let typ' =
                match valtype ctx.diagnostics ctx.types typ with
                | None ->
                    (* The declared type did not resolve (already reported).
                       Poison this local so a use does not cascade a second
                       mismatch against the dummy; the dummy value is unused. *)
                    poisoned_locals := IntSet.add !i !poisoned_locals;
                    Ref { nullable = true; typ = Any }
                | Some typ -> typ
              in
              if is_defaultable typ' then
                initialized_locals := IntSet.add !i !initialized_locals;
              (* Point a named local's warning at its name; an unnamed one at
                 the whole declaration. *)
              let location =
                match id with Some id -> id.Ast.info | None -> e.Ast.info
              in
              declared_locals :=
                (!i, Option.map (fun id -> id.Ast.desc) id, location)
                :: !declared_locals;
              incr i;
              Sequence.register locals id (typ', Plain typ))
            locs;
          let ctx =
            {
              locals;
              control_types = [ (None, return_types, return_source, ref false) ];
              return_types;
              return_source;
              modul = ctx;
              initialized_locals = !initialized_locals;
              used_locals = ref IntSet.empty;
              poisoned_locals = !poisoned_locals;
              label_decls = ref [];
            }
          in
          with_empty_stack ctx.modul field.info
            (let* () = instructions ctx instrs in
             pop_args ctx ~kind:`Output field.info ~source:return_source
               return_types);
          (* A named local whose name starts with [_] is intentionally unused;
             unnamed locals are always reported. *)
          if warn_unused then
            List.iter
              (fun (idx, name, location) ->
                if
                  (not (IntSet.mem idx !(ctx.used_locals)))
                  && not
                       (match name with
                       | Some n -> String.length n > 0 && n.[0] = '_'
                       | None -> false)
                then Error.unused_local ctx.modul.diagnostics ~location name)
              (List.rev !declared_locals);
          (* A named block label never branched to. A name starting with [_] is
             intentionally unused. *)
          if warn_unused then
            List.iter
              (fun ((name : Ast.Text.name), used) ->
                if
                  (not !used)
                  && not (String.length name.desc > 0 && name.desc.[0] = '_')
                then
                  Error.unused_label ctx.modul.diagnostics ~location:name.info
                    name.desc)
              (List.rev !(ctx.label_decls));
          if warn_unused then lint_body ctx instrs;
          register_exports ctx.modul exports
      | _ -> ())
    (List.concat_map Ast_utils.expand_import_group fields);
  ctx.types.origin <- Root

(* Report a "Trojan Source" bidirectional control character in any string the
   module carries — an export/import name, a data segment, a string literal, a
   feature or conditional string. A subset of what [wasm-tools] rejects in
   string literals; gated by [warn_unused] like the other lints. *)
let lint_confusable ctx fields =
  let d = ctx.diagnostics in
  let check (s : Ast.Text.name) =
    match Wax_utils.Unicode.first_confusable s.Ast.desc with
    | Some u -> Error.confusable_unicode d ~location:s.Ast.info u
    | None -> ()
  in
  let check_str ~location s =
    match Wax_utils.Unicode.first_confusable s with
    | Some u -> Error.confusable_unicode d ~location u
    | None -> ()
  in
  let rec check_cond (c : Ast.cond) =
    match c with
    | Cond_string s -> check s
    | Cond_var _ | Cond_version _ -> ()
    | Cond_and l | Cond_or l -> List.iter check_cond l
    | Cond_not c -> check_cond c
    | Cond_cmp (_, a, b) ->
        check_cond a;
        check_cond b
  in
  let check_instr (i : _ Ast.Text.instr) =
    match i.desc with
    | String (_, pieces) -> List.iter check pieces
    | If_annotation { cond; _ } -> check_cond cond
    | _ -> ()
  in
  let check_body instrs = List.iter (Ast_utils.iter_instr check_instr) instrs in
  let check_data init =
    List.iter
      (fun (e : (Ast.Text.datavalelem, Ast.location) Ast.annotated) ->
        match e.Ast.desc with
        | Str s -> check_str ~location:e.Ast.info s
        | Numlist _ | V128list _ -> ())
      init
  in
  let rec walk fields =
    List.iter
      (fun (field : (_ Ast.Text.modulefield, Ast.location) Ast.annotated) ->
        match field.Ast.desc with
        | Export { name; _ } -> check name
        | Import { module_; name; exports; _ } ->
            check module_;
            check name;
            List.iter check exports
        | Import_group1 { module_; items } ->
            check module_;
            List.iter (fun (n, _, _) -> check n) items
        | Import_group2 { module_; items; _ } ->
            check module_;
            List.iter check items
        | Func { instrs; exports; _ } ->
            List.iter check exports;
            check_body instrs
        | Global { init; exports; _ } ->
            List.iter check exports;
            check_body init
        | Elem { init; _ } -> List.iter check_body init
        | Memory { init; exports; _ } ->
            List.iter check exports;
            Option.iter check_data init
        | Table { exports; _ } | Tag { exports; _ } -> List.iter check exports
        | Data { init; _ } -> check_data init
        | String_global { init; _ } -> List.iter check init
        | Feature_annotation n -> check n
        | Module_if_annotation { cond; then_fields; else_fields } ->
            check_cond cond;
            walk then_fields.Ast.desc;
            Option.iter
              (fun (f : (_, _) Ast.annotated) -> walk f.Ast.desc)
              else_fields
        | Types _ | Start _ -> ())
      fields
  in
  walk fields

let exports ctx fields =
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Export { name; kind; index } -> (
          register_exports ctx [ name ];
          (* An exported field is externally reachable, so mark it used for the
             [unused-field] warning. *)
          let mark used seq =
            Option.iter
              (fun i -> Hashtbl.replace used i ())
              (Sequence.get_index_opt seq index)
          in
          match kind with
          | Func ->
              ignore (Sequence.get ctx.diagnostics ctx.functions index);
              mark ctx.used_functions ctx.functions
          | Memory ->
              ignore (Sequence.get ctx.diagnostics ctx.memories index);
              mark ctx.used_memories ctx.memories
          | Table ->
              ignore (Sequence.get ctx.diagnostics ctx.tables index);
              mark ctx.used_tables ctx.tables
          | Tag ->
              ignore (Sequence.get ctx.diagnostics ctx.tags index);
              mark ctx.used_tags ctx.tags
          | Global ->
              ignore (Sequence.get ctx.diagnostics ctx.globals index);
              mark ctx.used_globals ctx.globals;
              (* The host may assign an exported mutable global. *)
              mark ctx.assigned_globals ctx.globals)
      | _ -> ())
    fields

let start ctx fields =
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Start idx -> (
          let*? ty, _, _, _ = Sequence.get ctx.diagnostics ctx.functions idx in
          (* The start function is externally reachable. *)
          Option.iter
            (fun i -> Hashtbl.replace ctx.used_functions i ())
            (Sequence.get_index_opt ctx.functions idx);
          match (Types.get_subtype ctx.subtyping_info ty).typ with
          | Struct _ | Array _ | Cont _ ->
              Error.not_function_type ctx.diagnostics ~location:idx.info
          | Func { params; results } ->
              if not (params = [||] && results = [||]) then
                Error.start_function_signature ctx.diagnostics
                  ~location:idx.info)
      | _ -> ())
    fields

(* The functions that can actually run: those referenced from a root context
   (recorded in [used_functions] — an export, the start function, a global or
   table initializer, an element segment), plus everything they transitively
   call or take a [ref.func] of.

   Reachability, rather than "is referenced somewhere", is what makes the lint
   see a dead *cycle*: two functions that only call each other reference one
   another, so a presence check finds both used, yet neither can ever run. The
   same goes for anything only such a cycle reaches. An escaping [ref.func] is
   treated as a call, since where the reference ends up is not tracked — so the
   analysis stays conservative: it never reports a function that might run. *)
let reachable_functions ctx =
  let calls = Hashtbl.create 16 in
  List.iter
    (fun (caller, target) ->
      match target with
      | Ref_function callee -> Hashtbl.add calls caller callee
      | Ref_global _ | Ref_memory _ | Ref_table _ | Ref_tag _ | Ref_data _
      | Ref_elem _ ->
          ())
    ctx.body_references;
  let live = Hashtbl.create 16 in
  let rec visit f =
    if not (Hashtbl.mem live f) then begin
      Hashtbl.replace live f ();
      List.iter visit (Hashtbl.find_all calls f)
    end
  in
  Hashtbl.iter (fun f () -> visit f) ctx.used_functions;
  live

(* The type definitions that anything reachable names. Seeded by the type
   references made from a module-level context or from a function that can run,
   then closed over the references a type definition makes through its own
   components — so a rec group nothing outside it names is dead as a whole, its
   mutual references notwithstanding.

   A reference was recorded as written, so map it back to the definition it names:
   a numeric one is that index, a symbolic one goes through the name the
   definition was declared with. Deduplication is why references are not
   canonicalised earlier — two structurally equal named types share one canonical
   index, and a reference to either would otherwise mark both. *)
let reachable_types ctx ~live_functions =
  let index_of_name = Hashtbl.create 16 in
  Hashtbl.iter
    (fun i ((def_idx : Ast.Text.idx), _) ->
      match def_idx.desc with
      | Id name -> Hashtbl.replace index_of_name name i
      | Num _ -> ())
    ctx.types.type_defs;
  let target = function
    | By_index i -> Some i
    | By_name n -> Hashtbl.find_opt index_of_name n
  in
  (* Every source definition sharing a canonical index, for the by-canonical
     references (see [canonical_type_references]). *)
  let indices_of_canonical = Hashtbl.create 16 in
  Hashtbl.iter
    (fun i _ ->
      match Hashtbl.find_opt ctx.types.index_mapping (Uint32.of_int i) with
      | Some (Types.Def id, _, _, _) -> Hashtbl.add indices_of_canonical id i
      | Some (Types.Rec _, _, _, _) | None -> ())
    ctx.types.type_defs;
  let components = Hashtbl.create 16 in
  let seeds = ref [] in
  (* A reference made by a type definition is an edge from it; one made from a
     module-level context, or from a function that can run, is a seed. *)
  let record origin targets =
    match origin with
    | From_type src -> List.iter (Hashtbl.add components src) targets
    | Root -> seeds := targets @ !seeds
    | From_function f ->
        if Hashtbl.mem live_functions f then seeds := targets @ !seeds
    | Ignored -> ()
  in
  List.iter
    (fun (origin, r) -> record origin (Option.to_list (target r)))
    ctx.types.type_references;
  List.iter
    (fun (origin, id) ->
      record origin (Hashtbl.find_all indices_of_canonical id))
    ctx.types.canonical_type_references;
  let live = Hashtbl.create 16 in
  let rec visit t =
    if not (Hashtbl.mem live t) then begin
      Hashtbl.replace live t ();
      List.iter visit (Hashtbl.find_all components t)
    end
  in
  List.iter visit !seeds;
  live

(* Report module-defined fields that nothing reachable references, exported, or
   used as the start function (the module-level analog of an unused local), and
   likewise for imports; then the mutable globals that are never assigned.
   References are collected during validation — roots into the [used_*] tables,
   body references into [body_references] — and a name starting with [_] is
   intentionally unused. Runs after every other pass so all references have been
   seen. *)
let unused_fields ctx =
  if not ctx.warn_unused then ()
  else
    let live_functions = reachable_functions ctx in
    (* A field is used if a root context references it, or if a function that can
       actually run does. A reference from dead code keeps nothing alive. *)
    let used_in roots select =
      let t = Hashtbl.copy roots in
      List.iter
        (fun (caller, target) ->
          if Hashtbl.mem live_functions caller then
            Option.iter (fun i -> Hashtbl.replace t i ()) (select target))
        ctx.body_references;
      t
    in
    let used_globals =
      used_in ctx.used_globals (function Ref_global i -> Some i | _ -> None)
    and used_memories =
      used_in ctx.used_memories (function Ref_memory i -> Some i | _ -> None)
    and used_tables =
      used_in ctx.used_tables (function Ref_table i -> Some i | _ -> None)
    and used_tags =
      used_in ctx.used_tags (function Ref_tag i -> Some i | _ -> None)
    and used_data =
      used_in ctx.used_data (function Ref_data i -> Some i | _ -> None)
    and used_elem =
      used_in ctx.used_elem (function Ref_elem i -> Some i | _ -> None)
    in
    let intentional_name = function
      | Some n -> String.length n > 0 && n.[0] = '_'
      | None -> false
    in
    let intentional (name : Ast.Text.name option) =
      intentional_name (Option.map (fun (n : Ast.Text.name) -> n.desc) name)
    in
    let report emit used kind decls =
      List.iter
        (fun (idx, (name : Ast.Text.name option), location) ->
          if (not (Hashtbl.mem used idx)) && not (intentional name) then
            emit ctx.diagnostics ~location kind
              (Option.map (fun (n : Ast.Text.name) -> n.desc) name))
        (List.rev decls)
    in
    report Error.unused_field live_functions "function" ctx.defined_functions;
    report Error.unused_field used_globals "global" ctx.defined_globals;
    report Error.unused_field used_memories "memory" ctx.defined_memories;
    report Error.unused_field used_tables "table" ctx.defined_tables;
    report Error.unused_field used_tags "tag" ctx.defined_tags;
    report Error.unused_field used_data "data segment" ctx.defined_data;
    report Error.unused_field used_elem "element segment" ctx.defined_elem;
    report Error.unused_import live_functions "function" ctx.imported_functions;
    report Error.unused_import used_globals "global" ctx.imported_globals;
    report Error.unused_import used_memories "memory" ctx.imported_memories;
    report Error.unused_import used_tables "table" ctx.imported_tables;
    report Error.unused_import used_tags "tag" ctx.imported_tags;
    (* A type definition nothing reachable names, reported at the definition and
       in source (index) order like the rest. Only source definitions are
       candidates: the implicit function types interned for an inline block
       signature have no [type_defs] entry, so they are never reported. *)
    let live_types = reachable_types ctx ~live_functions in
    List.iter
      (fun (i, (def_idx : Ast.Text.idx)) ->
        let name = match def_idx.desc with Id n -> Some n | Num _ -> None in
        if (not (Hashtbl.mem live_types i)) && not (intentional_name name) then
          Error.unused_field ctx.diagnostics ~location:def_idx.info "type" name)
      (List.sort
         (fun (a, _) (b, _) -> compare a b)
         (Hashtbl.fold
            (fun i (def_idx, _) acc -> (i, def_idx) :: acc)
            ctx.types.type_defs []));
    (* A mutable global never assigned could be immutable. A global that is not
       used at all is already reported as [unused-field], so do not pile a second
       diagnostic on the same declaration. *)
    List.iter
      (fun (idx, (name : Ast.Text.name option), location) ->
        if
          Hashtbl.mem used_globals idx
          && (not (Hashtbl.mem ctx.assigned_globals idx))
          && not (intentional name)
        then
          Error.unnecessary_mut ctx.diagnostics ~location
            (Option.map (fun (n : Ast.Text.name) -> n.desc) name))
      (List.rev ctx.mutable_globals)

(*** Whole-module validation ***)

(* Syntactic well-formedness checks that the stack-based validation does not
   cover: duplicate identifiers in each namespace, an inline type annotation
   that disagrees with the type it names, duplicate parameter/local names, and a
   second start function. Type references are resolved through [ctx], the type
   context the rest of validation has already built, which handles recursive and
   forward references correctly. *)
let check_syntax ctx lst =
  let types = Hashtbl.create 16 in
  let functions = Hashtbl.create 16 in
  let memories = Hashtbl.create 16 in
  let tables = Hashtbl.create 16 in
  let globals = Hashtbl.create 16 in
  let tags = Hashtbl.create 16 in
  let elems = Hashtbl.create 16 in
  let datas = Hashtbl.create 16 in
  let check_unbound tbl kind id =
    let>@ id : Ast.Text.name = id in
    match Hashtbl.find_opt tbl id.desc with
    | Some prev_loc ->
        Error.index_already_bound ctx.diagnostics ~location:id.info ~prev_loc
          kind id
    | None -> Hashtbl.add tbl id.desc id.info
  in
  let iter_instrs f instrs =
    List.iter (Ast_utils.iter_instr (fun i -> f i.desc)) instrs
  in
  (* An inline type annotation [(type idx) (param ...) (result ...)] must name a
     function type whose signature equals the inline one. The reference is
     resolved with muted diagnostics — an unbound or non-function type is
     reported by the pass that owns the typeuse ([build_initial_env] for an
     import or tag, [functions] for a function, the body validation for a block
     or [call_indirect]); only the inline/named disagreement is this check's to
     report. The inline signature itself is built loudly: when a reference is
     also given, [typeuse] ignores the inline form, so an unbound type inside it
     is reported nowhere else. *)
  let check_inline_type idx target =
    let>@ gidx = resolve_type_index (muted ctx.diagnostics) ctx.types idx in
    match (Types.get_subtype ctx.subtyping_info gidx).typ with
    | Func f -> (
        match functype ctx.diagnostics ctx.types target with
        | Some f' ->
            if f <> f' then
              (* Render the definition's declared source signature — its concrete
                 references have no source name to reconstruct from the resolved
                 [f] (see [inline_function_type_mismatch]). The index resolved to
                 a [Func] above, so its source comptype is a [Func] too. *)
              let params, results =
                match lookup_source_comptype ctx.types idx with
                | Some (Func sft) -> functype_sources sft
                | _ -> assert false
              in
              Error.inline_function_type_mismatch ctx.diagnostics
                ~location:idx.Ast.info ~params ~results
        | None -> ())
    | Struct _ | Array _ | Cont _ -> ()
  in
  let check_instr_inline desc =
    let check_typeuse = function
      | Ast.Text.Typeuse (Some idx, Some ft) -> check_inline_type idx ft
      | _ -> ()
    in
    match desc with
    | Ast.Text.Block { typ = Some t; _ }
    | Ast.Text.Loop { typ = Some t; _ }
    | Ast.Text.If { typ = Some t; _ }
    | Ast.Text.Try { typ = Some t; _ }
    | Ast.Text.TryTable { typ = Some t; _ } ->
        check_typeuse t
    | CallIndirect (_, (Some idx, Some ft)) -> check_inline_type idx ft
    | ReturnCallIndirect (_, (Some idx, Some ft)) -> check_inline_type idx ft
    | _ -> ()
  in
  let check_duplicate_locals typ locals =
    let param_ids =
      match snd typ with
      | Some { Ast.Text.params; _ } ->
          Array.to_list (Array.map (fun p -> fst p.Ast.desc) params)
      | None -> []
    in
    let local_ids = List.map (fun e -> fst e.Ast.desc) locals in
    let seen = Hashtbl.create 16 in
    List.iter
      (fun id ->
        let*? id : Ast.Text.name = id in
        match Hashtbl.find_opt seen id.desc with
        | Some prev_loc ->
            Error.duplicate_local ctx.diagnostics ~location:id.Ast.info
              ~prev_loc id.desc
        | None -> Hashtbl.add seen id.desc id.Ast.info)
      (param_ids @ local_ids)
  in
  let check_import id (desc : Ast.Text.importdesc) =
    let tbl, kind =
      match desc with
      | Func _ -> (functions, "function")
      | Memory _ -> (memories, "memory")
      | Table _ -> (tables, "table")
      | Global _ -> (globals, "global")
      | Tag _ -> (tags, "tag")
    in
    check_unbound tbl kind id;
    match desc with
    | Func { typ = Some idx, Some sign; _ } -> check_inline_type idx sign
    | Tag (Some idx, Some sign) -> check_inline_type idx sign
    | _ -> ()
  in
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Types lst ->
          Array.iter
            (fun e ->
              check_unbound types "type" (fst e.Ast.desc);
              match (snd e.Ast.desc).Ast.Text.typ with
              | Ast.Text.Types.Func _ | Array _ | Cont _ -> ()
              | Struct lst ->
                  let fields = Hashtbl.create 16 in
                  Array.iter
                    (fun e -> check_unbound fields "field" (fst e.Ast.desc))
                    lst)
            lst
      | Import { id; desc; _ } -> check_import id desc
      | Import_group1 { items; _ } ->
          List.iter (fun (_, id, desc) -> check_import id desc) items
      | Import_group2 { desc; items; _ } ->
          List.iter (fun _ -> check_import None desc) items
      | Func { id; typ; locals; instrs; _ } ->
          check_unbound functions "function" id;
          (match typ with
          | Some idx, Some sign -> check_inline_type idx sign
          | _ -> ());
          check_duplicate_locals typ locals;
          iter_instrs check_instr_inline instrs
      | Memory { id; _ } -> check_unbound memories "memory" id
      | Table { id; _ } -> check_unbound tables "table" id
      | Tag { id; typ = Some idx, Some sign; _ } ->
          check_unbound tags "tag" id;
          check_inline_type idx sign
      | Tag { id; _ } -> check_unbound tags "tag" id
      | Global { id; _ } -> check_unbound globals "global" id
      | Export _ | Start _ -> ()
      | Elem { id; _ } -> check_unbound elems "elem" id
      | Data { id; _ } -> check_unbound datas "data" id
      | String_global { id; _ } -> check_unbound globals "global" (Some id)
      | Feature_annotation _ | Module_if_annotation _ -> ())
    lst;
  match
    List.filter
      (fun field ->
        match field.Ast.desc with Ast.Text.Start _ -> true | _ -> false)
      lst
  with
  | first :: second :: _ ->
      Error.multiple_start ctx.diagnostics ~location:second.Ast.info
        ~prev_loc:first.Ast.info
  | _ -> ()

let validate_configuration ?(warn_unused = true)
    ?(features = Wax_utils.Feature.default ()) diagnostics (_, fields) =
  let type_context =
    {
      types = Types.create ();
      last_index = 0;
      index_mapping = Hashtbl.create 16;
      label_mapping = Hashtbl.create 16;
      poisoned_index = Hashtbl.create 16;
      poisoned_label = Hashtbl.create 16;
      type_defs = Hashtbl.create 16;
      descriptor_source = Hashtbl.create 16;
      features;
      origin = Root;
      type_references = [];
      canonical_type_references = [];
      record_references = warn_unused;
    }
  in
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Types rectype -> add_type diagnostics type_context rectype
      | _ -> ())
    fields;
  collect_implicit_types diagnostics type_context fields;
  (* Make the type context available to [push] for go-to-type-definition
     recording (editor mode only; reset in [f]). *)
  if !recorded_types <> None then sink_type_context := Some type_context;
  (* Register the implicit [<string>] array type ([mut i8]) up front, so that
     validating an unnamed [@string] — which looks the type up via [string_type]
     ([add_rectype], idempotent) — gets an index within [subtyping_info] instead
     of one appended past the snapshot taken here. *)
  ignore (string_type type_context : Types.Id.t);
  let ctx =
    {
      diagnostics;
      types = type_context;
      subtyping_info = Types.subtyping_info type_context.types;
      functions = Sequence.make "function";
      memories = Sequence.make "memory";
      tables = Sequence.make "table";
      globals = Sequence.make "global";
      tags = Sequence.make "tag";
      data = Sequence.make "data segment";
      elem = Sequence.make "elem segment";
      exports = Hashtbl.create 16;
      refs = Hashtbl.create 16;
      used_functions = Hashtbl.create 16;
      used_globals = Hashtbl.create 16;
      used_memories = Hashtbl.create 16;
      used_tables = Hashtbl.create 16;
      used_tags = Hashtbl.create 16;
      used_data = Hashtbl.create 16;
      used_elem = Hashtbl.create 16;
      body_references = [];
      assigned_globals = Hashtbl.create 16;
      defined_functions = [];
      defined_globals = [];
      defined_memories = [];
      defined_tables = [];
      defined_tags = [];
      defined_data = [];
      defined_elem = [];
      mutable_globals = [];
      imported_functions = [];
      imported_globals = [];
      imported_memories = [];
      imported_tables = [];
      imported_tags = [];
      warn_unused;
    }
  in
  check_type_definitions ctx;
  build_initial_env ctx fields;
  let ctx =
    { ctx with subtyping_info = Types.subtyping_info type_context.types }
  in
  check_syntax ctx fields;
  tables_and_memories ctx fields;
  globals ctx fields;
  segments ctx fields;
  declared_func_exports ctx fields;
  functions ~warn_unused ctx fields;
  exports ctx fields;
  start ctx fields;
  if warn_unused then lint_confusable ctx fields;
  unused_fields ctx

(* Path-sensitive validation of conditional annotations.

   A module containing [(@if ...)] conditionals denotes one concrete module per
   "configuration" (a choice of branch at every reachable conditional). We
   explore every reachable configuration (via {!Cond_explore.check_all}),
   specializing the module for each — splicing in the selected branches to obtain
   a conditional-free module — validating it with {!validate_configuration}, and
   reporting each distinct error once, annotated with the minimal assumption
   under which it occurs. *)

(*** Conditional compilation and entry point ***)

(* Walk through every nested instruction (branch hints included) via the
   canonical [Ast_utils.fold_instr], so a conditional buried inside a
   branch-hinted branch is not missed. *)
let instr_has_conditional (i : _ Ast.Text.instr) =
  Ast_utils.fold_instr
    (fun found (i : _ Ast.Text.instr) ->
      found || match i.desc with If_annotation _ -> true | _ -> false)
    false i

let expr_has_conditional e = List.exists instr_has_conditional e

(* Exhaustive over [modulefield]: every instruction list a field can carry is
   inspected (including the offset expression of an active [data]/[elem]
   segment), and a new field variant is a compile error rather than a silent
   miss. Must stay in sync with [specialize] below, which walks the same lists. *)
let field_has_conditional (f : (_ Ast.Text.modulefield, _) Ast.annotated) =
  match f.desc with
  | Module_if_annotation _ -> true
  | Func { instrs; _ } -> expr_has_conditional instrs
  | Global { init; _ } -> expr_has_conditional init
  | Table { init; _ } -> (
      match init with
      | Init_default -> false
      | Init_expr e -> expr_has_conditional e
      | Init_segment segs -> List.exists expr_has_conditional segs)
  | Elem { init; mode; _ } -> (
      List.exists expr_has_conditional init
      ||
      match mode with
      | Active (_, offset) -> expr_has_conditional offset
      | Passive | Declare -> false)
  | Data { mode; _ } -> (
      match mode with
      | Active (_, offset) -> expr_has_conditional offset
      | Passive -> false)
  | Types _ | Import _ | Import_group1 _ | Import_group2 _ | Memory _ | Tag _
  | Export _ | Start _ | String_global _ | Feature_annotation _ ->
      false

(* Specialize a module for one configuration: resolve every conditional using
   the assumption [asm], splicing in the selected branch. Undetermined
   conditionals select [@then] and [enqueue] the [@else] configuration; each
   selected branch literal is passed to [record] to build the configuration's
   full assumption. *)
let specialize env diagnostics ~enqueue ~record asm0 fields =
  (* Resolve one conditional and return both the specialized branch and the
     assumption that holds afterwards. Each branch is taken only if it is
     reachable under [asm] (its conjunction with the branch condition is
     satisfiable); an unreachable branch is pruned, so we never explore an
     infeasible configuration. The surviving assumption is threaded into the
     following siblings, so e.g. once [cond1] forces [$wasi], a sibling
     [(@if (not $wasi) …)] has its [@then] pruned. *)
  let choose asm cond ~location ~then_branch ~else_branch =
    let c = Cond_solver.of_cond env diagnostics ~location cond in
    let then_asm = Cond_solver.and_ asm c
    and else_asm = Cond_solver.and_ asm (Cond_solver.not_ c) in
    if not (Cond_solver.is_satisfiable then_asm) then (
      record (Cond_solver.not_ c);
      (else_branch else_asm, else_asm))
    else if not (Cond_solver.is_satisfiable else_asm) then (
      record c;
      (then_branch then_asm, then_asm))
    else (
      enqueue else_asm;
      record c;
      (then_branch then_asm, then_asm))
  in
  let rec sfields asm fl =
    match fl with
    | [] -> []
    | f :: rest ->
        let fields, asm = sfield asm f in
        fields @ sfields asm rest
  and sfield asm (f : (_ Ast.Text.modulefield, _) Ast.annotated) =
    match f.desc with
    | Module_if_annotation { cond; then_fields; else_fields } ->
        choose asm cond ~location:f.info
          ~then_branch:(fun asm' -> sfields asm' then_fields.desc)
          ~else_branch:(fun asm' ->
            match else_fields with Some e -> sfields asm' e.desc | None -> [])
    | Func { id; typ; locals; instrs; exports; priority } ->
        let desc : _ Ast.Text.modulefield =
          Func
            { id; typ; locals; instrs = sinstrs asm instrs; exports; priority }
        in
        ([ { f with desc } ], asm)
    | Global { id; typ; init; exports } ->
        let desc : _ Ast.Text.modulefield =
          Global { id; typ; init = sinstrs asm init; exports }
        in
        ([ { f with desc } ], asm)
    | Table { id; typ; init; exports } ->
        let init : _ Ast.Text.tableinit =
          match init with
          | Init_default -> Init_default
          | Init_expr e -> Init_expr (sinstrs asm e)
          | Init_segment segs -> Init_segment (List.map (sinstrs asm) segs)
        in
        let desc : _ Ast.Text.modulefield = Table { id; typ; init; exports } in
        ([ { f with desc } ], asm)
    | Elem { id; typ; init; mode } ->
        let mode : _ Ast.Text.elemmode =
          match mode with
          | Active (idx, e) -> Active (idx, sinstrs asm e)
          | (Passive | Declare) as mode -> mode
        in
        let desc : _ Ast.Text.modulefield =
          Elem { id; typ; init = List.map (sinstrs asm) init; mode }
        in
        ([ { f with desc } ], asm)
    | Data { id; init; mode } ->
        let mode : _ Ast.Text.datamode =
          match mode with
          | Active (idx, e) -> Active (idx, sinstrs asm e)
          | Passive as mode -> mode
        in
        ([ { f with desc = Data { id; init; mode } } ], asm)
    | Types _ | Import _ | Import_group1 _ | Import_group2 _ | Memory _ | Tag _
    | Export _ | Start _ | String_global _ | Feature_annotation _ ->
        ([ f ], asm)
  and sinstrs asm l =
    match l with
    | [] -> []
    | i :: rest ->
        let instrs, asm = sinstr asm i in
        instrs @ sinstrs asm rest
  and sinstr asm (i : _ Ast.Text.instr) =
    match i.desc with
    | If_annotation { cond; then_body; else_body } ->
        choose asm cond ~location:i.info
          ~then_branch:(fun asm' -> sinstrs asm' then_body.desc)
          ~else_branch:(fun asm' ->
            match else_body with Some e -> sinstrs asm' e.desc | None -> [])
    | desc -> ([ { i with desc = sstructured asm desc } ], asm)
  and sstructured asm (desc : _ Ast.Text.instr_desc) =
    match desc with
    | Block b ->
        Block
          { b with block = { b.block with desc = sinstrs asm b.block.desc } }
    | Loop b ->
        Loop { b with block = { b.block with desc = sinstrs asm b.block.desc } }
    | If b ->
        If
          {
            b with
            if_block = { b.if_block with desc = sinstrs asm b.if_block.desc };
            else_block =
              { b.else_block with desc = sinstrs asm b.else_block.desc };
          }
    | TryTable b ->
        TryTable
          { b with block = { b.block with desc = sinstrs asm b.block.desc } }
    | Try b ->
        Try
          {
            b with
            block = { b.block with desc = sinstrs asm b.block.desc };
            catches =
              List.map
                (fun (idx, l) ->
                  (idx, { l with Ast.desc = sinstrs asm l.Ast.desc }))
                b.catches;
            catch_all =
              Option.map
                (fun b -> { b with Ast.desc = sinstrs asm b.Ast.desc })
                b.catch_all;
          }
    | Folded (h, l) ->
        Folded ({ h with desc = sstructured asm h.desc }, sinstrs asm l)
    (* Every instruction that carries no nested instruction is returned as-is.
       Enumerated rather than caught by a wildcard so a future instruction that
       nests others is a compile error here instead of silently escaping
       specialization. *)
    | ( Unreachable | Nop | Throw _ | ThrowRef | ContNew _ | ContBind _
      | Suspend _ | Resume _ | ResumeThrow _ | ResumeThrowRef _ | Switch _
      | Br _ | Br_if _ | Br_table _ | Br_on_null _ | Br_on_non_null _
      | Br_on_cast _ | Br_on_cast_fail _ | Br_on_cast_desc_eq _
      | Br_on_cast_desc_eq_fail _ | Return | Call _ | CallRef _ | ReturnCall _
      | ReturnCallRef _ | Drop | Select _ | LocalGet _ | LocalSet _ | LocalTee _
      | GlobalGet _ | GlobalSet _ | Load _ | LoadS _ | Store _ | StoreS _
      | Atomic _ | AtomicFence | MemorySize _ | MemoryGrow _ | MemoryFill _
      | MemoryCopy _ | MemoryInit _ | DataDrop _ | TableGet _ | TableSet _
      | TableSize _ | TableGrow _ | TableFill _ | TableCopy _ | TableInit _
      | ElemDrop _ | RefNull _ | RefFunc _ | RefIsNull | RefAsNonNull | RefEq
      | RefTest _ | RefCast _ | RefCastDescEq _ | RefGetDesc _ | StructNew _
      | StructNewDefault _ | StructNewDesc _ | StructNewDefaultDesc _
      | StructGet _ | StructSet _ | ArrayNew _ | ArrayNewDefault _
      | ArrayNewFixed _ | ArrayNewData _ | ArrayNewElem _ | ArrayGet _
      | ArraySet _ | ArrayLen | ArrayFill _ | ArrayCopy _ | ArrayInitData _
      | ArrayInitElem _ | RefI31 | I31Get _ | Const _ | UnOp _ | BinOp _
      | Add128 | Sub128 | MulWide _ | I32WrapI64 | I64ExtendI32 _ | F32DemoteF64
      | F64PromoteF32 | ExternConvertAny | AnyConvertExtern | VecBitselect
      | VecConst _ | VecUnOp _ | VecBinOp _ | VecTest _ | VecShift _
      | VecBitmask _ | VecLoad _ | VecStore _ | VecLoadLane _ | VecStoreLane _
      | VecLoadSplat _ | VecExtract _ | VecReplace _ | VecSplat _ | VecShuffle _
      | VecTernOp _ | Char _ | CallIndirect _ | ReturnCallIndirect _ | String _
      | If_annotation _ ) as desc ->
        desc
  in
  sfields asm0 fields

(* WebAssembly requires every import to precede all non-import definitions
   (functions, tables, memories, globals, tags). Report any import that follows
   such a definition. *)
let check_import_order diagnostics fields =
  ignore
    (List.fold_left
       (fun can_import (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
         match (can_import, field.desc) with
         | ( Some (previous, prev_loc),
             (Import _ | Import_group1 _ | Import_group2 _) ) ->
             Error.import_after_definition diagnostics ~location:field.info
               ~prev_loc previous;
             can_import
         | None, Func _ -> Some ("function", field.info)
         | None, Memory _ -> Some ("memory", field.info)
         | None, Table _ -> Some ("table", field.info)
         | None, Tag _ -> Some ("tag", field.info)
         | None, Global _ -> Some ("global", field.info)
         | None, String_global _ -> Some ("string", field.info)
         | ( Some _,
             (Func _ | Memory _ | Table _ | Tag _ | Global _ | String_global _)
           )
         | None, (Import _ | Import_group1 _ | Import_group2 _)
         | ( _,
             ( Types _ | Export _ | Start _ | Elem _ | Data _
             | Feature_annotation _ | Module_if_annotation _ ) ) ->
             can_import)
       None fields)

(* Apply the module's [(@feature "…")] declarations to [features]: each
   declared feature is enabled, in union with the command-line configuration —
   unless the command line explicitly disabled it, which is a conflict reported
   once, at the annotation. Runs at the entry point, before anything consults
   [is_enabled]. Only top-level annotations count: the annotation states a fact
   about the whole module, so it is not conditional. Mirrors the Wax typer's
   [apply_declared_features]. *)
let apply_declared_features diagnostics features fields =
  List.iter
    (fun (field : (_ Ast.Text.modulefield, _) Ast.annotated) ->
      match field.desc with
      | Ast.Text.Feature_annotation name -> (
          let location = name.Ast.info in
          match Wax_utils.Feature.of_name name.Ast.desc with
          | None -> Error.unknown_feature diagnostics ~location name.Ast.desc
          | Some feature ->
              if Wax_utils.Feature.explicitly_disabled features feature then
                Error.feature_conflict diagnostics ~location feature;
              (* Enable it even on a conflict: the error has been reported
                 once, at the annotation; without this every gated construct
                 below would error too. *)
              Wax_utils.Feature.declare features feature)
      | _ -> ())
    fields

let f ?(warn_unused = true) ?(features = Wax_utils.Feature.default ())
    ?record_types diagnostics ((name, fields) as modul) =
  Wax_utils.Debug.timed "validate" @@ fun () ->
  recorded_types := record_types;
  sink_config := 0;
  Fun.protect ~finally:(fun () ->
      recorded_types := None;
      sink_type_context := None)
  @@ fun () ->
  apply_declared_features diagnostics features fields;
  check_import_order diagnostics fields;
  if not (List.exists field_has_conditional fields) then
    validate_configuration ~warn_unused ~features diagnostics modul
  else
    (* Tag each explored configuration's recorded types with a distinct index,
       so a config-varying span's alternatives stay separable from a single
       configuration's multi-result tuple. *)
    let config = ref (-1) in
    Cond_explore.check_all diagnostics
      ?truncation_location:
        (match fields with f :: _ -> Some f.Ast.info | [] -> None)
      ~specialize:(fun env asm ~enqueue ~record ->
        (name, specialize env diagnostics ~enqueue ~record asm fields))
      ~check:(fun diagnostics modul ->
        incr config;
        sink_config := !config;
        validate_configuration ~warn_unused ~features diagnostics modul)
      ()
