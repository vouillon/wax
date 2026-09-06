open Ast
module Cond = Wax_wasm.Cond_solver
module Nz = Wax_wasm.Types.Normalized

(* The Printer-native output printers, captured before [open Infer] shadows
   [Output] with its [Format]-based wrappers. *)
module Printer_output = Output
open Infer
open Typing_env

type typed_module_annotation = Typing_env.typed_module_annotation
type inferred_module_annotation = Typing_env.inferred_module_annotation

type hover_target = Typing_env.hover_target =
  | Value_type of inferred_valtype
  | Type_def of subtype

type reference = Typing_env.reference = {
  use : Ast.location;
  definitions : Ast.location list;
  hover : hover_target option;
}

(*** Diagnostics ***)

let loc_first_char loc =
  let loc_start = loc.loc_start in
  { loc with loc_end = { loc_start with pos_cnum = loc_start.pos_cnum + 1 } }

let loc_last_char loc =
  let loc_end = loc.loc_end in
  { loc with loc_start = { loc_end with pos_cnum = loc_end.pos_cnum - 1 } }

module Error = struct
  open Wax_utils

  (* Message-building combinators (see {!Wax_utils.Message}). Prose is [text],
     joined with [++] (soft, wrap-point space) or [^^] (no space). An emphasized
     atom — [name] an identifier, [kw] a code token, [num] a numeric literal,
     [typ] an inferred type — is coloured when the theme is coloured and quoted
     ['…'] when it is not (so JSON/short, always uncoloured, are always quoted). *)
  let text = Message.text
  let ( ++ ) = Message.( ++ )
  let ( ^^ ) = Message.( ^^ )
  let name x = Message.ident x.Wax_utils.Ast.desc
  let kw = Message.code
  let num s = Message.styled Colors.Constant s

  (* An inferred type, rendered through the shared pretty-printer so it shares
     the message's theme and width. Quoted when the theme is uncoloured, to match
     the other emphasized atoms. *)
  let typ ty =
    Message.raw (fun sp ->
        let quote =
          Colors.escape_sequence sp.Styled_printer.theme Colors.Type = ""
        in
        if quote then Printer.string sp.Styled_printer.printer "'";
        (* Render the whole type in the [Type] colour as one unit, rather than
           syntax-highlighting its innards (parens, [&], keywords) in separate
           role colours — a type in a message reads as a single concept. *)
        Styled_printer.with_style sp Colors.Type (fun () ->
            Infer.output_inferred_type_styled sp ty);
        if quote then Printer.string sp.Styled_printer.printer "'")

  (* All errors share the same envelope: severity [Error], a message, and an
     optional hint. [report] captures that boilerplate so each error below is
     just its message (and, where relevant, a hint). *)
  let report ?hint ?related context ~location message =
    Diagnostic.report context ~location ~severity:Error ?hint ?related ~message
      ()

  (* Warnings share the same envelope as [report] but with severity [Warning],
     so they are printed without aborting the pass. [warning] names the warning
     so its level can be configured (see {!Wax_utils.Warning}).

     In error-recovery mode (type-checking a best-effort AST past syntax errors)
     every warning is at best secondary and usually a cascade: a local is
     "unused" only because its use was dropped at a sync boundary or auto-closed
     away at EOF, a result is "unused" because the following code was skipped,
     and the lints may fire on mangled recovered code. Warnings are advisory, so
     suppress them wholesale here — the user fixes the syntax errors first and the
     warnings surface on a clean re-check. This is the warning-severity analogue
     of the [unbound_name]/[short_stack] cascade guards. *)
  let warn ?warning ?universal ?hint ?edit ?related context ~location message =
    if not (Wax_utils.Diagnostic.in_recovery context) then
      Diagnostic.report context ~location ~severity:Warning ?warning ?universal
        ?hint ?edit ?related ~message ()

  (* A local declared by a [let] but never read. Prefix its name with [_] to
     silence the warning — offered as a quick fix by a zero-width [edit] that
     inserts the [_] at the name's start. *)
  let unused_local context ~location x =
    warn ~warning:Wax_utils.Warning.Unused_local ~universal:true context
      ~location
      ~edit:
        {
          Wax_utils.Diagnostic.edit_location =
            { location with loc_end = location.loc_start };
          new_text = "_";
        }
      (text "The local variable" ++ name x ++ text "is never used.")

  (* A module field (a function or global) declared but never referenced,
     exported, or used as the start function. Prefix its name with [_] to
     silence the warning. *)
  let unused_field context ~location kind x =
    warn ~warning:Wax_utils.Warning.Unused_field ~universal:true context
      ~location
      (text "The" ++ text kind ++ name x ++ text "is never used.")

  (* An imported field never referenced, exported, or used as the start function.
     Prefix its name with [_] to silence the warning. *)
  let unused_import context ~location kind x =
    warn ~warning:Wax_utils.Warning.Unused_import ~universal:true context
      ~location
      (text "The imported" ++ text kind ++ name x ++ text "is never used.")

  (* A [let]-declared (mutable) global that is never assigned, so it could be a
     [const]. An import (whose mutability is part of the linking contract) and an
     exported global (which the host may assign) are exempt, as is a name starting
     with [_]. *)
  let unnecessary_mut context ~location x =
    warn ~warning:Wax_utils.Warning.Unnecessary_mut ~universal:true context
      ~location
      ~hint:(text "Declare it with 'const' instead of 'let'.")
      (text "The global" ++ name x ++ text "is mutable but is never assigned.")

  (* A cast/test whose operand can never have the target type. *)
  let cast_always_fails context ~location ~is_test =
    warn ~warning:Wax_utils.Warning.Cast_always_fails ~universal:true context
      ~location
      (text
         (if is_test then
            "This type test is always false: the value can never have this \
             type."
          else "This cast always traps: the value can never have this type."))

  (* A "Trojan Source" bidirectional control character in a string (an
     export/import name, a string literal, a data segment, a feature or
     conditional string) that can make the source read differently than it
     runs. *)
  let confusable_unicode context ~location u =
    warn ~warning:Wax_utils.Warning.Confusable_unicode ~universal:true context
      ~location
      (text
         (Printf.sprintf
            "This string contains a bidirectional control character (U+%04X) \
             that can make the displayed text read differently than it runs."
            (Uchar.to_int u)))

  (* A cast/test whose operand already has the target type. A redundant cast (not
     a test, whose value cannot be dropped safely) carries an [edit] that removes
     it, so the editor can offer a quick fix. *)
  let redundant_cast ?edit context ~location ~is_test =
    warn ?edit ~warning:Wax_utils.Warning.Redundant_operation ~universal:true
      context ~location
      (text
         (if is_test then
            "This type test is always true: the value already has this type."
          else "This cast is redundant: the value already has this type."))

  (* A block label declared but never branched to. Prefix its name with [_] to
     silence the warning. As a quick fix, offer deleting the whole ['name:]
     prefix: [location] already spans ['name] (the leading quote through the
     name), and a short source scan extends it over the trailing [:] and the
     same-line whitespace up to the keyword. Bails (no edit) if the [:] is not
     found where expected. *)
  let unused_label context ~location x =
    let edit =
      match Wax_utils.Diagnostic.source context with
      | None -> None
      | Some src ->
          let n = String.length src in
          let is_ws c = c = ' ' || c = '\t' in
          let i = ref location.loc_end.Lexing.pos_cnum in
          while !i < n && is_ws src.[!i] do
            incr i
          done;
          if !i < n && src.[!i] = ':' then (
            incr i;
            while !i < n && is_ws src.[!i] do
              incr i
            done;
            Some
              {
                Wax_utils.Diagnostic.edit_location =
                  {
                    location with
                    loc_end = { location.loc_end with pos_cnum = !i };
                  };
                new_text = "";
              })
          else None
    in
    warn ?edit ~warning:Wax_utils.Warning.Unused_label ~universal:true context
      ~location
      (text "The label" ++ name x ++ text "is never used.")

  (* A statement that can never be reached: it follows an unconditional branch,
     [return], or [unreachable]. [related] points at the diverging instruction. *)
  let dead_code context ~location ~related =
    warn ~warning:Wax_utils.Warning.Dead_code ~universal:true context ~location
      ~related
      (text "This code is unreachable.")

  let short_stack context kind ~location ~actual ~expected =
    (* Like [unbound_name], suppress this in error-recovery mode: a stack
       underflow while type-checking a best-effort AST is usually a cascade from
       a value-producing construct dropped at a sync boundary, not a real
       mistake. The reporters ([pop], and [report_missing_hole]/[with_holes]
       for a hole) recover with [Error]/[()], so nothing downstream cascades;
       genuine underflows in intact code still surface on a clean re-check once
       the syntax errors are fixed. *)
    let values =
      match kind with
      | `Input -> "argument(s)"
      | `Output -> "returned value(s)"
      | `Holes -> "value(s)"
    in
    if not (Wax_utils.Diagnostic.in_recovery context) then
      report context ~location
        (text "Expecting " ++ Message.int expected ++ text values
         ++ text "from the stack, but there are"
         ++ Message.int actual
        ^^ text ".")

  let let_in_conditional context ~location =
    report context ~location
      (text
         "A let binding is not allowed inside a conditional annotation; \
          declare the local before the conditional.")

  let non_empty_stack context ~location render =
    report context ~location:(loc_last_char location)
      (text "Some values remain on the stack:" ^^ Message.raw render ^^ text ".")

  (* Report the values still on the stack by pointing a caret at each of them.
     [location] carries the topmost value; [related] the others. *)
  let leftover_values context ~location ~related =
    report context ~location ~related
      (text
         (if related = [] then "This value remains on the stack."
          else "These values remain on the stack."))

  let expected_func_type context ~location =
    report context ~location (text "Expected function type.")

  let inline_function_type_mismatch context ~location =
    report context ~location
      (text "The inline function type does not match the type definition.")

  let expected_struct_type context ~location =
    report context ~location (text "Expected struct type.")

  let expected_array_type context ~location =
    report context ~location (text "Expected array type.")

  let expected_struct context ~location =
    report context ~location (text "Expected struct.")

  let expected_array context ~location =
    report context ~location (text "Expected array.")

  let expected_func context ~location =
    report context ~location (text "Expected function.")

  (* An operation (a call, a field/array access, …) needs its operand's concrete
     type to be compiled, but the operand's type is unknown: it was taken off the
     polymorphic stack of unreachable or branch-terminated code. This is the
     first error for the operand (an already-failed operand reads as the [Error]
     type and stays silent), so it is reported here. *)
  let unknown_operand_type context ~location =
    report context ~location
      (text
         "Cannot determine the type of this expression, which is needed to \
          compile this operation.")

  (* A struct literal omitted its type name in a position where the expected
     type does not pin an exact struct type, so the type cannot be inferred. *)
  let cannot_infer_struct_type context ~location =
    report context ~location
      (text "Cannot infer the struct type here; add an explicit type, as in"
       ++ kw "{T| ..}"
      ^^ text ".")

  let cannot_infer_array_type context ~location =
    report context ~location
      (text "Cannot infer the array type here; add an explicit type, as in"
       ++ kw "[T| ..]"
      ^^ text ".")

  let method_needs_parentheses context ~location meth =
    report context ~location
      (kw meth
       ++ text
            "is an instruction method and must be called with parentheses, as"
       ++ kw (meth ^ "()")
      ^^ text ".")

  let type_mismatch context ~location ~current ty' ty =
    report context ~location
      (text "Argument" ++ Message.int current ++ text "should have type"
       ++ typ ty ++ text "but has type" ++ typ ty'
      ^^ text ".")

  let not_an_expression context ~location n =
    (* Suppress in error-recovery mode, like [short_stack]: an instruction with
       the wrong number of values in expression position is usually a cascade
       from recovery mangling the surrounding code (a dropped operand, or a
       construct auto-closed at EOF). Both callers recover with [Error], so
       nothing downstream cascades; a genuine arity error in intact code still
       surfaces on a clean re-check. *)
    if not (Wax_utils.Diagnostic.in_recovery context) then
      report context ~location
        (text "An expression is expected here. This instruction returns"
        ++ Message.int n ++ text "values.")

  let binop_type_mismatch context ~location ty1 ty2 =
    report context ~location
      (text "This operator cannot be applied to operands of types"
       ++ typ ty1 ++ text "and" ++ typ ty2
      ^^ text ".")

  (* [expected_at] points a secondary caret at whatever imposes [expected] when
     that is elsewhere and would otherwise be guesswork — a [br_table] target
     label, whose block's result type is what the value must satisfy, and which
     tells apart two reports on the same value from differently-typed targets.
     The validator's [instruction_type_mismatch] labels its own the same way. *)
  let expression_type_mismatch ?expected_at context ~location ~provided
      ~expected =
    report context ~location
      ?related:
        (Option.map
           (fun loc ->
             [
               {
                 Wax_utils.Diagnostic.location = loc;
                 message = text "expected here";
               };
             ])
           expected_at)
      (text "This expression has type"
       ++ typ provided
       ++ text "but is expected to have type"
       ++ typ expected
      ^^ text ".")

  let value_count_mismatch context ~location ~expected ~provided =
    report context ~location
      (text "This instruction provides"
      ++ Message.int provided ++ text "value(s) but" ++ Message.int expected
      ++ text "was/were expected.")

  let operand_count_mismatch context ~location ~expected ~provided =
    report context ~location
      (text "This instruction expects"
      ++ Message.int expected ++ text "operand(s) but" ++ Message.int provided
      ++ text "was/were provided.")

  let invalid_method_receiver context ~location ty =
    report context ~location
      ((text "This operation cannot be applied to a value of type" ++ typ ty)
      ^^ text ".")

  let invalid_management_call context ~location meth =
    report context ~location
      ((text "Invalid arguments in call to" ++ kw meth) ^^ text ".")

  let if_without_else context ~location =
    report context ~location
      (text "This " ++ kw "if"
      ++ text " must produce a value and so requires an "
      ++ kw "else" ++ text " branch.")

  let parameterized_block_expression context ~location =
    report context ~location
      (text "A block, loop or if used as an expression cannot take parameters.")

  let uninitialized_local context ~location x =
    report context ~location
      (text "The local variable" ++ name x ++ text "has not been initialized.")

  let non_nullable_table context ~location =
    report context ~location
      (text "A table with a non-nullable element type must have an initializer.")

  let start_function_signature context ~location =
    report context ~location
      (text "The start function must have no parameters and no results.")

  let multiple_start context ~location ~prev_loc =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "other start function here";
          };
        ]
      (text "A module can have at most one start function.")

  let multiple_module context ~location ~prev_loc =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "other name annotation here";
          };
        ]
      (text "A module can have at most one name annotation.")

  let unknown_annotation context ~location name =
    report context ~location ((text "Unknown annotation" ++ kw name) ^^ text ".")

  let annotation_value_mismatch context ~location name expected =
    report context ~location
      ((text "The" ++ text name ++ text "annotation expects" ++ text expected)
      ^^ text ".")

  let annotation_not_allowed context ~location name =
    report context ~location
      (text "The" ++ text name ++ text "annotation is not allowed here.")

  let guard_not_allowed context ~location name =
    report context ~location
      (text
         "A conditional guard is only allowed on an export or start \
          annotation, not on"
       ++ text name
      ^^ text ".")

  let multiple_import context ~location ~prev_loc =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "other import-name annotation here";
          };
        ]
      (text "An import can have at most one import-name annotation.")

  let final_supertype context ~location x =
    report context ~location
      (text "The type" ++ name x
       ++ text "is final and cannot be extended; declare it "
       ++ kw "open"
      ^^ text ".")

  let invalid_subtype context ~location x =
    report context ~location
      ((text "This type is not a valid subtype of" ++ name x) ^^ text ".")

  let descriptor_outside_rec_group context ~location ~described =
    report context ~location
      (text "The"
      ++ text (if described then "described" else "descriptor")
      ++ text "type must be in the same recursion group.")

  let descriptor_not_reciprocal context ~location ~described =
    report context ~location
      (text
         (if described then
            "This descriptor does not describe the type it is attached to."
          else "The descriptor of this type does not describe it back."))

  let forward_use_of_described context ~location =
    report context ~location
      (text "A described type must be declared before its descriptor.")

  let descriptor_not_struct context ~location ~described =
    report context ~location
      (text "A"
      ++ text (if described then "described" else "descriptor")
      ++ text "type must be a struct type.")

  let type_without_descriptor context ~location =
    report context ~location
      (text "This descriptor instruction requires a type that has a descriptor.")

  let descriptor_allocation_required context ~location =
    report context ~location
      (text
         "A type with a descriptor must be allocated with a descriptor: \
          {descriptor(d) | …}.")

  let feature_disabled context ~location feature =
    report context ~location
      (text "This uses the"
       ++ text (Wax_utils.Feature.name feature)
       ++ text "feature, which is not enabled; pass --feature"
       ++ text (Wax_utils.Feature.name feature)
      ^^ text ".")

  let unknown_feature context ~location name =
    report context ~location
      ((text "Unknown feature" ++ kw name)
      ^^ text ". Known features:"
         ++ text
              (String.concat ", "
                 (List.map Wax_utils.Feature.name Wax_utils.Feature.all))
      ^^ text ".")

  let feature_conflict context ~location feature =
    report context ~location
      (text "This module requires the"
       ++ text (Wax_utils.Feature.name feature)
       ++ text "feature, which is disabled on the command line; drop --feature"
       ++ text (Wax_utils.Feature.name feature ^ "=off")
      ^^ text ".")

  let feature_declaration_in_conditional context ~location =
    report context ~location
      (text "A" ++ kw "#![feature = \"…\"]"
      ++ text
           "declaration states a fact about the whole module and must appear \
            at the top level, not inside a conditional.")

  let module_name_in_conditional context ~location =
    report context ~location
      (text "A" ++ kw "#![module = \"…\"]"
      ++ text
           "name annotation applies to the whole module and must appear at the \
            top level, not inside a conditional.")

  (* A secondary caret at [location] labelled with an inferred value type. Used
     to point at each branch of an [if]/select whose branches are in
     incompatible type hierarchies: there is no common supertype — and, unlike a
     checked position which can name one expected type, no annotation that would
     reconcile them — so we just show what each branch produces. *)
  let typed_branch_label location ty =
    { Wax_utils.Diagnostic.location; message = typ ty }

  let select_type_mismatch context ~location ~loc1 ~loc2 ty1 ty2 =
    report context ~location
      ~related:[ typed_branch_label loc1 ty1; typed_branch_label loc2 ty2 ]
      (text
         "The two branches of this select have no common supertype, so its \
          result type cannot be inferred.")

  (* The exit values of a block-like construct (an [if]'s two branches, or a
     [do]/[loop]/[try]'s fall-through and/or values branched to its label) do not
     join to a common supertype. A caret marks each offending value. *)
  let block_exit_type_mismatch context ~location ~loc1 ~loc2 ty1 ty2 =
    report context ~location
      ~related:[ typed_branch_label loc1 ty1; typed_branch_label loc2 ty2 ]
      (text
         "The values reaching this block's exit have no common supertype, so \
          its result type cannot be inferred.")

  (* A value delivered by [br_if] stays on the stack (the fall-through) typed as
     the block's result, so its type must equal the inferred result exactly, not
     merely be a subtype. Here it is a strict subtype and there is no annotation
     to pin the result, so the block cannot be given a result type consistent with
     both. *)
  let br_if_result_mismatch context ~location ~loc ~result ty =
    report context ~location
      ~related:[ typed_branch_label loc ty; typed_branch_label location result ]
      (text "This " ++ kw "br_if"
      ++ text
           " value stays on the stack as the block's result, so its type must \
            match the inferred result exactly; add a result annotation to the \
            block.")

  (* Two targets of the same [br_table] take different numbers of values;
     [first] is the reference target (the first bound one). *)
  let branch_arity_mismatch context ~location ~first_loc first ~expected
      ~provided =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = first_loc;
            message = text "other branch target here";
          };
        ]
      (text "This branch target expects"
      ++ Message.int provided
      ++ text "value(s), while branch target"
      ++ name first ++ text "expects" ++ Message.int expected
      ++ text "value(s).")

  let name_already_bound context ~location ~prev_loc kind x =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "previously bound here";
          };
        ]
      (text "A" ++ text kind ++ text "named" ++ name x
     ++ text "is already bound.")

  let did_you_mean = function
    | [] -> None
    | suggestions ->
        Some
          (text "Did you mean"
           ++ Message.enumerate ~conj:"or" (List.map Message.ident suggestions)
          ^^ text "?")

  let unbound_name context ~location ?(suggestions = []) kind x =
    (* In error-recovery mode (type-checking a best-effort AST past syntax
       errors) a name is often unbound only because the construct that would
       bind it was dropped at a sync boundary — our recovery drops spans rather
       than leaving a placeholder node, so the binding is simply absent. Such
       "not bound" reports are cascades from the syntax error, so suppress them;
       the caller has already reported the syntax errors, and real type errors
       in the intact regions still surface. The value still recovers as [Error]
       at the use site, so nothing downstream cascades either. *)
    if not (Wax_utils.Diagnostic.in_recovery context) then
      report ?hint:(did_you_mean suggestions) context ~location
        (text "The" ++ text kind ++ name x ++ text "is not bound.")

  let unknown_intrinsic context ~location ns name =
    report context ~location
      (text "There is no" ++ kw (ns ^ "::" ^ name) ++ text "intrinsic.")

  let intrinsic_not_called context ~location ns name =
    report context ~location
      (text "The qualified name"
      ++ kw (ns ^ "::" ^ name)
      ++ text "can only be used as a function call.")

  (* Compilation-hints proposal, mirroring [Validation]'s checks on the same hint:
     a call-target list only means something for a call whose callee is not already
     known, and the listed frequencies must leave room for the unlisted ones. *)
  let call_targets_direct_call context ~location =
    report context ~location
      (text
         "A call-target hint may only prefix an indirect call. This callee is \
          a function, so the call is direct and its target is already known.")

  (* Compilation-hints proposal: an optimization priority is stated only alongside
     a compilation one, so either spelling of it needs [#[priority]] too. *)
  let priority_required context ~location which =
    report context ~location
      (text "The"
       ++ kw ("#[" ^ which ^ "]")
       ++ text "attribute needs a" ++ kw "#[priority = n]"
      ^^ text ".")

  let conflicting_optimization context ~location ~prev_loc =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "the other one here";
          };
        ]
      (text "A function states at most one optimization priority:"
       ++ kw "#[optimization = n]" ++ text "or" ++ kw "#[run_once]"
      ^^ text ", not both.")

  let call_targets_over_100 context ~location ~total =
    report context ~location
      (((text "The call-target frequencies add up to" ++ Message.int total)
       ^^ text "%, more than 100%.")
      ++ text
           "A shortfall is how the hint says other, unlisted targets take the \
            remainder.")

  let before_hole context ~location =
    report context ~location
      ((text "This expression occurs before a hole " ++ kw "_") ^^ text ".")

  let hole_in_control_operand context ~location ~construct ~role =
    report context ~location
      (text "A hole" ++ kw "_" ++ text "cannot be used as a" ++ kw construct
       ++ text role
      ^^ text ".")

  let duplicated_field context ~location ~prev_loc x =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "other field here";
          };
        ]
      ((text "Several fields have the same name" ++ name x) ^^ text ".")

  let splice_without_supertype context ~location =
    report context ~location
      (kw ".."
      ++ text " requires a supertype to inherit fields from (write "
      ++ kw "type t: super = { .., ... }"
      ++ text ").")

  let splice_non_struct context ~location x =
    report context ~location
      (kw ".."
      ++ text " can only inherit fields from a struct supertype;"
      ++ name x ++ text "is not a struct.")

  let duplicated_parameter context ~location ~prev_loc x =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "other parameter here";
          };
        ]
      ((text "Several parameters have the same name" ++ name x) ^^ text ".")

  let constant_expression_required context ~location =
    report context ~location
      (text "Only constant expressions are allowed here.")

  let integer_literal_required context ~location =
    report context ~location (text "Only integer literals are allowed here.")

  let number_literal_required context ~location =
    report context ~location (text "Only number literals are allowed here.")

  let data_run_bad_element context ~location typename =
    report context ~location
      (text "This value is out of range for the data run's element type"
       ++ kw typename
      ^^ text ".")

  let data_v128_arity context ~location count =
    report context ~location
      (text "This v128 lane group must have"
      ++ Message.int count ++ text "lanes.")

  let memory_offset_too_large context ~location max_offset =
    report context ~location
      (text "The memory offset should be less than"
       ++ num (Printf.sprintf "0x%Lx" (Wax_utils.Uint64.to_int64 max_offset))
      ^^ text ".")

  let memory_align_too_large context ~location natural =
    report context ~location
      (text "The memory alignment is larger than the natural alignment"
       ++ Message.int natural
      ^^ text ".")

  let memory_immediate_too_large context ~location =
    report context ~location
      (text
         "This memory offset or alignment must fit a 64-bit unsigned integer.")

  let bad_memory_align context ~location =
    report context ~location
      (text "The memory alignment should be a power of two.")

  let atomic_alignment context ~location natural =
    report context ~location
      (text "The alignment of an atomic access must be its natural alignment"
       ++ Message.int natural
      ^^ text ".")

  let atomic_signed_load context ~location ~cast ~extend =
    report context ~location
      (text "An atomic load zero-extends; use"
      ++ (kw cast ^^ text ",")
      ++ text "then" ++ kw extend
      ++ text "if you need the sign.")

  let invalid_lane_index context ~location max_lane =
    report context ~location
      ((text "The lane index should be less than" ++ Message.int max_lane)
      ^^ text ".")

  let lane_value_out_of_range context ~location bits =
    report context ~location
      (text "The lane value does not fit in" ++ Message.int bits ++ text "bits.")

  let labelled_argument_not_allowed context ~location =
    report context ~location
      (text "Labelled arguments are only allowed for the"
      ++ (kw "offset" ^^ text ",")
      ++ kw "align" ++ text "and" ++ kw "lane"
      ++ text "immediates of a memory access.")

  let become_on_stack_switching context ~location =
    report context ~location
      (kw "become" ++ text "cannot apply to a stack-switching operation.")

  let unknown_argument_label context ~location ~suggestions x =
    report ?hint:(did_you_mean suggestions) context ~location
      ((text "Unknown argument label" ++ name x) ^^ text ".")

  let duplicate_argument_label context ~location ~prev_loc x =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "previously given here";
          };
        ]
      (text "The argument label" ++ name x ++ text "is given several times.")

  let positional_argument_after_label context ~location =
    report context ~location
      (text "A positional argument cannot follow a labelled argument.")

  (* The pre-labelled-arguments syntax passed the [align]/[offset] (and SIMD
     [lane]) immediates positionally; give old code a targeted migration
     message rather than a generic arity error. *)
  let positional_memory_immediate context ~location ~example =
    report context ~location
      (text "The static immediates of a memory access must be labelled, e.g."
       ++ kw example
      ^^ text ".")

  let missing_lane_immediate context ~location =
    report context ~location
      (text "This memory access needs a"
       ++ kw "lane:" ++ text "immediate (e.g." ++ kw "lane: 0"
      ^^ text ").")

  let limit_too_large context ~location kind max =
    report context ~location
      (text "The" ++ text kind
       ++ text "size is too large. It should be less than"
       ++ num (Printf.sprintf "0x%Lx" (Wax_utils.Uint64.to_int64 max))
      ^^ text ".")

  let limit_mismatch context ~location kind =
    report context ~location
      (text "The" ++ text kind
      ++ text "maximum size should be larger than the minimal size.")

  let invalid_page_size context ~location =
    report context ~location (text "The custom page size must be 1 or 65536.")

  let shared_memory_without_max context ~location =
    report context ~location (text "A shared memory must have a maximum size.")

  let duplicated_export context ~location ~prev_loc name =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "previously exported here";
          };
        ]
      ((text "There is already an export of name" ++ kw name) ^^ text ".")

  (* A cast to a continuation type that is not a provable no-op: continuations
     carry no RTT, so no cast can ever narrow one — point at the value's
     introduction, not the cast site. *)
  let cont_cast_not_ascription context ~location =
    report context ~location
      ~hint:
        (text
           "Give the value a declared continuation type where it is introduced \
            (a parameter, local or block-result annotation).")
      (text
         "A cast to a continuation type is a compile-time ascription: the \
          operand's type must already be a subtype of the target, as there is \
          no runtime continuation cast.")

  let invalid_cast_type context ~location =
    report context ~location
      (text "Continuation types cannot be used in a cast instruction.")

  let stack_switching_type_mismatch context ~location ~descr =
    report context ~location
      ((text "Type mismatch in this stack switching instruction:" ++ text descr)
      ^^ text ".")

  let reserved_type_name context ~location x =
    report context ~location (name x ++ text "is a reserved built-in type name.")

  let expected_cont_type context ~location =
    report context ~location
      (text
         "This expression should be a reference to a declared continuation \
          type.")

  (* Mirrors the call_ref rule for an abstract function reference at a call:
     the type immediate comes from the receiver's static type. Unlike a
     function reference, an abstract [&cont] cannot be cast to a declared
     continuation type (the proposal defines no such cast), so the fix is to
     give the value its precise type at its source. *)
  let abstract_cont_receiver context ~location =
    report context ~location
      (text
         "The continuation type cannot be resolved from this expression. Give \
          the value a declared continuation type where it is introduced (a \
          parameter, local or block-result annotation): a continuation \
          reference cannot be narrowed by a cast.")

  let on_clause_context context ~location =
    report context ~location
      (text "An" ++ kw "on"
      ++ text "handler clause is only allowed on a"
      ++ (kw "resume" ^^ text ",")
      ++ kw "resume_throw" ++ text "or" ++ kw "resume_throw_ref" ++ text "call."
      )

  let switch_needs_tag context ~location =
    report context ~location
      (text "A" ++ kw "switch"
      ++ text "names its enabling tag as a labelled immediate, e.g."
      ++ (kw "c.switch(x, tag: t)" ^^ text "."))

  let resume_throw_needs_tag context ~location =
    report context ~location
      (kw "resume_throw"
      ++ text "raises a tag applied to its payload, e.g."
      ++ (kw "c.resume_throw(exc(x))" ^^ text "."))

  let constant_global_required context ~location =
    report context ~location
      (text "Only accessing a constant global is allowed here.")

  let immutable context ~location what =
    report context ~location
      (text "This" ++ text what ++ text "is immutable and cannot be assigned.")

  let not_assignable context ~location x =
    report context ~location (name x ++ text "cannot be assigned.")

  let field_count_mismatch context ~location ~expected ~provided =
    report context ~location
      (text "This structure provides"
      ++ Message.int provided ++ text "field(s) but" ++ Message.int expected
      ++ text "was/were expected.")

  let missing_field context ~location x =
    report context ~location
      ((text "There is no field named" ++ name x) ^^ text ".")

  let invalid_cast context ~location ty' =
    report context ~location
      (text "This value of type" ++ typ ty'
      ++ text "cannot be cast to the target type.")

  let tag_with_results context ~location =
    report context ~location
      (text "An exception tag cannot have result values.")

  let catch_target_mismatch context ~location provided expected =
    report context ~location
      (text "Catching this exception provides a value of type"
       ++ typ provided
       ++ text "but the handler's branch target expects"
       ++ typ expected
      ^^ text ".")

  let not_defaultable context ~location =
    report context ~location
      (text "This type has no default value for all its fields.")

  let incompatible_array_elements context ~location =
    report context ~location
      (text "The source and destination array element types are incompatible.")

  let incompatible_element_type context ~location provided expected =
    report context ~location
      (text "The element type" ++ typ provided
       ++ text "is not compatible with the expected element type"
       ++ typ expected
      ^^ text ".")

  let invalid_string_element_type context ~location =
    report context ~location
      (text "A string literal can only build an [i8] or [i16] array.")

  let string_not_unicode context ~location =
    report context ~location
      (text "A string building an [i16] array must be a valid Unicode string.")

  let expected_ref context ~location =
    report context ~location (text "Expected reference.")

  let dispatch_duplicate_arm context ~location ~prev_loc x =
    report context ~location
      ~related:
        [
          {
            Wax_utils.Diagnostic.location = prev_loc;
            message = text "other arm here";
          };
        ]
      ((text "This dispatch has several cases named" ++ name x) ^^ text ".")

  (* The Wasm-to-Wax conversion recorded the type a node's value must have (see
     [Ast.instr]'s [expected]) and this run resolved another one, so the Wax about
     to be printed would recompile at a different opcode width — a silent
     miscompile. [pinnable] says whether a grounding pin could have corrected it
     (the value is a flexible literal tree), which is exactly what the conversion's
     default [`Repair] mode does instead of reporting; see {!reconcile_widths}:
     - pinnable: this report IS the [--debug width-check] mode of a repair, so it
       is purely a fault of the tool — the pin [From_wasm] should have placed.
     - not pinnable: the value's type is fixed by its context, so no cast can
       correct it (one would convert the value) — either the input is invalid, or
       the conversion is wrong. Reported in BOTH modes.
     The expression is spelled out because a synthesized dead-code node has no real
     source span to point at. Both wordings share the leading phrase, which the
     fuzz harness greps for (oracle 5c, drop-width.sh). *)
  let width_invariant_violated context ~location ~inferred ~required ~pinnable
      expr =
    report context ~location
      ~hint:
        (text
           (if pinnable then
              "This is an internal invariant of the WebAssembly-to-Wax \
               conversion, not a problem with the input; without '--debug \
               width-check' the conversion repairs it by pinning the \
               expression."
            else
              "Either this WebAssembly is invalid — a binary input is trusted, \
               never validated, so check it with 'wax check' — or the \
               WebAssembly-to-Wax conversion is wrong. A cast here would \
               convert the value rather than pin it, so the conversion does \
               not repair it."))
      (text "Decompiler width invariant violated for"
       ++ kw expr
       ++ (match inferred with
         | Some inferred ->
             text "recompiling it would infer"
             ++ kw (Infer.Output.valtype_string inferred)
         | None -> text "recompiling it would leave its type unresolved")
       ++ text "but the WebAssembly it came from requires"
       ++ kw (Infer.Output.valtype_string required)
      ^^ text
           (if pinnable then "."
            else
              ": its type is fixed by context, not defaulted, so no pin can \
               correct it."))
end

(*** Symbol tables and namespaces ***)

module Namespace = struct
  include Typing_env.Namespace

  let make ?(links = None) cond = { cond; tbl = Hashtbl.create 16; links }

  let entries ns (x : Ast.ident) =
    try Hashtbl.find ns.tbl x.desc with Not_found -> []

  (* A name conflicts with an earlier declaration only if their assumptions can
     both hold; declarations in mutually-exclusive branches do not conflict. *)
  let conflict ns x =
    let c = !(ns.cond) in
    List.find_opt
      (fun (_, _, c') -> Cond.is_satisfiable (Cond.and_ c c'))
      (entries ns x)

  let register d ns kind x =
    (match conflict ns x with
    | Some (kind', prev_loc, _) ->
        Error.name_already_bound d ~location:x.info ~prev_loc kind' x
    | None -> ());
    Hashtbl.replace ns.tbl x.desc ((kind, x.info, !(ns.cond)) :: entries ns x)

  let exists d ns x =
    match conflict ns x with
    | Some (kind', prev_loc, _) ->
        Error.name_already_bound d ~location:x.info ~prev_loc kind' x;
        true
    | None -> false
end

module Tbl = struct
  include Typing_env.Tbl

  let make ?(hover = fun _ -> None) ~current namespace kind =
    {
      kind;
      namespace;
      tbl = Hashtbl.create 16;
      used = Hashtbl.create 16;
      current;
      hover;
    }

  (* Every context that referenced [name]: [None] for a module-level one (a
     root), [Some f] for the body of function [f]. One entry per reference. The
     unused-field lint asks this rather than a plain "is it referenced", so a
     reference made from dead code can be discounted. *)
  let referrers env name = Hashtbl.find_all env.used name

  (* [f referrer name] for every reference recorded in this table. *)
  let iter_references env f =
    Hashtbl.iter (fun name referrer -> f referrer name) env.used

  (* Record a reference to [name] from [referrer], for a use that names no
     declaration syntactically (see [canonical_type_references]). Same one
     entry per (name, origin) pair as [resolve]. *)
  let mark_reference env name referrer =
    if
      referrer <> Ignored
      && not (List.mem referrer (Hashtbl.find_all env.used name))
    then Hashtbl.add env.used name referrer

  (* [f name value] for every declaration in this table. *)
  let iter_entries env f =
    Hashtbl.iter
      (fun name entries -> List.iter (fun (_, v) -> f name v) entries)
      env.tbl

  let cur env = !(env.namespace.cond)

  let entries env (x : Ast.ident) =
    try Hashtbl.find env.tbl x.desc with Not_found -> []

  let add d env x v =
    Namespace.register d env.namespace env.kind x;
    Hashtbl.replace env.tbl x.desc ((cur env, v) :: entries env x)

  let exists d env x = Namespace.exists d env.namespace x

  (* Replace the most recently added entry (added by [add] under the current
     assumption); used by [add_type] to fix up rectype indices in place. *)
  let override env x v =
    match entries env x with
    | _ :: tl -> Hashtbl.replace env.tbl x.desc ((cur env, v) :: tl)
    | [] -> Hashtbl.replace env.tbl x.desc [ (cur env, v) ]

  (* Pick the declaration whose assumption is entailed by the current one,
     falling back to one merely compatible with it, then to the most recent.
     A successful lookup marks the name referenced (for the unused-field lint);
     [resolve] is only ever called to look up a reference, never for a
     declaration (which goes through [add]). *)
  (* Pick the declaration whose assumption best matches the current one, without
     recording a use. Shared by [resolve] (which then marks the name used) and
     [find_no_mark] (which does not). *)
  let select env x =
    match entries env x with
    | [] -> None
    | [ (_, v) ] -> Some v
    | l -> (
        let c = cur env in
        let pick p = Option.map snd (List.find_opt (fun (c', _) -> p c') l) in
        match pick (fun c' -> Cond.logical_implies c c') with
        | Some _ as r -> r
        | None -> (
            match pick (fun c' -> Cond.is_satisfiable (Cond.and_ c c')) with
            | Some _ as r -> r
            | None -> ( match l with (_, v) :: _ -> Some v | [] -> None)))

  let resolve env x =
    let r = select env x in
    (match r with
    | Some v ->
        (* One entry per (name, origin) pair, not per reference: a helper called
           a thousand times from one function is one edge. Keeps [used] bounded by
           the reference graph rather than by the instruction count. *)
        let referrer = !(env.current) in
        if
          referrer <> Ignored
          && not (List.mem referrer (Hashtbl.find_all env.used x.desc))
        then Hashtbl.add env.used x.desc referrer;
        (* Link this use to every definition of the name (several only across
           conditional branches); [resolve] handles only references, so [x.info]
           is a use site. The resolved value's summary rides along for hover. *)
        record_reference ~hover:(env.hover v) env.namespace.links x.info
          (List.map
             (fun (_, loc, _) -> loc)
             (Namespace.entries env.namespace x))
    | None -> ());
    r

  let find d env x =
    match resolve env x with
    | Some _ as r -> r
    | None ->
        let suggestions =
          Wax_utils.Spell_check.f
            (fun f -> Hashtbl.iter (fun k _ -> f k) env.tbl)
            x.desc
        in
        Error.unbound_name d ~location:x.info ~suggestions env.kind x;
        None

  let find_opt env x = resolve env x

  (* Look up a name's binding without counting it as a reference. Used by the
     typer's own internal lookups (e.g. a function resolving its own declared
     type while it is being checked) that must not mark the name used, so the
     unused-field lint still fires on a defined-but-unreferenced function. *)
  let find_no_mark env x = select env x

  let iter env f =
    Hashtbl.iter (fun k l -> List.iter (fun (_, v) -> f k v) l) env.tbl

  (* Drop the most recently added entry (the temporary [add_type] placeholder),
     keeping any declaration of the same name from another branch. *)
  let remove env x =
    match entries env x with
    | _ :: (_ :: _ as tl) -> Hashtbl.replace env.tbl x.desc tl
    | _ -> Hashtbl.remove env.tbl x.desc
end

type types = Typing_env.types

let get_type_definition d types nm = Option.map snd (Tbl.find d types nm)

(* The canonical index of an already-defined type; a [Rec] would mean a group
   still under construction, which the type-definition builders never look up. *)
let def_id : Wax_wasm.Types.ref_index -> Wax_wasm.Types.Id.t = function
  | Def id -> id
  | Rec _ -> assert false

(* How a source reference appears inside a rec group being registered. *)
let resolve_type_ref d (ctx : type_context) name =
  let+@ res = Tbl.find d ctx.types name in
  fst res

(* The canonical index of an already-defined referenced type. *)
let resolve_type_name d ctx name =
  let+@ r = resolve_type_ref d ctx name in
  def_id r

(* Record that [feature] is used and, if it is disabled, report it at
   [location]. Typing continues either way (error recovery). *)
let require_feature d (ctx : type_context) ~location feature =
  Wax_utils.Feature.mark_used ctx.features feature;
  if not (Wax_utils.Feature.is_enabled ctx.features feature) then
    Error.feature_disabled d ~location feature

let heaptype d ctx (h : heaptype) : Internal.heaptype option =
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
      let+@ ty = resolve_type_name d ctx idx in
      (Type ty : Internal.heaptype)
  | Exact idx ->
      require_feature d ctx ~location:idx.info
        Wax_utils.Feature.Custom_descriptors;
      let+@ ty = resolve_type_name d ctx idx in
      (Exact ty : Internal.heaptype)

let reftype d ctx { nullable; typ } =
  let+@ typ = heaptype d ctx typ in
  { Internal.nullable; typ }

let valtype d ctx ty : Internal.valtype option =
  match ty with
  | I32 -> Some I32
  | I64 -> Some I64
  | F32 -> Some F32
  | F64 -> Some F64
  | V128 -> Some V128
  | Ref r ->
      let+@ ty = reftype d ctx r in
      (Ref ty : Internal.valtype)

(* Like [Array.map] into an option, returning [None] as soon as [f] returns
   [None] on any element (so [let*!] propagates a single failure). *)
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

(* Report any parameter name used more than once in a signature. *)
let check_unique_param_names d params =
  ignore
    (Array.fold_left
       (fun s p ->
         match param_name p with
         | None -> s
         | Some name ->
             (match List.assoc_opt name.desc s with
             | Some prev_loc ->
                 Error.duplicated_parameter d ~location:name.info ~prev_loc name
             | None -> ());
             (name.desc, name.info) :: s)
       [] params
      : (string * location) list)

let muttype f d ctx { mut; typ } =
  let+@ typ = f d ctx typ in
  { mut; typ }

(* Type-definition builders producing the normalized form ({!Wax_wasm.Types.
   Normalized}) that {!Wax_wasm.Types.add_rectype} takes: an in-group reference
   is [Rec pos], anything else [Def id]. Separate from the [Internal]-producing
   builders above, which serve the checker where every reference is defined. *)
let n_heaptype d ctx (h : heaptype) : Nz.heaptype option =
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
      let+@ r = resolve_type_ref d ctx idx in
      (Type r : Nz.heaptype)
  | Exact idx ->
      require_feature d ctx ~location:idx.info
        Wax_utils.Feature.Custom_descriptors;
      let+@ r = resolve_type_ref d ctx idx in
      (Exact r : Nz.heaptype)

let n_reftype d ctx { nullable; typ } : Nz.reftype option =
  let+@ typ = n_heaptype d ctx typ in
  { Nz.nullable; typ }

let n_valtype d ctx ty : Nz.valtype option =
  match ty with
  | I32 -> Some I32
  | I64 -> Some I64
  | F32 -> Some F32
  | F64 -> Some F64
  | V128 -> Some V128
  | Ref r ->
      let+@ ty = n_reftype d ctx r in
      (Ref ty : Nz.valtype)

let n_functype d ctx { params; results } : Nz.functype option =
  check_unique_param_names d params;
  let*@ params =
    array_map_opt (fun p -> n_valtype d ctx (param_type p)) params
  in
  let+@ results = array_map_opt (fun ty -> n_valtype d ctx ty) results in
  { Nz.params; results }

let n_storagetype d ctx ty : Nz.storagetype option =
  match ty with
  | Value ty ->
      let+@ ty = n_valtype d ctx ty in
      (Value ty : Nz.storagetype)
  | Packed ty -> Some (Packed ty)

let n_fieldtype d ctx ty : Nz.fieldtype option = muttype n_storagetype d ctx ty

let comptype d (ctx : type_context) (ty : comptype) : Nz.comptype option =
  match ty with
  | Func ty ->
      let+@ ty = n_functype d ctx ty in
      (Func ty : Nz.comptype)
  | Struct fields ->
      let _ : (string * location) list =
        Array.fold_left
          (fun s (field : (ident * fieldtype, location) Ast.annotated) ->
            let name = field_name field in
            (match List.assoc_opt name.desc s with
            | Some prev_loc ->
                Error.duplicated_field d ~location:name.info ~prev_loc name
            | None -> ());
            (name.desc, name.info) :: s)
          [] fields
      in
      let+@ fields =
        array_map_opt (fun field -> n_fieldtype d ctx (field_type field)) fields
      in
      (Struct fields : Nz.comptype)
  | Array field ->
      let+@ field = n_fieldtype d ctx field in
      (Array field : Nz.comptype)
  | Cont idx ->
      let+@ r = resolve_type_ref d ctx idx in
      (Cont r : Nz.comptype)

(* A reference is to an already-defined type when it is a [Def], or a [Rec]
   member strictly before [current] in the group. *)
let defined_before current : Wax_wasm.Types.ref_index -> bool = function
  | Def _ -> true
  | Rec pos -> pos < current

let subtype d (ctx : type_context) current
    { typ; supertype; final; descriptor; describes } : Nz.subtype option =
  let*@ typ = comptype d ctx typ in
  let*@ supertype =
    match supertype with
    | None -> Some None
    | Some sup ->
        let+@ r = resolve_type_ref d ctx sup in
        (* A supertype must be declared before; a self-reference or a forward
           reference within the same rec group is treated as unbound, matching
           the validator (rather than crashing). Drop the offending supertype so
           the subtype chain stays acyclic and later subtype queries terminate. *)
        if defined_before current r then Some r
        else (
          Error.unbound_name d ~location:sup.info "type" sup;
          None)
  in
  (* [descriptor]/[describes] may refer mutually within the rec group, so no
     declared-before restriction applies. *)
  let resolve_opt = function
    | None -> Some None
    | Some (idx : Ast.ident) ->
        require_feature d ctx ~location:idx.info
          Wax_utils.Feature.Custom_descriptors;
        let+@ r = resolve_type_ref d ctx idx in
        Some r
  in
  let*@ descriptor = resolve_opt descriptor in
  let+@ describes = resolve_opt describes in
  { Nz.typ; supertype; final; descriptor; describes }

(* Each member's components (its supertype, field and element types, a descriptor
   clause) are references made *by that member*, so they only keep their targets
   alive if the member itself is: a rec group nothing else names is dead as a
   whole, cycle and all. *)
let rectype d (ctx : type_context) ty =
  let outer = !(ctx.types.current) in
  let r =
    array_mapi_opt
      (fun i elt ->
        if outer <> Ignored then
          ctx.types.current := From_type (member_name elt).desc;
        subtype d ctx i (member_type elt))
      ty
  in
  ctx.types.current := outer;
  r

(* Replace a leading [..] splice sentinel in each struct of the rec group with
   the supertype's fields. Called after the group's names are temporarily
   registered (so an in-group supertype resolves), and expands members in source
   order so an earlier member is already expanded when a later one inherits from
   it. Returns a fresh array; the parsed module AST keeps its sentinel (for
   [format] / decompilation round-trip), while the internal type and [ctx.types]
   get the expanded fields. *)
let expand_splices d (ctx : type_context) ty =
  let expanded = Array.copy ty in
  Array.iteri
    (fun i elt ->
      let name = member_name elt and sub = member_type elt in
      match sub.typ with
      | Struct fields
        when Array.length fields > 0 && Ast.is_splice_field fields.(0) ->
          let delta = Array.sub fields 1 (Array.length fields - 1) in
          let parent_fields =
            match sub.supertype with
            | None ->
                Error.splice_without_supertype d ~location:fields.(0).info;
                None
            | Some sup -> (
                match Tbl.find_opt ctx.types sup with
                | Some (idx, parent) -> (
                    (* An in-group member is a [Rec]; use its already-expanded
                       form. A self/forward reference ([j >= i]) is reported as
                       unbound by [subtype], so skip. *)
                    let parent =
                      match idx with
                      | Wax_wasm.Types.Rec j ->
                          if j < i then Some (member_type expanded.(j))
                          else None
                      | Def _ -> Some parent
                    in
                    match parent with
                    | Some { typ = Struct pf; _ } -> Some pf
                    | Some _ ->
                        Error.splice_non_struct d ~location:sup.info sup;
                        None
                    | None -> None)
                | None -> None (* unbound supertype: reported by [subtype] *))
          in
          let fields' =
            match parent_fields with
            | Some pf -> Array.append pf delta
            | None -> delta
          in
          expanded.(i) <-
            { elt with desc = (name, { sub with typ = Struct fields' }) }
      | _ -> ())
    ty;
  expanded

(* The built-in type names a [type] declaration (or a [rec] member) may not
   take: [T::] extends to declared types, making the [::] left-hand side one
   namespace shared by the intrinsic namespaces and user types, so the
   built-ins must stay unambiguous ([&i64] is the value type, [atomic::fence]
   the intrinsic, …). The valtypes, the abstract heap types (the parser's
   [absheaptype_tbl] set), and the [atomic] intrinsic namespace ([v128]/[i64]
   are already valtypes; [cont] is a keyword). [From_wasm] renames a [$type]
   that collides (see [Namespace.reserved_heap_types]). *)
let reserved_type_names =
  [
    "i32";
    "i64";
    "f32";
    "f64";
    "v128" (* the value types *);
    "any";
    "array";
    "eq";
    "exn";
    "extern";
    "func";
    "i31";
    "nocont";
    "noexn";
    "noextern";
    "nofunc";
    "none";
    "struct" (* the abstract heap types *);
    "atomic" (* the intrinsic namespace *);
  ]

let add_type d (ctx : type_context) ty =
  Array.iteri
    (fun i elt ->
      let name = member_name elt and typ = member_type elt in
      if List.mem name.desc reserved_type_names then
        Error.reserved_type_name d ~location:name.info name;
      Tbl.add d ctx.types name (Wax_wasm.Types.Rec i, typ))
    ty;
  (* Expand [..] splices before building the internal type and before the final
     [ctx.types] override below, so both see the supertype's fields. *)
  let ty = expand_splices d ctx ty in
  match rectype d ctx ty with
  | None ->
      (* Remove temporary names on failure *)
      Array.iter (fun elt -> Tbl.remove ctx.types (member_name elt)) ty;
      None
  | Some ity ->
      (* Well-formedness of [descriptor]/[describes] clauses, which must link two
         struct types within the same recursion group. In [ity] a [Rec] reference
         names a member of this group; a [Def] denotes an already-defined type
         outside it. *)
      Array.iteri
        (fun i (sub : Nz.subtype) ->
          let location = ty.(i).info in
          (match sub.descriptor with
          | None -> ()
          | Some (Def _) ->
              Error.descriptor_outside_rec_group d ~location ~described:false
          | Some (Rec pos) -> (
              match ity.(pos).describes with
              | Some (Rec o) when o = i -> ()
              | _ ->
                  Error.descriptor_not_reciprocal d ~location ~described:false));
          (match sub.describes with
          | None -> ()
          | Some (Def _) ->
              Error.descriptor_outside_rec_group d ~location ~described:true
          | Some (Rec pos) -> (
              if pos >= i then Error.forward_use_of_described d ~location;
              match ity.(pos).descriptor with
              | Some (Rec dd) when dd = i -> ()
              | _ -> Error.descriptor_not_reciprocal d ~location ~described:true
              ));
          if
            (sub.descriptor <> None || sub.describes <> None)
            && match sub.typ with Struct _ -> false | _ -> true
          then
            Error.descriptor_not_struct d ~location
              ~described:(sub.describes <> None))
        ity;
      let i' = Wax_wasm.Types.add_rectype ctx.internal_types ity in
      (* The type space grew, so any memoised subtyping info is stale. *)
      ctx.subtyping_info_cache <- None;
      Array.iteri
        (fun i elt ->
          let name = member_name elt and typ = member_type elt in
          (* Normalization drops a supertype the spec forbids — a forward or self
             reference, which is not "declared before" (see [subtype]/
             [defined_before]). Drop it from the source type stored here too, so
             the source-level walkers ([heap_lub] via [immediate_supertype]) never
             follow the cyclic edge and loop; the error was already reported. *)
          let typ =
            match ity.(i).supertype with
            | None -> { typ with supertype = None }
            | Some _ -> typ
          in
          Tbl.override ctx.types name
            (Wax_wasm.Types.Def (Wax_wasm.Types.Id.add i' i), typ))
        ty;
      Some i'

(*** The module context ***)

(* The subtyping info for the current type space, memoised on [type_context] and
   rebuilt on demand after [add_type] invalidates it. Always current, so a
   subtyping query on a type minted while type-checking (an inline [&fn(..)] cast
   target) sees it rather than indexing past a stale snapshot. *)
let subtyping_info ctx =
  match ctx.type_context.subtyping_info_cache with
  | Some info -> info
  | None ->
      let info =
        Wax_wasm.Types.subtyping_info ctx.type_context.internal_types
      in
      ctx.type_context.subtyping_info_cache <- Some info;
      info

(*** Name resolution and subtyping ***)

(* Type [f] under the assumption of a conditional branch ([positive] for
   [@then], negative for [@else]), restoring the previous assumption after. *)
let with_cond_ref cond_ref cond_env diagnostics ~location cond positive f =
  let saved = !cond_ref in
  let c = Cond.of_cond cond_env diagnostics ~location cond in
  cond_ref := Cond.and_ saved (if positive then c else Cond.not_ c);
  Fun.protect ~finally:(fun () -> cond_ref := saved) f

let with_cond ctx ~location cond positive f =
  with_cond_ref ctx.cond ctx.cond_env ctx.diagnostics ~location cond positive f

(* The [lookup_*_type] family resolves a type NAME to its composite type of the
   expected kind. An unbound name is REPORTED (at the reference, with
   spell-check suggestions — [Tbl.find]); silently returning [None] here let a
   construction literal naming an unbound type be accepted and lowered to
   [unreachable]. A bound name of the wrong kind gets the kind-specific
   error. *)
let lookup_func_type ?location ctx name =
  let*@ ty = Tbl.find ctx.diagnostics ctx.type_context.types name in
  match (snd ty).typ with
  | Func f -> Some f
  | Struct _ | Array _ | Cont _ ->
      Error.expected_func_type ctx.diagnostics
        ~location:(Option.value ~default:name.info location);
      None

let lookup_struct_type ?location ctx name =
  let*@ ty = Tbl.find ctx.diagnostics ctx.type_context.types name in
  match (snd ty).typ with
  | Struct fields -> Some fields
  | Func _ | Array _ | Cont _ ->
      Error.expected_struct_type ctx.diagnostics
        ~location:(Option.value ~default:name.info location);
      None

(* A canonical key for a set of field names, so two structs with the same fields
   (in any order) get the same key. Identifiers never contain a comma. *)
let field_set_key names = String.concat "," (List.sort_uniq compare names)

(* The unique struct type whose field-set matches the literal's [fields], or
   [None] when none or several do (then the type is ambiguous and must be
   named). O(#fields) given the precomputed [ctx.structs_by_fields] map. *)
let infer_struct_by_fields ctx fields =
  let key =
    field_set_key (List.map (fun ((idx : Ast.ident), _) -> idx.desc) fields)
  in
  match Hashtbl.find_opt ctx.structs_by_fields key with
  | Some (Some name) -> Some name
  | Some None | None -> None

(* A struct-literal field's value. A punned field ([None], written [{x}]) stands
   for the like-named local/global, i.e. [Get x]; typing resolves it to that
   explicit [Get], which is what is type-checked and emitted, so lowering never
   sees a pun. *)
let field_value (name : ident) = function
  | Some i -> i
  | None ->
      {
        desc = Get name;
        info = name.info;
        hints = Wax_wasm.Hints.none;
        expected = Unset;
      }

let lookup_array_type ?location ctx name =
  let*@ ty = Tbl.find ctx.diagnostics ctx.type_context.types name in
  match (snd ty).typ with
  | Array field -> Some field
  | Func _ | Struct _ | Cont _ ->
      Error.expected_array_type ctx.diagnostics
        ~location:(Option.value ~default:name.info location);
      None

(* The composite type of a synthesized type (its name starting with ['<'], e.g.
   [<string>] or an inline function type) — used as the [anon_comptype] of an
   [inferred_valtype] so a reference to it renders by that composite type rather
   than by its meaningless synthetic name. [None] for a source-named type. *)
let inline_comptype ctx (name : ident) =
  if name.desc <> "" && name.desc.[0] = '<' then
    Option.map
      (fun (_, (sub : subtype)) -> sub.typ)
      (Tbl.find_opt ctx.type_context.types name)
  else None

(* The name of the function type a continuation type wraps. *)
let lookup_cont_inner ?location ctx name =
  let*@ ty = Tbl.find ctx.diagnostics ctx.type_context.types name in
  match (snd ty).typ with
  | Cont ft -> Some ft
  | Func _ | Struct _ | Array _ ->
      Error.expected_func_type ctx.diagnostics
        ~location:(Option.value ~default:name.info location);
      None

let top_heap_type ctx (t : heaptype) : heaptype option =
  match t with
  | Any | Eq | I31 | Struct | Array | None_ -> Some Any
  | Func | NoFunc -> Some Func
  | Exn | NoExn -> Some Exn
  | Cont | NoCont -> Some Cont
  | Extern | NoExtern -> Some Extern
  | Type ty | Exact ty -> (
      let+@ ty = Tbl.find ctx.diagnostics ctx.types ty in
      match (snd ty).typ with
      | Struct _ | Array _ -> Any
      | Func _ -> Func
      | Cont _ -> Cont)

(* Whether a heap type belongs to the continuation hierarchy, without reporting
   an unbound reference (the caller's normal resolution handles that). *)
let is_cont_heaptype ctx (t : heaptype) =
  match t with
  | Cont | NoCont -> true
  | Type ty | Exact ty -> (
      match Tbl.find_opt ctx.types ty with
      | Some x -> ( match (snd x).typ with Cont _ -> true | _ -> false)
      | None -> false)
  | Any | Eq | I31 | Struct | Array | None_ | Func | NoFunc | Exn | NoExn
  | Extern | NoExtern ->
      false

let diff_ref_type t1 t2 =
  { nullable = t1.nullable && not t2.nullable; typ = t1.typ }

let storage_subtype ctx ty ty' =
  match (ty, ty') with
  | Packed I8, Packed I8 | Packed I16, Packed I16 -> true
  | Value ty, Value ty' ->
      Option.value ~default:true (* Do not generate a spurious error *)
        (let*@ ty = valtype ctx.diagnostics ctx.type_context ty in
         let+@ ty' = valtype ctx.diagnostics ctx.type_context ty' in
         Wax_wasm.Types.val_subtype (subtyping_info ctx) ty ty')
  | Packed I8, Packed I16
  | Packed I16, Packed I8
  | Packed _, Value _
  | Value _, Packed _ ->
      false

let storage_subtype' ctx (ty : Wax_wasm.Types.Internal.storagetype)
    (ty' : Wax_wasm.Types.Internal.storagetype) =
  match (ty, ty') with
  | Packed I8, Packed I8 | Packed I16, Packed I16 -> true
  | Value ty, Value ty' ->
      Wax_wasm.Types.val_subtype (subtyping_info ctx) ty ty'
  | Packed I8, Packed I16
  | Packed I16, Packed I8
  | Packed _, Value _
  | Value _, Packed _ ->
      false

let field_subtype info (ty : Wax_wasm.Types.Internal.fieldtype)
    (ty' : Wax_wasm.Types.Internal.fieldtype) =
  ty.mut = ty'.mut
  && storage_subtype' info ty.typ ty'.typ
  && ((not ty.mut) || storage_subtype' info ty'.typ ty.typ)

(* Whether [ty] is the result cell of a block whose type is being inferred. *)
let is_inferring ty = match Cell.get ty with Collecting _ -> true | _ -> false

(* The type a value passing through a branch to [ty] takes: it continues on the
   stack typed as the target's result. When the target is a block being inferred
   ([Collecting]) with a declared result (an annotation under test, or the context
   type in expression position), that result is the right type — resolve to it, so
   the pass-through is typed as the block's result rather than its own, possibly
   narrower, operand (which would be unsound, see [Collecting.exacts]). With no
   declared result (a fully-inferred block) the [Collecting] cell would leak as a
   value, so the caller keeps the operand's own type instead. *)
let rec resolve_declared ty =
  match Cell.get ty with
  | Collecting { declared = Some d; _ } -> resolve_declared d
  | _ -> ty

(* Whether the inferred type [ty] is a subtype of the expected type [ty'].
   Not a pure relation: when the two are compatible it *unifies* their
   union-find cells (so an as-yet-unconstrained literal like [Int]/[Number]
   gets pinned to the concrete type it is checked against). [Unknown] or [Error]
   on the left (dead code / error recovery) is a subtype of anything;
   [UnknownRef] is a subtype of every reference type but of no other (so a
   numeric use of it is rejected). None of the three appears on the right
   because expected types always come from a real declaration, annotation or
   instruction signature — hence the [assert]. *)
let rec subtype ?location ?(pin = true) ctx ty ty' =
  let ity = Cell.get ty in
  let ity' = Cell.get ty' in
  match (ity, ity') with
  (* [ty'] is a block result being inferred. Record [ty]'s natural type — a
     snapshot taken before any validation below resolves it — as a value reaching
     the block's exit, to be joined later (see [block_infer_general]); pair it with
     [location] when the caller has one, so a join failure can point at the exit.
     When an annotation is under test ([declared]), also validate [ty] against it
     per-delivery and return that result, so a [br]/catch carrying the wrong type
     is reported precisely at its site rather than once, generically, at the join.
     A [Collecting] cell never appears as a real value type, so the left-hand
     cases below treat it like [Unknown]. *)
  | _, Collecting st -> (
      match st.declared with
      | Some d ->
          (* An annotation is under test: the [subtype] check below may resolve
             [ty], so record a snapshot of its natural type first — the keep-bool
             decision compares that pre-validation type against the annotation. *)
          st.collected <- (location, Cell.make ity) :: st.collected;
          subtype ?location ~pin ctx ty d
      | None ->
          (* No annotation under test, so nothing here resolves [ty]: record the
             live cell. When the join later settles the block's result to a
             concrete width, that propagates back to a flexible numeric literal
             reaching the exit (the only types [join_value_types] merges) — else
             the literal keeps its default width and [To_wasm] emits, e.g., an f64
             const as the fall-through of an f32-typed block (invalid). *)
          st.collected <- (location, ty) :: st.collected;
          true)
  | Collecting _, _ -> true
  | Valtype ty, Valtype ty' ->
      Wax_wasm.Types.val_subtype (subtyping_info ctx) ty.internal ty'.internal
  (* A flexible numeric literal ([Number]/[Int]/[LargeInt]/[Float]) never appears
     as the expected (right-hand) type: an expected type comes from a declaration,
     annotation or instruction signature — always a concrete valtype, or a
     [Collecting] block result (handled above). This is the numeric counterpart of
     the [Unknown]/[Error]/[UnknownRef] right-hand assertion below. *)
  | _, (Number | Int | LargeInt | Float) -> assert false
  | Null, Null ->
      Cell.merge ty ty' ity;
      true
  | Number, Valtype { internal = I32 | I64 | F32 | F64; _ }
  | Int, Valtype { internal = I32 | I64; _ }
  | Float, Valtype { internal = F32 | F64; _ }
  (* LargeInt — a numeric literal too big for i32: never i32, defaults to i64; the
     concrete types it accepts are i64, f32 and f64. *)
  | LargeInt, Valtype { internal = I64 | F32 | F64; _ }
  | Null, Valtype { internal = Ref { nullable = true; _ }; _ } ->
      Cell.merge ty ty' ity';
      true
  | ( Null,
      Valtype
        {
          internal = I32 | I64 | F32 | F64 | V128 | Ref { nullable = false; _ };
          _;
        } )
  | Valtype _, Null
  | Number, (Null | Valtype { internal = V128 | Ref _; _ })
  | Int, (Null | Valtype { internal = F32 | F64 | V128 | Ref _; _ })
  | Float, (Null | Valtype { internal = I32 | I64 | V128 | Ref _; _ })
  | LargeInt, (Null | Valtype _) ->
      false
  | (Int8 | Int16), _ | _, (Int8 | Int16) -> false
  | Unknown, (Valtype _ as t) ->
      (* A polymorphic value (a hole taken off the [Unreachable] stack of dead
         code) genuinely takes whatever concrete type consumes it: pin it, so
         [To_wasm] sees a definite type instead of [None] — which it can only
         lower as [unreachable], dropping the enclosing instruction. The
         universal-bottom counterpart of the [UnknownRef] reference pin below,
         and of [join_value_types]'s pin of an [Unknown] block exit. Not pinned
         under [~pin:false] (a [br_table], whose one value is checked against
         several targets of legitimately different types — pinning it to the
         first would wrongly reject the rest); it stays [Unknown] and [To_wasm]
         passes the hole through the polymorphic stack unchanged. *)
      if pin then Cell.set ty t;
      true
  | (Unknown | Error), _ -> true
  | UnknownRef, (Valtype { internal = Ref _; _ } as t) ->
      (* The bottom reference is a subtype of every reference; pin it to the
         hierarchy it is checked against, so it resolves to a concrete type in
         that hierarchy rather than the default any-hierarchy [&none]. Not
         pinned under [~pin:false] for the same [br_table] reason as [Unknown]
         above: a bottom reference reaching targets of different reference types
         (a [&func] and a [&t] label) is a subtype of each, so pinning it to the
         first-checked one would reject the others. *)
      if pin then Cell.set ty t;
      true
  | _, (Unknown | Error | UnknownRef) -> assert false
  | UnknownRef, _ -> false

let cast ctx ty ty' =
  let ity = Cell.get ty in
  match (ity, ty') with
  | (Number | Int), Ref { typ = I31 | Extern; _ } ->
      Cell.set ty (Valtype i32_valtype);
      true
  | (Number | Int), I32 ->
      Cell.set ty (Valtype i32_valtype);
      true
  | (Number | Int), I64 ->
      Cell.set ty (Valtype i64_valtype);
      true
  (* A still-flexible numeric literal ([Number]) folds straight to the target
     float constant. A value already committed to a family — [Int] (an integer
     operation such as [x & y] or [clz]) or [Float] (a float operation, or a
     float literal) — is *not* accepted here for the opposite family: a plain
     [int <-> float] cast needs a signedness ([as f32_s], [as i32_u]) to lower to
     a [convert]/[trunc], so it falls through to the cast error, exactly as a cast
     of a concrete [i32]/[f32] value does. (An integer-to-float [convert] would
     carry a sign, as [signed_cast].) *)
  | (Number | Float), F32 ->
      Cell.set ty (Valtype f32_valtype);
      true
  | (Number | Float), F64 ->
      Cell.set ty (Valtype f64_valtype);
      true
  (* The literal is always i64 here since it is too big for i32. A cast to
     [i32] wraps it (the low 32 bits), as produced when decompiling e.g.
     [i64.extend32_s] of a constant; a cast to [i64] is the identity. *)
  | LargeInt, (I32 | I64) ->
      Cell.set ty (Valtype i64_valtype);
      true
  (* A cast to a float folds the literal to a float constant, exactly like a
     small [Number] literal above (a runtime integer-to-float [convert] would
     carry a sign, as [signed_cast]). Settle the operand at the target float type
     so [to_wasm] emits [f32.const]/[f64.const] rather than an unlowerable [i64]
     value. *)
  | LargeInt, F32 ->
      Cell.set ty (Valtype f32_valtype);
      true
  | LargeInt, F64 ->
      Cell.set ty (Valtype f64_valtype);
      true
  (* [ref.i31] takes an [i32]; the i64-sized literal wraps to [i32] first, exactly
     like [i64 as &i31] below ([to_wasm] re-emits [i32.wrap_i64] then [ref.i31]).
     This is the residue of [(big as i32) as &i31] after [simplify] fuses the
     inner wrap into the [i31] cast. [&extern] is the same with
     [extern.convert_any] appended, as [i64 as &extern] below. *)
  | LargeInt, Ref { typ = I31 | Extern; _ } ->
      Cell.set ty (Valtype i64_valtype);
      true
  | LargeInt, _ -> false (* not v128 or another reference *)
  | Null, Ref { typ = ty'; _ } ->
      (let>@ typ = top_heap_type ctx ty' in
       let ty' = Ref { nullable = true; typ } in
       let>@ ity' = valtype ctx.diagnostics ctx.type_context ty' in
       Cell.set ty
         (Valtype { typ = ty'; internal = ity'; anon_comptype = None }));
      true
  | Valtype { internal = F32 | F64; _ }, (F32 | F64)
  | Valtype { internal = I32 | I64; _ }, I32
  | Valtype { internal = I64; _ }, I64
  | Valtype { internal = V128; _ }, V128
  (* [i32 as &i31] is [ref.i31]; [i64 as &i31] wraps to [i32] first. *)
  | Valtype { internal = I32 | I64; _ }, Ref { typ = I31; _ }
  (* [i32 as &extern]: [ref.i31] then [extern.convert_any]; [i64 as &extern]
     wraps to [i32] first, as [i64 as &i31] above. *)
  | Valtype { internal = I32 | I64; _ }, Ref { typ = Extern; _ } ->
      true
  | Valtype { internal = Ref _ as ity; _ }, Ref { typ = ty'; _ } -> (
      let sub a b = Wax_wasm.Types.val_subtype (subtyping_info ctx) a b in
      Option.value ~default:true
        (let*@ typ = top_heap_type ctx ty' in
         let+@ ity' =
           valtype ctx.diagnostics ctx.type_context
             (Ref { nullable = true; typ })
         in
         sub ity ity')
      ||
      (* [extern] <-> [any] across hierarchies ([any.convert_extern] /
         [extern.convert_any]), then a [ref.cast] to the concrete target. The
         [ref.cast] handles nullability, so only hierarchy membership is checked
         here — test the operand against a *nullable* reference regardless of the
         target's nullability (a nullable operand cast to a non-null target is a
         valid convert-then-null-checking-cast). *)
      match ty' with
      | Extern -> sub ity (Ref { nullable = true; typ = Any })
      | Any -> sub ity (Ref { nullable = true; typ = Extern })
      | _ ->
          Option.value ~default:false
            (let+@ top = top_heap_type ctx ty' in
             (sub ity (Ref { nullable = true; typ = Extern }) && top = Any)
             || (sub ity (Ref { nullable = true; typ = Any }) && top = Extern)))
  | ( (Number | Int | Float | Valtype { internal = I32 | F32 | I64 | F64; _ }),
      ( Ref
          {
            typ =
              ( Func | NoFunc | Exn | NoExn | Cont | NoCont | Extern | NoExtern
              | Any | Eq | Array | Struct | Type _ | Exact _ | None_ );
            _;
          }
      | V128 ) )
  | Valtype { internal = F32 | F64; _ }, (I32 | I64)
  | Valtype { internal = I32 | I64; _ }, (F32 | F64)
  | Valtype { internal = I32; _ }, I64
  (* A value committed to one numeric family cast to the other with a plain
     (unsigned) cast: it needs a signedness to lower to a [convert]/[trunc], so
     it is rejected here (a still-flexible [Number] literal folds above). *)
  | Int, (F32 | F64)
  | Float, I64
  | ( (Float | Valtype { internal = F32 | F64 | V128; _ }),
      (I32 | Ref { typ = I31; _ }) )
  | (Null | Valtype { internal = Ref _; _ }), (I32 | I64 | F32 | F64 | V128)
  | Valtype { internal = V128; _ }, (I64 | F32 | F64 | Ref _)
  | (Int8 | Int16), _ ->
      false
  (* An operand already known to be a REFERENCE cannot be cast to a numeric type,
     exactly as the concrete-reference case above says — [UnknownRef] is "some
     reference, type not yet resolved", not "unknown whether a reference". Left in
     the blanket-accepting arm below, the check passed here and [to_wasm] was later
     handed a ref->float cast it has no lowering for, hitting its [assert false]
     rather than reporting anything (a wax-mutation-fuzzer crash). A genuinely
     unresolved [Unknown] hole must stay polymorphic and is still accepted: it is a
     dead-code stack value that unifies with whatever its block needs. *)
  | UnknownRef, (I32 | I64 | F32 | F64 | V128) -> false
  | (Unknown | Error | UnknownRef | Collecting _), _ -> true

let signed_cast ctx ty ty' =
  let ity = Cell.get ty in
  match (ity, ty') with
  | (Int8 | Int16), (`I32 | `I64) -> true
  | Valtype { internal = Ref _ as ity; _ }, (`I32 | `I64) ->
      (* [i31.get] extracts an [i32]; [&ref as i64_X] widens it further. *)
      Wax_wasm.Types.val_subtype (subtyping_info ctx) ity
        (Ref { nullable = true; typ = Any })
  | Null, (`I32 | `I64) ->
      (* As for a concrete any-hierarchy reference above ([null] is a valid
         [&?i31]): [ref.cast (ref i31)] + [i31.get], widened for [i64] — traps
         at runtime, like the reference case. Pin the operand to [&?any] so
         [to_wasm] takes that path. *)
      Cell.set ty
        (Valtype
           {
             typ = Ref { typ = Any; nullable = true };
             internal = Ref { typ = Any; nullable = true };
             anon_comptype = None;
           });
      true
  | (Number | Int), (`I64 | `F32 | `F64) ->
      (* [i64.extend_i32], [f*.convert_i32]: default the integer source to i32. *)
      Cell.set ty (Valtype i32_valtype);
      true
  | LargeInt, (`F32 | `F64) ->
      (* [f*.convert_i64]: a [LargeInt] source defaults to i64. *)
      Cell.set ty (Valtype i64_valtype);
      true
  | LargeInt, (`I32 | `I64) ->
      (* The only numeric -> i32/i64 signed cast is a float truncation
         ([iNN.trunc_f*_X]) — there is no i64->i32 or i64->i64 signed *integer*
         conversion — so the flexible source is a float and defaults to f64, as
         the [Number, `I32] case below. Without this a [LargeInt] there was
         rejected, so a decompiled [iNN.trunc_f* (f*.const <big>)] — which
         renders the const as a large integer literal — failed to recompile. *)
      Cell.set ty (Valtype f64_valtype);
      true
  | Valtype { internal = I32; _ }, `I64
  | Valtype { internal = I32 | I64; _ }, (`F32 | `F64)
  | Valtype { internal = F32 | F64; _ }, (`I32 | `I64) ->
      true
  | Number, `I32 ->
      (* The only numeric -> i32 signed cast is a float truncation
         ([i32.trunc_f*_s]), so a flexible [Number] source is a float and defaults
         to f64 (like the [Float] case below). ([Int] is rejected below: no
         integer -> i32 signed conversion exists.) *)
      Cell.set ty (Valtype f64_valtype);
      true
  | Int, `I32 (* no integer-to-i32 signed conversion exists *)
  | Valtype { internal = I32; _ }, `I32
  | Valtype { internal = I64; _ }, (`I32 | `I64)
  (* A signed cast to a float is an integer->float [convert]; float->float has no
     signedness, so a float source (concrete or the abstract [Float]) is rejected
     for a float target — only [demote]/[promote] via a plain cast. *)
  | (Float | Valtype { internal = F32 | F64; _ }), (`F32 | `F64)
  | (Int8 | Int16), (`F32 | `F64)
  (* An any-hierarchy reference (or [null]) to [i64] is accepted above
     ([i31.get] + extend); to a float it is rejected — no reference-to-float
     conversion exists. *)
  | ( ( Null
      | Valtype
          {
            internal =
              Ref
                {
                  typ =
                    Type _ | Exact _ | None_ | Struct | Array | I31 | Eq | Any;
                  _;
                };
            _;
          } ),
      (`F32 | `F64) )
  | ( Valtype
        {
          internal =
            ( V128
            | Ref
                {
                  typ =
                    ( Func | NoFunc | Exn | NoExn | Cont | NoCont | Extern
                    | NoExtern );
                  _;
                } );
          _;
        },
      _ ) ->
      false
  (* A bare float literal carries the abstract [Float]; default it to its
     canonical f64 (like the concrete [F32 | F64] arms above) so a strict cast on
     it — e.g. [1.5 as i64_s_strict], the [i64.trunc_f64_s] a decompiled
     [f64.const] produces — type-checks instead of being rejected as float. *)
  | Float, (`I32 | `I64) ->
      Cell.set ty (Valtype f64_valtype);
      true
  (* A polymorphic reference (the bottom [UnknownRef], e.g. [null!] in dead code)
     is a reference: a signed cast to [i32]/[i64] is [i31.get] (as for a concrete
     any-hierarchy reference above), but it can never convert to a float. *)
  | UnknownRef, (`I32 | `I64) -> true
  | UnknownRef, (`F32 | `F64) -> false
  | (Unknown | Error | Collecting _), _ -> true

(*** The typing stack ***)

type stack =
  | Unreachable
  | Empty
  | Poisoned
    (* The poison of an already-reported failure whose stack effect is
         unknown (a producer that did not resolve, an underflow): pops yield
         [Error] silently — unlike [Unreachable] (dead code), whose pops yield
         [Unknown] and re-default, and which the dead-code lint keys on. *)
  | Cons of location option * inferred_type Cell.t * stack

let rec output_stack pp st =
  let module SP = Wax_utils.Styled_printer in
  match st with
  | Empty -> ()
  | Unreachable ->
      Wax_utils.Printer.space pp.SP.printer ();
      SP.print_styled pp Wax_utils.Colors.Keyword "unreachable"
  | Poisoned ->
      Wax_utils.Printer.space pp.SP.printer ();
      SP.print_styled pp Wax_utils.Colors.Keyword "poisoned"
  | Cons (_, ty, st) ->
      Wax_utils.Printer.space pp.SP.printer ();
      output_inferred_type_styled pp ty;
      output_stack pp st

let print_stack st =
  Wax_utils.Printer.run_err (fun p ->
      let pp =
        Wax_utils.Styled_printer.create ~printer:p
          ~theme:Wax_utils.Colors.no_color
          ~trivia:(Wax_utils.Trivia.empty ())
          ()
      in
      Wax_utils.Printer.string p "Stack:";
      output_stack pp st);
  (st, ())

let _ = print_stack

(* The typing monad. A monadic action is a function [stack -> stack * 'a]: it
   reads the operand stack, may push/pop, and returns the new stack alongside
   its result. This threads the stack implicitly so the instruction cases read
   top-to-bottom instead of passing [st] by hand. The operators:

   - [return v]      lift a value, leaving the stack unchanged;
   - [let* x = e]    bind: run [e], thread its stack into the continuation;
   - [let*! x = e]   run [e : _ option], short-circuiting a [None] (a failed
                     lookup) by returning an [unreachable] recovery instruction
                     so typing continues without cascading errors;
   - [unreachable e] run [e] but mark the resulting stack [Unreachable] (the
                     polymorphic stack of code after a [br]/[return]/etc.).

   Not to be confused with the pure-option [let*@]/[let+@]/[let>@] above. *)
let unreachable e st =
  let _, v = e st in
  (Unreachable, v)

let return v st = (st, v)

let ( let* ) e f st =
  let st, v = e st in
  f v st

let ( let*! ) e f =
  match e with
  | Some v -> f v
  | None ->
      return
        {
          desc = Ast.Unreachable;
          info = ([| Cell.make Error |], (Ast.no_loc ()).info);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }

(* Pop the top operand's type. An [Unreachable] (polymorphic) stack yields a
   fresh [Unknown] and consumes nothing; [Empty] is a genuine stack underflow.
   No diagnostic is emitted here: the placeholder cell is recorded in
   [ctx.missing_holes] with the counts, so the hole that ends up consuming it
   reports the underflow at its own location ([report_missing_hole]) — sparing
   the caller any knowledge of how the pending values are distributed — and
   [with_holes] covers a placeholder that recovery drops. An underflow turns
   the stack unreachable (mirroring the Wasm validator's [pop_any]), so one
   missing value is tracked once rather than once per subsequent pop. *)
let pop_any ctx batch current expected st =
  match st with
  | Unreachable -> (st, Cell.make Unknown)
  | Poisoned ->
      let cell = Cell.make Error in
      (* Poisoned by this very run's underflow (below): this value is missing
         too, so track it under the same batch — the report lands on the FIRST
         hole without a value. A stack poisoned before this run keeps plain,
         silent placeholders. *)
      (match !batch with
      | Some b -> ctx.missing_holes := (cell, b) :: !(ctx.missing_holes)
      | None -> ());
      (st, cell)
  | Cons (_, ty, r) -> (r, ty)
  | Empty ->
      let cell = Cell.make Error in
      let b =
        {
          hole_reported = false;
          hole_actual = current;
          hole_expected = expected;
        }
      in
      batch := Some b;
      ctx.missing_holes := (cell, b) :: !(ctx.missing_holes);
      (Poisoned, cell)

(* Pop [count] pending values, returning them together with the underflow
   batch, if one occurred (for [with_holes]'s fallback report). *)
let pop_many ctx count =
  let batch = ref None in
  let rec loop n accu =
    if n = count then return (accu, batch)
    else
      let* ty = pop_any ctx batch n count in
      loop (n + 1) (ty :: accu)
  in
  loop 0 []

let pop ctx kind ~location current expected ty st =
  match st with
  | Unreachable | Poisoned -> (st, ())
  | Cons (loc_opt, ty', r) -> (
      match Cell.get ty' with
      | Error ->
          (* The top value is the poison of an already-reported error. Leave it
             on the stack instead of consuming it — like the polymorphic
             [Unreachable] case above — so it keeps suppressing leftover-stack
             diagnostics in this scope (see [with_empty_stack]). Consuming it
             would strip the poison and let a cascade surface: e.g. a rejected
             instruction recovers as an [Error] value where the correct one was
             void, and popping that phantom as the block's result leaves the
             genuine value below it reading as a bogus leftover. *)
          (st, ())
      | _ ->
          (if not (subtype ctx ty' ty) then
             match loc_opt with
             | Some loc ->
                 Error.expression_type_mismatch ctx.diagnostics ~location:loc
                   ~provided:ty' ~expected:ty
             | None ->
                 Error.type_mismatch ctx.diagnostics ~location ~current ty' ty);
          (r, ()))
  | Empty ->
      Error.short_stack ctx.diagnostics kind
        ~location:
          (match kind with
          | `Input -> loc_first_char location
          | `Holes -> location
          | `Output -> loc_last_char location)
        ~actual:(expected - current - 1)
        ~expected;
      (* As in [pop_any]: an underflow poisons the stack, so one missing value
         is reported once, not once per remaining pop. *)
      (Poisoned, ())

let pop_args ctx kind ~location args =
  let len = Array.length args in
  let rec loop pos =
    if pos = 0 then return ()
    else
      let pos = pos - 1 in
      let* () = pop ctx kind ~location pos len args.(pos) in
      loop pos
  in
  loop len

(* Pushing an [Error] value poisons the whole stack ([Unreachable]): the failed
   producer's true arity is unknown (a call that did not resolve may have
   produced any number of values), so later consumers must absorb any count
   silently — reporting an underflow there would anchor a derived error away
   from the original fault. This is the push-side twin of [with_empty_stack]'s
   rule that an [Error] anywhere on the stack suppresses the leftover report,
   and of [pop_any]'s underflow-turns-unreachable. *)
let push loc ty st =
  match Cell.get ty with
  | Error -> ((match st with Unreachable -> Unreachable | _ -> Poisoned), ())
  | _ -> (Cons (loc, ty, st), ())

let push_results ~loc results =
  let len = Array.length results in
  let loc = if len = 1 then Some loc else None in
  let rec loop i =
    if i = len then return ()
    else
      let* () = push loc results.(i) in
      loop (i + 1)
  in
  loop 0

type empty_stack_context = Expression | Block | Function

let with_empty_stack ctx ~kind:_ ~location f =
  let st, res = f Empty in
  (* Decide what to report about values still on the stack. A value of type
     [Error] is the poison of an already-reported error, so if any leftover
     carries it the stack is unreliable and the whole diagnostic is a cascade —
     suppress it. Otherwise the leftovers are genuine values and are reported: a
     caret on each that has a source location, or — for values that carry only
     an error-recovery placeholder location, which are still real values, just
     not locatable — the construct itself. [scan] gathers the locatable values
     (topmost first, after the final [List.rev]) and whether any [Error] value
     is present. *)
  let rec scan has_error locs = function
    | Cons (loc, cell, st) ->
        let has_error =
          has_error || match Cell.get cell with Error -> true | _ -> false
        in
        let locs = match loc with None -> locs | Some loc -> loc :: locs in
        scan has_error locs st
    | Empty | Unreachable | Poisoned -> (has_error, List.rev locs)
  in
  (match st with
  | Empty | Unreachable | Poisoned -> ()
  | Cons _ -> (
      match scan false [] st with
      | true, _ -> () (* poison on the stack: an already-reported cascade *)
      | false, location :: rest ->
          (* Point a caret right at each locatable leftover value rather than at
             the (potentially large) enclosing construct. *)
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
      | false, [] ->
          (* Real values remain but none carries a usable location: name the
             construct and list what is on the stack. *)
          Error.non_empty_stack ctx.diagnostics ~location (fun pp ->
              output_stack pp st)));
  res

(*** Instruction-checking helpers ***)

let internalize_valtype ctx typ =
  let+@ internal = valtype ctx.diagnostics ctx.type_context typ in
  { typ; internal; anon_comptype = None }

let internalize ?inline ctx typ =
  let+@ internal = valtype ctx.diagnostics ctx.type_context typ in
  valtype_cell { typ; internal; anon_comptype = inline }

(* Check that a source element reference type can be stored where [dst] elements
   are expected (table.copy / table.init / array.init_elem): [src] must be a
   subtype of [dst]. *)
let check_elem_subtype ctx ~location ~src ~dst =
  match
    (internalize_valtype ctx (Ref src), internalize_valtype ctx (Ref dst))
  with
  | Some s, Some d ->
      if
        not
          (Wax_wasm.Types.val_subtype (subtyping_info ctx) s.internal d.internal)
      then
        Error.incompatible_element_type ctx.diagnostics ~location
          (valtype_cell s) (valtype_cell d)
  | _ -> ()

(* The inferred type of a value read from a field: a packed [i8]/[i16] field
   reads back as the unpacked [Int8]/[Int16] cell, any other as its value type.
   (Distinct from the [fieldtype] type converter above, which maps a source
   field type to its [Internal] form.) *)
let field_read_type ctx (f : fieldtype) =
  match f.typ with
  | Value typ -> internalize ctx typ
  | Packed I8 -> Some (Cell.make Int8)
  | Packed I16 -> Some (Cell.make Int16)

let unpack_type (f : fieldtype) =
  match f.typ with Value v -> v | Packed _ -> I32

let branch_target ctx label =
  let rec find l label =
    match l with
    | [] ->
        let suggestions =
          Wax_utils.Spell_check.f
            (fun f ->
              List.iter
                (fun (l, _) -> Option.iter (fun (l : Ast.ident) -> f l.desc) l)
                ctx.control_types)
            label.Annot.desc
        in
        Error.unbound_name ctx.diagnostics ~location:label.info ~suggestions
          "label" label;
        ctx.unresolved_label := true;
        [||]
    | (Some label', res) :: _ when label.desc = label'.Annot.desc ->
        ctx.used_labels :=
          IntSet.add label'.info.loc_start.pos_cnum !(ctx.used_labels);
        record_reference ctx.resolve_links label.info [ label'.info ];
        res
    | _ :: rem -> find rem label
  in
  find ctx.control_types label

(* Whether [label] resolves to an in-scope control label. Unlike
   [branch_target], reports nothing and records no use; used to tell an unbound
   label (already diagnosed) from a legitimately void target when both present as
   [[||]]. *)
let label_in_scope ctx (label : Ast.ident) =
  List.exists
    (fun ((l : Ast.ident option), _) ->
      match l with Some l' -> l'.desc = label.desc | None -> false)
    ctx.control_types

(* Draw "did you mean" suggestions from the namespaces an identifier may
   legitimately name, which depends on how it is used:
   - [Get] reads any value, so a local, a global or a function;
   - [Set] assigns, so a local or a mutable global;
   - [Tee] only ever targets a local. *)
let get_suggestions ctx name =
  Wax_utils.Spell_check.f
    (fun f ->
      StringMap.iter (fun k _ -> f k) ctx.locals;
      Tbl.iter ctx.globals (fun k _ -> f k);
      Tbl.iter ctx.functions (fun k _ -> f k))
    name

let set_suggestions ctx name =
  Wax_utils.Spell_check.f
    (fun f ->
      StringMap.iter (fun k _ -> f k) ctx.locals;
      Tbl.iter ctx.globals (fun k (mut, _) -> if mut then f k))
    name

let local_suggestions ctx name =
  Wax_utils.Spell_check.f
    (fun f -> StringMap.iter (fun k _ -> f k) ctx.locals)
    name

(* One-line summaries of a resolved reference, rendered the way diagnostics do,
   for a hover on a name that is not itself an expression (a type reference, a
   [Set]/[Tee] target, a bare global). A poison value ([None]) has no summary. *)
let hover_of_valtype ty = Option.map (fun ity -> Value_type ity) ty

let hover_of_global ((_, ty) : bool * inferred_valtype option) =
  hover_of_valtype ty

let hover_of_type ((_, st) : Wax_wasm.Types.ref_index * subtype) =
  Some (Type_def st)

(* A name in value position resolves, in order, to a local, then a global, then
   a function (as a non-null reference); [Get]/[Set]/[Tee] share this ladder and
   only differ in what they do with each outcome. *)
type resolved_var =
  | Local of inferred_valtype option * Ast.location
  | Global of bool (* mutable *) * inferred_valtype option
  | Func_ref of Wax_wasm.Types.Id.t * string * bool
  | Poisoned
    (* A function whose signature failed to resolve: bound, already reported
         at its definition, reads as [Error] with no further report. *)
  | Unbound

let resolve_variable ctx (idx : Ast.ident) =
  match StringMap.find_opt idx.desc ctx.locals with
  | Some (ty, def) ->
      record_reference ~hover:(hover_of_valtype ty) ctx.resolve_links idx.info
        [ def ];
      Local (ty, def)
  | None -> (
      match Tbl.find_opt ctx.globals idx with
      | Some (mut, ty) -> Global (mut, ty)
      | None -> (
          match Tbl.find_opt ctx.functions idx with
          | Some (Some (ty, ty', exact)) -> Func_ref (ty, ty', exact)
          | Some None -> Poisoned
          | None -> Unbound))

(* Whether [name] denotes a memory (resp. table) usable as a method/index
   receiver — [mem.load(..)], [tab[..]], [tab.size()]. A local of the same name
   shadows it: Wax resolves a bare name to a local first, and globals, functions,
   memories and tables share one namespace (so only a local can collide), so the
   receiver form must defer to the local just as [Get name] does. *)
let memory_receiver ctx (name : Ast.ident) =
  (not (StringMap.mem name.desc ctx.locals))
  && Tbl.find_opt ctx.memories name <> None

let table_receiver ctx (name : Ast.ident) =
  (not (StringMap.mem name.desc ctx.locals))
  && Tbl.find_opt ctx.tables name <> None

(* Likewise for a data/element segment named by [seg.drop()] (and the segment
   operand of [mem.init]/[tab.init]/array segment ops): usable as such only when
   not shadowed by a local. *)
let segment_receiver ctx (name : Ast.ident) =
  (not (StringMap.mem name.desc ctx.locals))
  && (Tbl.find_opt ctx.datas name <> None || Tbl.find_opt ctx.elems name <> None)

(* When [e] is an atomic narrow-load call [mem.atomic_load8/16(p)] (whose
   raw-bits result a cast resolves), its access width. Used to reject an
   [as iN_s] cast on it: only the zero-extending [_u] atomic loads exist. *)
let atomic_narrow_load_width ctx e =
  match e.desc with
  | Call ({ desc = StructGet ({ desc = Get memname; _ }, meth); _ }, _)
    when memory_receiver ctx memname -> (
      match Wax_wasm.Atomics.of_method_name meth.desc with
      | Some (Wax_wasm.Atomics.Load ((`W8 | `W16) as w)) -> Some w
      | _ -> None)
  | _ -> None

(* Check the operands of an integer (resp. float) binary operator and return
   the unified result-type cell — the two operand cells are merged on success,
   so the caller takes [typ1] as the operator's result type. *)
let check_int_bin_op ctx ~location typ1 typ2 =
  (match (Cell.get typ1, Cell.get typ2) with
  | Valtype { internal = I32; _ }, Valtype { internal = I32; _ }
  | Valtype { internal = I64; _ }, Valtype { internal = I64; _ }
  | (Valtype { internal = I32 | I64; _ } | Int), (Number | Int) ->
      Cell.merge typ1 typ2 (Cell.get typ1)
  | (Number | Int), Valtype { internal = I32 | I64; _ } ->
      Cell.merge typ1 typ2 (Cell.get typ2)
  | Number, Number -> Cell.merge typ1 typ2 Int
  (* A LargeInt operand forces i64: it pairs with i64 or another flexible integer
     (never i32). *)
  | Valtype { internal = I64; _ }, LargeInt ->
      Cell.merge typ1 typ2 (Cell.get typ1)
  | LargeInt, Valtype { internal = I64; _ } ->
      Cell.merge typ1 typ2 (Cell.get typ2)
  (* An integer-only operator pins every [LargeInt] operand to i64: it exceeds
     i32, and the result is a committed integer (never a float), so the pair takes
     i64 rather than the still-float-capable [LargeInt]. *)
  | LargeInt, (LargeInt | Number | Int) | (Number | Int), LargeInt ->
      Cell.merge typ1 typ2 (Valtype i64_valtype)
  (* A fully-flexible [Number] on the left pairs with a flexible [Int] (the
     symmetric [Int, Number] and [Number, Number] cases are above). *)
  | Number, Int -> Cell.merge typ1 typ2 Int
  | _ -> Error.binop_type_mismatch ctx.diagnostics ~location typ1 typ2);
  typ1

let check_float_bin_op ctx ~location typ1 typ2 =
  (match (Cell.get typ1, Cell.get typ2) with
  | Valtype { internal = F32; _ }, Valtype { internal = F32; _ }
  | Valtype { internal = F64; _ }, Valtype { internal = F64; _ }
  | (Valtype { internal = F32 | F64; _ } | Float), (Number | Float | LargeInt)
    ->
      Cell.merge typ1 typ2 (Cell.get typ1)
  | (Number | Float | LargeInt), Valtype { internal = F32 | F64; _ } ->
      Cell.merge typ1 typ2 (Cell.get typ2)
  (* Two flexible operands of a float operator (the [Float, _] cases are above):
     a large-int literal is taken as a float here, so anything pairs to [Float]. *)
  | (Number | LargeInt), (Number | Float | LargeInt) ->
      Cell.merge typ1 typ2 Float
  | _ -> Error.binop_type_mismatch ctx.diagnostics ~location typ1 typ2);
  typ1

(* Check and unify the operands of a numeric binary operator that accepts either
   integers or floats (+, -, *, ==, !=); the two cells are merged to their common
   type. Operands here are concrete or flexible numeric literals — the caller
   handles the abstract [Unknown]/[Error] arms. Two fully-flexible [Number]s stay
   [Number] (the operator could still resolve either way); any more committed
   operand pins the pair to its group. Mirrors [check_int_bin_op] (int group) and
   [check_float_bin_op] (float group) unioned. *)
let check_num_concrete ctx ~location ty1 ty2 =
  match (Cell.get ty1, Cell.get ty2) with
  | Valtype { internal = I32; _ }, Valtype { internal = I32; _ }
  | Valtype { internal = I64; _ }, Valtype { internal = I64; _ }
  | Valtype { internal = F32; _ }, Valtype { internal = F32; _ }
  | Valtype { internal = F64; _ }, Valtype { internal = F64; _ } ->
      ()
  | (Valtype { internal = I32 | I64; _ } | Int), (Number | Int)
  | (Valtype { internal = F32 | F64; _ } | Float), (Number | Float | LargeInt)
    ->
      Cell.merge ty1 ty2 (Cell.get ty1)
  | (Number | Int), Valtype { internal = I32 | I64; _ }
  | (Number | Float | LargeInt), Valtype { internal = F32 | F64; _ } ->
      Cell.merge ty1 ty2 (Cell.get ty2)
  | Valtype { internal = I64; _ }, LargeInt -> Cell.merge ty1 ty2 (Cell.get ty1)
  | LargeInt, Valtype { internal = I64; _ } -> Cell.merge ty1 ty2 (Cell.get ty2)
  (* Two flexible literals (the [Float, _] and [LargeInt, Valtype] cases are
     above). A [LargeInt] with a committed [Int] must be an integer — the [Int]
     cannot be a float — and a [LargeInt] cannot be i32, so their sole common type
     is i64; with another [LargeInt] or a fully-flexible [Number] it stays
     [LargeInt] (the operator could still resolve to a float). *)
  | LargeInt, Int | Int, LargeInt -> Cell.merge ty1 ty2 (Valtype i64_valtype)
  | LargeInt, (LargeInt | Number) | Number, LargeInt ->
      Cell.merge ty1 ty2 LargeInt
  | LargeInt, Float -> Cell.merge ty1 ty2 Float
  | Number, Float -> Cell.merge ty1 ty2 Float
  | Number, Int -> Cell.merge ty1 ty2 Int
  | Number, Number -> Cell.merge ty1 ty2 Number
  | _ -> Error.binop_type_mismatch ctx.diagnostics ~location ty1 ty2

let field_has_default (ty : fieldtype) =
  match ty.typ with
  | Packed _ -> true
  | Value ty -> (
      match ty with
      | I32 | I64 | F32 | F64 | V128 -> true
      | Ref { nullable; _ } -> nullable)

(* The typed node for [i]: its hints ride along, being advisory metadata the
   typer neither reads nor changes, and so does its [expected] type — the
   decompiler's record of the type this node must have, which the width check
   compares against the cells recorded here. *)
let return_statement (i : location instr)
    (desc : (inferred_type Cell.t array * location) instr_desc) (ty : _ array)
    st =
  ( st,
    {
      desc;
      info = ((ty : _ array), i.info);
      hints = i.hints;
      expected = i.expected;
    } )

let return_expression i desc ty = return_statement i desc [| ty |]

let expression_type ctx (i : _ Ast.instr) =
  let typ, location = i.info in
  match typ with
  | [| ty |] -> ty
  | _ ->
      (* Once per rendered diagnostic: several consumers may query the same node,
         and nested value-less expressions share a start column (e.g. the inner
         and outer of [a.m().m()], both value-less), so a full-span key would let
         two identical "returns N values" errors print at the same location. Key
         on the rendered position (start column) and the reported count — exactly
         what the diagnostic shows — so a genuine second error with a different
         count still surfaces (see the [not_expression_reported] field). *)
      let key = (location.loc_start.Lexing.pos_cnum, Array.length typ) in
      if not (Hashtbl.mem ctx.not_expression_reported key) then (
        Hashtbl.add ctx.not_expression_reported key ();
        (* An unresolved label in this function makes the value shape
           unreliable (see [unresolved_label]); stay quiet then. *)
        if not !(ctx.unresolved_label) then
          Error.not_an_expression ctx.diagnostics ~location (Array.length typ));
      Cell.make Error

let check_subtype ?(pin = true) ?expected_at ctx ~location ty' ty =
  (* Pass [location] so that, when [ty] is an inferring block result, the value
     is recorded with its branch site (see [Collecting]). *)
  if not (subtype ~location ~pin ctx ty' ty) then
    Error.expression_type_mismatch ?expected_at ctx.diagnostics ~location
      ~provided:ty' ~expected:ty

(* [~pin:false] checks the subtypes without resolving a polymorphic left-hand
   value against the (single) right-hand type — for a [br_table], whose one set
   of values is checked against every target label, so pinning a bottom value to
   the first target's type would wrongly reject a later, differently-typed one
   (see {!subtype}). *)
let check_subtypes ?(pin = true) ?expected_at ctx ~location types' types =
  if Array.length types' <> Array.length types then
    Error.value_count_mismatch ctx.diagnostics ~location
      ~expected:(Array.length types) ~provided:(Array.length types')
  else
    Array.iter2
      (fun ty' ty -> check_subtype ~pin ?expected_at ctx ~location ty' ty)
      types' types

let check_type ctx i ty =
  let ty' = expression_type ctx i in
  let ok = subtype ctx ty' ty in
  if not ok then
    Error.expression_type_mismatch ctx.diagnostics ~location:(snd i.info)
      ~provided:ty' ~expected:ty

(* [standalone_valtype] is context-independent (its only reference result is the
   built-in [None_] bottom), so the typer's ctx-threading call sites delegate to
   the pure {!Typing_env.standalone_valtype}; the [ctx] is kept for call-site
   uniformity. *)
let standalone_valtype _ctx ty = Typing_env.standalone_valtype ty

(* Resolve the type that an omitted annotation takes from its initializer, as in
   [let x = e] or [const x = e]: an as-yet-unconstrained literal is pinned to a
   concrete type the way the final type erasure does (int/number -> i32,
   float -> f64, null -> nullref), so the binding gets a definite type. Mutates
   [ty] so later uses observe the resolved type. *)
let resolve_omitted_valtype ctx ty =
  match Cell.get ty with
  | Valtype v -> Some v
  | LargeInt ->
      let v = i64_valtype in
      Cell.set ty (Valtype v);
      Some v
  | Int | Number | Int8 | Int16 | Unknown | Error | Collecting _ ->
      let v = i32_valtype in
      Cell.set ty (Valtype v);
      Some v
  | Float ->
      let v = f64_valtype in
      Cell.set ty (Valtype v);
      Some v
  | Null ->
      let+@ v =
        internalize_valtype ctx (Ref { nullable = true; typ = None_ })
      in
      Cell.set ty (Valtype v);
      v
  (* The bottom reference concretizes to the non-null [&none], matching the type
     [null!] produced before [UnknownRef] existed. *)
  | UnknownRef ->
      let+@ v =
        internalize_valtype ctx (Ref { nullable = false; typ = None_ })
      in
      Cell.set ty (Valtype v);
      v

(* The type an unannotated [let]/global binding takes from its initializer,
   recording a poison ([None]) type when the initializer has no concrete one. An
   [Unknown] initializer (unreachable / branch code) reports an error here: a
   binding needs a determinable type to be compiled, and silently demoting it to
   the [Error] type would mask that. An [Error] initializer (already reported)
   stays silent. *)
let bound_value_type ctx ~location result_ty =
  match Cell.get result_ty with
  | Error -> None
  | Unknown ->
      Error.unknown_operand_type ctx.diagnostics ~location;
      None
  | _ -> resolve_omitted_valtype ctx result_ty

(* --- Annotation dropping (the "keep-bool" machinery) -----------------------

   When converting from Wasm, the typed AST is rewritten ([ctx.simplify]) to
   drop type annotations that the inferred types make redundant, so the printed
   Wax is not littered with annotations a reader (or a re-parse) would recover
   anyway. The decision rests on the {!reinfer} value [check_instruction] returns
   alongside each checked node: what an unannotated binding ([let x = <node>])
   would re-infer the node to be, standalone. The binding/construct site then
   drops the annotation precisely when [simplify] is on and that re-inference
   already equals the annotation ([reinfer_needed] says it is not load-bearing).

   The pieces, by where the annotation lives:
   - a scalar value vs. its annotation: the leaf [check_instruction] arm returns
     [Typ] of the value's own snapshot; [reinfer_needed]/[annotation_needed]
     compare its standalone type to the expected one;
   - control constructs ([if]/[?:]/block/loop/try) join their sub-nodes'
     re-inference ([join_reinfer]) so a nested tail reports its own type rather
     than being read through a cell the expected type flowed into;
   - a block/loop/try result type of its own: [block_keep_bool] /
     [block_keep_reinfer], with [context_block_typ] / [finalize_inferred] filling
     an omitted result from context or dropping a redundant declared one;
   - [drop_supertype] is the one relaxation (an immutable binding may drop a
     mere-supertype annotation), applied at the binding site.
   --------------------------------------------------------------------------- *)

(* Whether [i] is a (possibly cast-wrapped) [null].

   This guards the dropping of a redundant type annotation on an initialized
   binding ([let]/[const]) when converting from Wasm. The general rule is to
   drop the annotation when the initializer's type already equals it. That is
   unsound for [null]: [from_wasm] lowers [ref.null t] to [(null : &?t)] (a cast),
   so the initializer's inferred type is the concrete [&?t] and the comparison
   reports the annotation as redundant — but the printed bare [null] re-infers to
   the *floating* null type [&?none], not [&?t], so dropping the annotation would
   not round-trip. The annotation (or the cast) is what pins the type, so we must
   keep it.

   The keep decision now does exactly compare against what omitting the
   annotation re-infers to: the [Cast] arm of [check_instruction] reports [Typ]
   of the floating [&?none] for an elided [null], and the leaf arm the same for a
   bare one, so the ordinary [reinfer_needed] comparison keeps the annotation
   without a special case at the binding site. This predicate remains for the two
   places that still key on the syntactic shape rather than the re-inferred type:
   [classify_trailing] (routing a trailing [null] through the result) and the
   [Cast] arm's own guard (deciding whether the cast can be elided). *)
let rec is_null_initializer (i : _ instr) =
  match i.desc with
  | Null -> true
  | Cast (e, _) -> is_null_initializer e
  | _ -> false

(* Whether an operand's PRINTED form re-parses type-ADAPTIVELY: with no type of
   its own, it takes the hierarchy the enclosing context suggests. A bare [null]
   and a [Hole] (a dead-code stack value, or one reconnecting to a bottom null)
   are the base cases; a [select]/[?:] is adaptive when both its arms are (its
   result type is its arms'), and likewise an [if]/[do]-block through its
   tail(s). It is the criterion behind [restore_inner] (below): only an adaptive
   operand collapses a cross-hierarchy [extern.convert_any]/[any.convert_extern]
   into a plain [ref.null] when its inner any/extern cast is dropped, so only for
   it must the inner cast be re-grounded. An anchored operand (a concrete
   reference value) fixes the convert regardless; re-grounding it would be inert
   but noisy, so it is excluded. A [Cast] node never reaches here (the caller
   guards on the inner having been dropped, so the operand is no longer a cast).
   Extensible: further adaptive tails (a [Let] body's tail, a labelled block)
   could be added if a sweep surfaces them. *)
let rec reparse_adaptive (i : _ instr) =
  match i.desc with
  | Null | Hole -> true
  | Select (_, a, b) -> reparse_adaptive a && reparse_adaptive b
  (* A block ([do]/[if]) coming from [From_wasm] carries an explicit result type,
     which pins it, so it never re-parses adaptively and needs no case here. *)
  | _ -> false

let valtype_equal ctx (a : inferred_valtype) (b : inferred_valtype) =
  Wax_wasm.Types.val_subtype (subtyping_info ctx) a.internal b.internal
  && Wax_wasm.Types.val_subtype (subtyping_info ctx) b.internal a.internal

(* Bidirectional checking helpers (see [check_instruction] below).

   The keep-bool for a non-construction value: the contextual annotation is
   load-bearing unless the value's own standalone-resolved type ([standalone],
   captured BEFORE [check_type] mutates the cell) already equals it. This
   mirrors exactly the drop test [bind_let_value]/globals applied via
   [standalone_valtype], so routing those sites through [check_instruction] preserves their
   behaviour — e.g. [let x: i32 = 1] still drops to [let x = 1] (a floating
   number resolves to [i32]), while [let x: i64 = 1] keeps its annotation.

   [drop_supertype] loosens the test for an immutable binding (a [const] global):
   there the annotation is no more than a supertype of the value's own type, so
   dropping it narrows the binding to that subtype — sound because nothing
   reassigns it, and a narrower immutable global still satisfies every use (and
   every import) expecting the wider type. The standalone value must therefore
   only be a *subtype* of the annotation, not equal to it.

   The one exception: a *bottom* reference ([&?none] and friends), the standalone
   type of a bare [null]. Narrowing an annotation down to it is not a useful
   subtype — it drops all type information and changes the emitted [ref.null $t]
   to [ref.null none] — so a [null] whose annotation is a strict supertype keeps
   it regardless of [drop_supertype], matching the documented "a null initializer
   keeps its annotation" rule. Equality still drops ([const g: &?none = null]). *)
let annotation_needed ?(drop_supertype = false) ctx
    (standalone : inferred_valtype option) expected =
  let is_bottom_ref (v : inferred_valtype) =
    match v.typ with
    | Ref { typ = None_ | NoFunc | NoExtern | NoExn | NoCont; _ } -> true
    | _ -> false
  in
  match (standalone, Cell.get expected) with
  | Some v, Valtype b ->
      if drop_supertype && not (is_bottom_ref v) then
        not
          (Wax_wasm.Types.val_subtype (subtyping_info ctx) v.internal b.internal)
      else not (valtype_equal ctx v b)
  | _ -> true

(* Whether [expected] carries a real type expectation (vs. the [Unknown]
   sentinel used when [check_instruction] is entered from synthesis with no context).
   [subtype] asserts on an [Unknown] right-hand side, so callers guard with
   this before checking against [expected]. *)
let has_expectation expected =
  match Cell.get expected with Unknown | Collecting _ -> false | _ -> true

(* For a block-like construct (do/loop/try/try_table) checked against [expected]:
   the single cell to type its body and handlers against — its declared result,
   or [expected] when the annotation was omitted (a re-parse of a dropped one). *)
let context_result_cell ctx typ ~expected =
  if typ.results = [||] then expected
  else
    match array_map_opt (internalize ctx) typ.results with
    | Some [| c |] -> c
    | _ -> expected

(* Whether a block's declared result type equals the type its context already
   pins, so re-parsing recovers it from that context and the annotation can be
   dropped. Shared by [context_block_typ] (the [simplify] rewrite) and the
   quick-fix suggestion. *)
let block_result_redundant ctx typ ~expected ~result_cell =
  typ.results <> [||]
  &&
  match
    (standalone_valtype ctx expected, standalone_valtype ctx result_cell)
  with
  | Some a, Some b -> valtype_equal ctx a b
  | _ -> false

(* The exact user heap-type name [expected] pins, if any — usable to supply an
   omitted struct/array type name. A supertype top ([any]/[eq]/[struct]/[array]/
   …) or a floating/non-ref cell returns [None]: construction needs the exact
   type, never a supertype. *)
let exact_named_type expected =
  match Cell.get expected with
  | Valtype { typ = Ref { typ = Type ident | Exact ident; _ }; _ } -> Some ident
  | _ -> None

(* The user type name a heap type refers to ([Type]/[Exact]), or [None] for an
   abstract/bottom heap type. *)
let named_heaptype (t : heaptype) =
  match t with Type ident | Exact ident -> Some ident | _ -> None

(* A value type is defaultable unless it is a non-nullable reference: such a
   local has no zero value and must be assigned before use. *)
let is_defaultable (ty : valtype) =
  match ty with Ref { nullable; _ } -> nullable | _ -> true

let mark_initialized ctx name =
  ctx.initialized_locals <- StringSet.add name ctx.initialized_locals

(* Report a read of the not-yet-initialized local [idx], or — while a trailing
   operand is being typed out of emission order — defer it into the innermost
   active collector, to be re-checked at that operand's emission slot (see
   [type_trailing_operand]). Both the [Get] arm and a deferred read's re-check go
   through here, so a re-check that still fails under an outer deferral re-defers
   rather than reports. *)
let report_uninitialized ctx idx =
  match ctx.deferred_uninit with
  | collector :: _ -> collector := idx :: !collector
  | [] -> Error.uninitialized_local ctx.diagnostics ~location:idx.info idx

(* Type-check one [let] binding against [result_ty] — the value it takes off the
   stack — and record the local. Returns the binding to emit: an annotation that
   [simplify] finds redundant (it equals what the value would infer to on its
   own) is dropped, so Wax printed back from Wasm omits it. Used for both the
   single-value form and each name of a multi-value [let]. *)
let bind_let_value ctx ~location result_ty (name, typ) =
  match typ with
  | Some typ ->
      (* The type the value would take on its own, captured before
         [check_subtype] constrains it. *)
      let standalone = standalone_valtype ctx result_ty in
      (* Whether the annotation equals what the value would infer on its own, so
         it is redundant. Returned to the caller so it can offer a quick fix; the
         binding itself is dropped only under [simplify]. *)
      let redundant =
        Option.value ~default:false
          (let+@ ity = internalize_valtype ctx typ in
           check_subtype ctx ~location result_ty (valtype_cell ity);
           Option.iter
             (fun name ->
               ctx.locals <-
                 StringMap.add name.Annot.desc (Some ity, name.info) ctx.locals;
               ctx.local_decls := name :: !(ctx.local_decls);
               mark_initialized ctx name.desc)
             name;
           Option.fold ~none:false
             ~some:(fun v -> valtype_equal ctx v ity)
             standalone)
      in
      ((name, if ctx.simplify && redundant then None else Some typ), redundant)
  | None ->
      Option.iter
        (fun name ->
          (* The local takes its initializer's type; an [Unknown]/[Error]
             initializer has no determinable one, so the local is recorded as
             poison ([None]) rather than defaulting to [i32], and an [Unknown]
             initializer is additionally reported (see [bound_value_type]). *)
          let ity = bound_value_type ctx ~location result_ty in
          ctx.locals <-
            StringMap.add name.Annot.desc (ity, name.info) ctx.locals;
          ctx.local_decls := name :: !(ctx.local_decls);
          mark_initialized ctx name.desc)
        name;
      ((name, None), false)

(* When converting from Wasm, an expression producing several values (typically
   a call) is emitted as a bare statement, and the values it leaves on the stack
   are peeled off by a following run of [let x = _] declarations (and [_ = _]
   drops for results that are discarded). [merge_let_tuple] folds that run back
   into a single multi-binding [let (..) = expr] — the exact inverse of how such
   a [let] lowers, so the rewrite preserves semantics.

   The run consumed is exactly [head]'s result arity, read from the typed info,
   so we never absorb a [let x = _] that draws from a value sitting below
   [head]. Each bound name takes one value left to right, whereas the lowering
   stores the topmost value first, so the bindings are the run in reverse. Only
   done while simplifying, i.e. on the Wasm-to-Wax path. *)
let merge_let_tuple ctx head rest =
  let is_hole i = match i.desc with Hole -> true | _ -> false in
  let arity = Array.length (fst head.info) in
  let rec take n acc l =
    if n = 0 then Some (List.rev acc, l)
    else
      match l with
      (* A named binding [let x = _] or an anonymous drop [_ = _] (both a
         single-binding [Let] over a hole): peel one value each. *)
      | { desc = Let ([ b ], Some v); _ } :: r when is_hole v ->
          take (n - 1) (b :: acc) r
      | _ -> None
  in
  if (not ctx.simplify) || arity < 2 then head :: rest
  else
    match take arity [] rest with
    | Some (bindings, rest')
      when List.exists (fun (name, _) -> Option.is_some name) bindings ->
        let info = ([||], snd head.info) in
        (* The [let] is a statement: it produces no value, so it carries no
           [expected] type of its own (the bound [head] keeps its). *)
        {
          desc = Let (List.rev bindings, Some head);
          info;
          hints = head.hints;
          expected = Unset;
        }
        :: rest'
    | _ -> head :: rest

(* Check a list of typed operands against an array of expected types. *)
let check_operands ctx ~location l expected =
  if Array.length expected = List.length l then
    List.iter2 (fun i ty -> check_type ctx i ty) l (Array.to_list expected)
  else
    (* With the type immediates inferred from the receiver, a wrong operand
       count is no longer caught as an immediate/operand mismatch; report it
       as an arity error. *)
    Error.operand_count_mismatch ctx.diagnostics ~location
      ~expected:(Array.length expected) ~provided:(List.length l)

(* A missing else branch behaves like an empty one: it leaves the block
   parameters on the stack, so it is valid only when those already match the
   results (in particular, an if that produces a value needs an explicit else). *)
let missing_else_ok ctx params results =
  Array.length params = Array.length results
  && Array.for_all2 (fun p r -> subtype ctx p r) params results

(* The function type wrapped by a continuation type, given its (canonical) heap
   type. Mirrors [Validation.cont_functype_of_heaptype]. *)
let cont_functype ctx (h : Internal.heaptype) : Internal.functype option =
  match h with
  | Type ty | Exact ty -> (
      match (Wax_wasm.Types.get_subtype (subtyping_info ctx) ty).typ with
      | Cont ft -> (
          match (Wax_wasm.Types.get_subtype (subtyping_info ctx) ft).typ with
          | Func f -> Some f
          | Struct _ | Array _ | Cont _ -> None)
      | Func _ | Struct _ | Array _ -> None)
  | _ -> None

(* [ft] matches [ft'] when their arities agree and [ft']'s parameters /
   [ft]'s results are respectively subtypes. Mirrors [Validation.functype_matches]. *)
let functype_matches info (ft : Internal.functype) (ft' : Internal.functype) =
  Array.length ft.params = Array.length ft'.params
  && Array.length ft.results = Array.length ft'.results
  && Array.for_all Fun.id
       (Array.mapi
          (fun i p -> Wax_wasm.Types.val_subtype info ft'.params.(i) p)
          ft.params)
  && Array.for_all Fun.id
       (Array.mapi
          (fun i r -> Wax_wasm.Types.val_subtype info r ft'.results.(i))
          ft.results)

(* A source function type with its parameter and result types resolved to their
   canonical (Binary) form, for structural comparison with [functype_matches]. *)
let internal_functype ctx (ft : functype) : Internal.functype option =
  let*@ params =
    array_map_opt
      (fun p ->
        let+@ iv = internalize_valtype ctx (param_type p) in
        iv.internal)
      ft.params
  in
  let+@ results =
    array_map_opt
      (fun t ->
        let+@ iv = internalize_valtype ctx t in
        iv.internal)
      ft.results
  in
  ({ params; results } : Internal.functype)

(* Validate a [resume]/[resume_throw] handler table. [result_types] is the
   result type of the resumed continuation. Mirrors
   [Validation.check_resume_table]. *)
let check_resume_handlers ctx ~result_types handlers =
  let info = subtyping_info ctx in
  (* A block whose result is being inferred presents its label as a [Collecting]
     cell. The handler reads the label's type to validate the contract, which the
     join cannot re-derive, so resolve to the declared annotation under test and
     mark it needed (kept). *)
  let rec internal_of_inferred ty =
    match Cell.get ty with
    | Valtype { internal; _ } -> Some internal
    | Collecting { declared = Some d; _ } -> internal_of_inferred d
    | _ -> None
  in
  let to_internal arr =
    array_map_opt
      (fun typ ->
        let+@ iv = internalize_valtype ctx typ in
        iv.internal)
      arr
  in
  List.iter
    (fun handler ->
      match handler with
      | OnLabel (tag, label) -> (
          match Tbl.find ctx.diagnostics ctx.tags tag with
          | None -> ignore (branch_target ctx label)
          | Some { params = ts3; results = ts4 } ->
              let ts' = branch_target ctx label in
              let mismatch () =
                Error.stack_switching_type_mismatch ctx.diagnostics
                  ~location:label.info
                  ~descr:
                    "this handler must take the tag's parameters followed by a \
                     continuation of the remaining result type"
              in
              (* When the label is unbound, [branch_target] has already reported
                 it and returned [[||]]; skip the contract check so the same
                 label is not flagged a second time (as the unknown-tag arm
                 above skips it). *)
              if not (label_in_scope ctx label) then ()
              else begin
                (* The handler label receives the tag's parameters followed by a
                   continuation of type [cont (ts4 -> result_types)]. *)
                let n = Array.length ts' in
                if n <> Array.length ts3 + 1 then mismatch ()
                else begin
                  (* The continuation slot may be a block result still being
                   inferred (the Wasm->Wax [simplify] pass), presented as a
                   [Collecting] cell. Reading it to validate the contract is a use
                   the join cannot re-derive, so mark its annotation needed (kept);
                   [internal_of_inferred] resolves the cell to that declared type
                   below. Only this last slot can be under inference: a block being
                   inferred has a single result, so a handler with tag parameters
                   (n > 1) is never inferred and its slots are concrete. A cell
                   inferring with no declared annotation resolves to [None] below
                   and so fails the contract check, as it must. *)
                  (match Cell.get ts'.(n - 1) with
                  | Collecting cs -> cs.needed <- true
                  | _ -> ());
                  Array.iteri
                    (fun i p ->
                      let t = param_type p in
                      match
                        (internalize_valtype ctx t, internal_of_inferred ts'.(i))
                      with
                      | Some it, Some it' ->
                          if
                            not
                              (Wax_wasm.Types.val_subtype info it.internal it')
                          then mismatch ()
                      | _ -> ())
                    ts3;
                  match internal_of_inferred ts'.(n - 1) with
                  | Some (Ref { typ = ht; _ }) -> (
                      match cont_functype ctx ht with
                      | Some ft' -> (
                          match (to_internal ts4, to_internal result_types) with
                          | Some params, Some results ->
                              if
                                not
                                  (functype_matches info { params; results } ft')
                              then mismatch ()
                          | _ -> ())
                      | None -> mismatch ())
                  | _ -> mismatch ()
                end
              end)
      | OnSwitch tag -> (
          match Tbl.find ctx.diagnostics ctx.tags tag with
          | None -> ()
          | Some { params = ts3; results = ts4 } -> (
              let mismatch descr =
                Error.stack_switching_type_mismatch ctx.diagnostics
                  ~location:tag.info ~descr
              in
              (* A switch handler tag has type [] -> [t*]. The reified current
                 continuation ([cont [t2*] -> [t*]]) runs to this [resume]
                 boundary, whose results are [result_types], so [t*] must
                 *equal* those results (equivalence, not merely subtyping): a
                 subtype would let a continuation whose completion produces the
                 boundary results be observed by a peer at the narrower tag type.
                 Mirrors [Validation]'s [result_equivalent] check; the older
                 written subtyping rule is unsound. *)
              if Array.length ts3 <> 0 then
                mismatch "the tag of a 'switch' handler must take no parameters"
              else
                match (to_internal ts4, to_internal result_types) with
                | Some tr, Some cr ->
                    if
                      Array.length tr <> Array.length cr
                      || not
                           (Array.for_all2
                              (fun a b ->
                                Wax_wasm.Types.val_subtype info a b
                                && Wax_wasm.Types.val_subtype info b a)
                              tr cr)
                    then
                      mismatch
                        "the results of a 'switch' handler's tag must match \
                         the resumed continuation's results"
                | _ -> ())))
    handlers

(* Whether the receiver of a scalar-intrinsic-method call [recv.min(..)] names a
   reference (e.g. a struct) rather than a numeric value. Decided purely, by
   looking the name up in the locals / globals — no typing, so the dispatch can
   gate on it without recording a spurious use. A reference receiver means
   [recv.min] loads a function-pointer field (an indirect call), not the scalar
   [min] intrinsic; only a numeric receiver reaches [type_binary_intrinsic_call].
   A non-name receiver (a literal, a nested expression) is not a reference. *)
let receiver_is_ref ctx recv =
  let is_ref = function
    | Some ({ typ = Ref _; _ } : inferred_valtype) -> true
    | _ -> false
  in
  match recv.Ast.desc with
  | Get name -> (
      match StringMap.find_opt name.desc ctx.locals with
      | Some (ity, _) -> is_ref ity
      | None -> (
          match Tbl.entries ctx.globals name with
          | (_, (_, ity)) :: _ -> is_ref ity
          | [] -> false))
  | _ -> false

(* Whether the receiver of an array-op method call ([a.fill(..)]) names a value
   whose type is a reference to an array type. Pure, like {!receiver_is_ref}: it
   reads the name's type from the locals / globals and the referenced type's
   definition from the type table, recording nothing. Gates the recovery of a
   wrong-arity array op (an [a.fill()] being typed) so a struct with a field
   named [fill]/[copy]/[init] is left to the indirect-call path instead. *)
let receiver_is_array_ref ctx recv =
  let ref_name = function
    | Some ({ typ = Ref { typ = Type n | Exact n; _ }; _ } : inferred_valtype)
      ->
        Some n
    | _ -> None
  in
  let arrname =
    match recv.Ast.desc with
    | Get name -> (
        match StringMap.find_opt name.desc ctx.locals with
        | Some (ity, _) -> ref_name ity
        | None -> (
            match Tbl.entries ctx.globals name with
            | (_, (_, ity)) :: _ -> ref_name ity
            | [] -> None))
    | _ -> None
  in
  match arrname with
  | None -> false
  | Some n -> (
      match Tbl.entries ctx.type_context.types n with
      | (_, (_, sub)) :: _ -> (
          match sub.typ with Array _ -> true | _ -> false)
      | [] -> false)

(* A cast is transparent to the hole-order check exactly when [to_wasm] lowers it
   to no instruction (so it occupies its operand's position and produces nothing):
   an operand with no value type — unreachable / failed code, where the cast emits
   nothing — or a numeric-scalar identity, the only [Nop] case in [to_wasm]'s cast
   lowering. Everything else IS emitted: a numeric conversion ([_ as f32] on an
   [f64] hole is [f32.demote_f64]) or a reference cast (always a [ref.cast], even
   an up-cast), and operates on the stack top, so it must be ordered like any
   other value-producing expression. *)
let cast_is_transparent ctx ~cast ~operand =
  match Cell.get (expression_type ctx operand) with
  | Unknown | Error -> true
  | Valtype { internal = (I32 | I64 | F32 | F64) as src; _ } -> (
      match Cell.get (expression_type ctx cast) with
      | Valtype { internal = dst; _ } -> src = dst
      | _ -> false)
  | _ -> false

(* The threaded state of the expression typer's monad ([return]/[let*]):
   [pending] holds the stack values a [Hole] may consume, handed to each
   subexpression as an exact slice at every distribution point (see [with_slice]),
   so consumption no longer depends on the textual order the children are typed
   in — a sibling that errors, recovers or is typed out of order (a [StructDesc]
   descriptor, a call callee — see [type_trailing_operand]) cannot desynchronise
   the rest. [value_loc]
   and [reported] fold in the hole-order check: [value_loc] is the source location
   of the first value-producing operand emitted in the current distribution, so
   reaching a hole-bearing operand after it means a hole occurs after a value on
   the stack (unencodable) — reported at that value, with [reported] guarding a
   duplicate. *)
type 'a hole_st = {
  pending : 'a list;
  value_loc : location option;
  reported : bool;
}

(* Split [l] after [n] elements, tolerating [n] past the end. *)
let rec list_split n l =
  if n <= 0 then ([], l)
  else
    match l with
    | [] -> ([], [])
    | x :: r ->
        let a, b = list_split (n - 1) r in
        (x :: a, b)

(* Whether an operand pushes a value onto the stack (so a following hole would
   consume it rather than the intended pending value). A [Hole] pushes nothing (it
   names an already-present pending value); a transparent cast (see
   [cast_is_transparent]) lowers to no instruction, so it pushes exactly what its
   operand does; every other operand emits at least one value-producing
   instruction. Static receivers (memory/table/segment names, a [tab[..]] table)
   are immediates, not operands, and never reach here. *)
let rec emits_value ctx (node : _ Ast.instr) =
  match node.desc with
  | Hole -> false
  | Cast (inner, _) when cast_is_transparent ctx ~cast:node ~operand:inner ->
      emits_value ctx inner
  | _ -> true

(* Consume the pending value a [Hole] stands for. Per-subexpression slicing
   ([with_slice]) hands each hole its own slot, so an empty [pending] here is a
   recovery-only path: a hole-bearing sibling was skipped or an operand
   underflowed (already reported). Recover with an [Error] value rather than the
   former [assert false] (exit 125). *)
let pop_parameter st =
  match st.pending with
  | x :: r -> ({ st with pending = r }, x)
  | [] -> (st, Cell.make Error)

(* Report the underflow behind the value a hole just consumed, if it was one of
   the placeholders [pop_any] recorded: the report points at the hole itself,
   the most precise anchor for a missing value. One report per underflow — the
   batch is marked, and [with_holes] falls back to the whole expression only
   when the placeholder never reached a hole (a recovery path). *)
let report_missing_hole ctx ~location ty =
  match List.find_opt (fun (cell, _) -> cell == ty) !(ctx.missing_holes) with
  | Some (_, batch) ->
      ctx.missing_holes :=
        List.filter (fun (cell, _) -> cell != ty) !(ctx.missing_holes);
      if not batch.hole_reported then begin
        batch.hole_reported <- true;
        Error.short_stack ctx.diagnostics `Holes ~location
          ~actual:batch.hole_actual ~expected:batch.hole_expected
      end
  | None -> ()

let _print_arg_stack l =
  Wax_utils.Printer.run_err (fun p ->
      let pp =
        Wax_utils.Styled_printer.create ~printer:p
          ~theme:Wax_utils.Colors.no_color
          ~trivia:(Wax_utils.Trivia.empty ())
          ()
      in
      List.iteri
        (fun i ty ->
          if i > 0 then Wax_utils.Printer.space p ();
          output_inferred_type_styled pp ty)
        l)

(* Peel the condition / reference operand off the last slot of a branch
   instruction's operand types, returning it together with the remaining branch
   parameters. The operand is an arbitrary expression, which may type to no
   value at all (e.g. a call to a function with no results); rather than assert,
   report the missing operand and recover with an unknown value. *)
let split_on_last_type ctx ~location i =
  let a = fst i.info in
  let len = Array.length a in
  if len = 0 then (
    Error.operand_count_mismatch ctx.diagnostics ~location ~expected:1
      ~provided:0;
    (Cell.make Error, [||]))
  else (a.(len - 1), Array.sub a 0 (len - 1))

let immediate_supertype s : Ast.heaptype =
  match (s.supertype, s.typ) with
  | Some t, _ -> Type t
  | None, Struct _ -> Struct
  | None, Array _ -> Array
  | None, Func _ -> Func
  | None, Cont _ -> Cont

(* The top of [h]'s subtyping hierarchy ([Any]/[Func]/[Extern]/[Exn]/[Cont]),
   without reporting an unbound type ([None] then). *)
let heaptype_top ctx (h : Ast.heaptype) : Ast.heaptype option =
  match h with
  | Any | Eq | I31 | Struct | Array | None_ -> Some Any
  | Func | NoFunc -> Some Func
  | Extern | NoExtern -> Some Extern
  | Exn | NoExn -> Some Exn
  | Cont | NoCont -> Some Cont
  | Type id | Exact id -> (
      match Tbl.find_opt ctx.type_context.types id with
      | Some (_, s) -> (
          match s.typ with
          | Struct _ | Array _ -> Some Any
          | Func _ -> Some Func
          | Cont _ -> Some Cont)
      | None -> None)

(* A bottom reference of a hierarchy. *)
let is_bottom_heaptype = function
  | None_ | NoFunc | NoExtern | NoExn | NoCont -> true
  | _ -> false

(* The [typ] to store for a do/loop/try/try_table block after its body is typed:
   fill an omitted result from [expected] (so re-parse / [to_wasm] recovers it),
   or drop a declared result on [simplify] when it equals the context — then
   re-parse recovers the same type from the same context, so nothing is lost.
   Under [ctx.suggest] the same redundant result type is offered as an editor
   quick fix (see [suggest_block_result]). Both the [simplify] drop and the
   suggestion key on [block_result_redundant], so they cannot drift.
   [keyword]/[block_start]/[brace_start] locate the '<keyword> t {' the source
   scan trims the type from. *)
let context_block_typ ctx ~keyword (block_start : Lexing.position)
    (brace_start : Lexing.position) typ ~expected ~result_cell =
  let redundant = block_result_redundant ctx typ ~expected ~result_cell in
  if ctx.suggest && redundant then
    Typing_suggest.suggest_block_result ctx ~keyword block_start brace_start;
  if typ.results = [||] then
    match standalone_valtype ctx expected with
    | Some iv -> { typ with results = [| iv.typ |] }
    | None -> typ
  else if ctx.simplify && redundant then { typ with results = [||] }
  else typ

(* Lint a reference cast ([is_test = false]) or test ([is_test = true]) given the
   operand's inferred type and the interned target type. Under single-inheritance
   subtyping two heap types share a value only when one is a subtype of the
   other, so unrelated types make the cast always trap / the test always false
   (unless a shared [null] slips through); an operand that already has the target
   type makes it redundant. A bottom-reference operand's CAST is skipped: it is
   load-bearing (dropping it loses the type the value stands in for). A TEST
   deletes nothing, so a bottom operand is linted like any other — mirroring the
   Wasm validator's [lint_cast], which has no bottom exclusion.

   [operand_location] is the source span of the cast's operand, used (under
   [ctx.suggest]) to offer a quick fix that removes a redundant cast by deleting
   the ' as t' suffix running from the operand's end to the cast's end. *)
let lint_ref_cast ?operand_location ctx ~location ~is_test op_natural
    target_natural =
  let info = subtyping_info ctx in
  (* Report the INNERMOST always-trapping cast of a chain only: a cast or test
     over a value that can never be produced is unreachable, and whatever it says
     about that value merely follows from the inner verdict — the fix belongs at
     the inner cast (see [cast_traps_reported]). The span is recorded whether or
     not the report came out, so a longer chain stays quiet past its second cast.
     Only the always-trapping verdict is chained: a REDUNDANT outer cast is an
     independent claim about the cast itself (its target is the type the operand
     already has, whatever that operand does at run time) with its own fix, and
     the Wasm validator's [lint_cast] reports it on the lowered form — a source
     chain lowers to one [ref.cast] per cast, so suppressing it here left the wat
     form of [g as &t as &t] linted and the wax form silent. *)
  let span_key (l : Ast.location) =
    (l.loc_start.Lexing.pos_cnum, l.loc_end.Lexing.pos_cnum)
  in
  let operand_traps =
    match operand_location with
    | Some ol -> Hashtbl.mem ctx.cast_traps_reported (span_key ol)
    | None -> false
  in
  if operand_traps then
    Hashtbl.replace ctx.cast_traps_reported (span_key location) ();
  let cast_always_fails () =
    Hashtbl.replace ctx.cast_traps_reported (span_key location) ();
    if not operand_traps then
      Error.cast_always_fails ctx.diagnostics ~location ~is_test
  in
  let redundant_cast ?edit () =
    Error.redundant_cast ?edit ctx.diagnostics ~location ~is_test
  in
  match (op_natural, target_natural) with
  | ( Valtype { typ = Ref { typ = op_src; _ }; internal = Ref op; _ },
      Valtype { internal = Ref tgt; _ } )
    when is_test || not (is_bottom_heaptype op_src) ->
      (* [any] <-> [extern] across hierarchies is the lossless
         [extern.convert_any] / [any.convert_extern] conversion (the surface
         spells it [as &extern] / [as &any]), not a [ref.cast]: it never traps
         and, since it changes hierarchy, is never redundant. Don't lint it —
         reporting it as an always-trapping (or redundant) cast is a false
         positive. *)
      let bridged =
        let open Wax_wasm.Types in
        let in_hier h top = heap_subtype info h top in
        (in_hier op.typ Internal.Any && in_hier tgt.typ Internal.Extern)
        || (in_hier op.typ Internal.Extern && in_hier tgt.typ Internal.Any)
      in
      let related =
        Wax_wasm.Types.heap_subtype info op.typ tgt.typ
        || Wax_wasm.Types.heap_subtype info tgt.typ op.typ
      in
      if bridged then ()
      else if (not related) && not (op.nullable && tgt.nullable) then
        cast_always_fails ()
      else if Wax_wasm.Types.ref_subtype info op tgt then
        let edit =
          match operand_location with
          | Some (ol : Ast.location) when ctx.suggest && not is_test ->
              Some (deletion_edit (span ol.loc_end location.loc_end))
          | _ -> None
        in
        redundant_cast ?edit ()
  | ( Valtype { typ = Ref { typ = op_src; _ }; internal = Ref op; _ },
      Valtype { internal = I32 | I64; _ } )
    when (not is_test)
         && (not (is_bottom_heaptype op_src))
         && Wax_wasm.Types.heap_subtype info op.typ Internal.Any
         && not
              (Wax_wasm.Types.heap_subtype info op.typ Internal.I31
              || Wax_wasm.Types.heap_subtype info Internal.I31 op.typ) ->
      (* [ref as iN_s/u] extracts an i31 payload: it lowers to a [ref.cast (ref
         i31)] then an [i31.get] (see [To_wasm.default_cast]). An [any]-hierarchy
         reference that can never be an [i31] — a [struct]/[array], not
         [any]/[eq]/[i31] — makes that [ref.cast] always trap, exactly as the
         Wasm validator reports on the lowered form. *)
      cast_always_fails ()
  | _ -> ()

(* The type lookups below never fail *)
let rec heap_lub ctx (h1 : Ast.heaptype) (h2 : Ast.heaptype) =
  match (h1, h2) with
  (* A bottom reference is below everything in its hierarchy, so its lub with any
     type of that same hierarchy is that other type. Handle this before walking a
     concrete [Type] up to its supertype, which would otherwise discard the
     bottom and over-generalise (e.g. [lub(none, $t)] giving [struct] not [$t]). *)
  | b, h when is_bottom_heaptype b && heaptype_top ctx b = heaptype_top ctx h ->
      Some h
  | h, b when is_bottom_heaptype b && heaptype_top ctx b = heaptype_top ctx h ->
      Some h
  (* [exact] survives a lub only when both sides are the same exact type; any
     generalization drops exactness (an [exact a]/[exact b] pair joins at their
     common non-exact supertype). *)
  | Exact id1, Exact id2 ->
      let*@ i1, _ = Tbl.find_opt ctx.type_context.types id1 in
      let*@ i2, _ = Tbl.find_opt ctx.type_context.types id2 in
      if i1 = i2 then Some (Exact id1) else heap_lub ctx (Type id1) (Type id2)
  | Exact id1, h -> heap_lub ctx (Type id1) h
  | h, Exact id2 -> heap_lub ctx h (Type id2)
  | Type id1, Type id2 ->
      let*@ i1, s1 = Tbl.find_opt ctx.type_context.types id1 in
      let*@ i2, s2 = Tbl.find_opt ctx.type_context.types id2 in
      if i1 > i2 then heap_lub ctx (immediate_supertype s1) h2
      else if i2 > i1 then heap_lub ctx h1 (immediate_supertype s2)
      else Some h1
  | Type id1, _ ->
      let*@ _, s1 = Tbl.find_opt ctx.type_context.types id1 in
      heap_lub ctx (immediate_supertype s1) h2
  | _, Type id2 ->
      let*@ _, s2 = Tbl.find_opt ctx.type_context.types id2 in
      heap_lub ctx h1 (immediate_supertype s2)
      (* Abstract hierarchy *)
  | None_, None_ -> Some None_
  | (None_ | I31), I31 | I31, None_ -> Some I31
  | (None_ | Struct), Struct | Struct, None_ -> Some Struct
  | (None_ | Array), Array | Array, None_ -> Some Array
  | (None_ | I31 | Struct | Array | Eq), Eq
  | Eq, (None_ | I31 | Struct | Array)
  | (Struct | Array), I31
  | I31, (Struct | Array)
  | Struct, Array
  | Array, Struct ->
      Some Eq
  | (None_ | I31 | Struct | Array | Eq | Any), Any
  | Any, (None_ | Eq | I31 | Struct | Array) ->
      Some Any
  | NoFunc, NoFunc -> Some NoFunc
  | (NoFunc | Func), Func | Func, NoFunc -> Some Func
  | NoExtern, NoExtern -> Some NoExtern
  | (NoExtern | Extern), Extern | Extern, NoExtern -> Some Extern
  | NoExn, NoExn -> Some NoExn
  | (NoExn | Exn), Exn | Exn, NoExn -> Some Exn
  | NoCont, NoCont -> Some NoCont
  | (NoCont | Cont), Cont | Cont, NoCont -> Some Cont
  | ( (None_ | Eq | I31 | Struct | Array | Any),
      (NoExtern | Extern | NoExn | Exn | NoFunc | Func) )
  | ( (NoExtern | Extern | NoExn | Exn | NoFunc | Func),
      (None_ | Eq | I31 | Struct | Array | Any) )
  | (NoFunc | Func), (NoExtern | Extern | NoExn | Exn)
  | (NoExtern | Extern | NoExn | Exn), (NoFunc | Func)
  | (NoExtern | Extern), (NoExn | Exn)
  | (NoExn | Exn), (NoExtern | Extern)
  (* Continuation types form their own hierarchy, incompatible with all
     others (and have no Wax surface syntax). *)
  | (Cont | NoCont), _
  | _, (Cont | NoCont) ->
      None

let val_lub ctx v1 v2 =
  match (v1, v2) with
  | Ref r1, Ref r2 ->
      let+@ lub = heap_lub ctx r1.typ r2.typ in
      let nullable = r1.nullable || r2.nullable in
      Ref { nullable; typ = lub }
  | _ -> if v1 = v2 then Some v1 else None

(* The least upper bound of two value type cells, or [None] when they have no
   common type. Mirrors the [Select] (?:) reconciliation: it pins an
   as-yet-unconstrained literal/[null] to the other side and lubs two reference
   types via [val_lub]. Used to combine the values reaching a block's exit (the
   branches of an [if], etc.) when inferring the block's result type. *)
let join_value_types ctx ty1 ty2 =
  match (Cell.get ty1, Cell.get ty2) with
  (* [Unknown]/[Error] are the universal bottom: the other side wins (the lub of
     [Unknown] and [UnknownRef] is the more informative [UnknownRef]). [UnknownRef]
     (a bottom reference) joins with any other reference — concrete, [Null] or
     another [UnknownRef] — which, being a supertype, wins; a bottom reference
     paired with a non-reference (e.g. [i32]) has no common type and falls
     through to a mismatch. *)
  (* An [Unknown] value reaching a block's exit (a hole on the polymorphic stack of
     dead code) genuinely takes the block's result type: pin it (merge), so a
     branch that also passes it through — a [br_if]/[br_on_null] whose value is then
     cast — sees the resolved width rather than staying [Unknown], which would make
     [To_wasm] drop the cast. [Error] (already reported) stays the untouched bottom. *)
  | _, Unknown ->
      Cell.merge ty1 ty2 (Cell.get ty1);
      Some ty1
  | Unknown, _ ->
      Cell.merge ty1 ty2 (Cell.get ty2);
      Some ty2
  | _, Error -> Some ty1
  | Error, _ -> Some ty2
  | UnknownRef, UnknownRef ->
      (* Merge the two bottom references so pinning one (later, against a concrete
         type) pins the other too. *)
      Cell.merge ty1 ty2 UnknownRef;
      Some ty1
  | (Valtype { internal = Ref _; _ } | Null), UnknownRef ->
      Cell.set ty2 (Cell.get ty1);
      Some ty1
  | UnknownRef, (Valtype { internal = Ref _; _ } | Null) ->
      Cell.set ty1 (Cell.get ty2);
      Some ty2
  | Null, Null ->
      (* Unify the two nulls so pinning one (later, to a reference type) pins the
         other too. *)
      Cell.merge ty1 ty2 Null;
      Some ty1
  | Valtype { internal = I32; _ }, Valtype { internal = I32; _ }
  | Valtype { internal = I64; _ }, Valtype { internal = I64; _ }
  | Valtype { internal = F32; _ }, Valtype { internal = F32; _ }
  | Valtype { internal = F64; _ }, Valtype { internal = F64; _ } ->
      Some ty2
  | (Int | Number), (Int | Valtype { internal = I32 | I64; _ })
  | (Float | Number), (Float | Valtype { internal = F32 | F64; _ })
  | Number, Number ->
      Cell.merge ty1 ty2 (Cell.get ty2);
      Some ty2
  | ( (Valtype { internal = I32; _ } | Valtype { internal = I64; _ }),
      (Int | Number) )
  | ( (Valtype { internal = F32; _ } | Valtype { internal = F64; _ }),
      (Float | Number) )
  | (Int | Float), Number ->
      Cell.merge ty1 ty2 (Cell.get ty1);
      Some ty1
  (* A [LargeInt] (literal too big for i32) defaults to i64 and is also
     convertible to a float. It joins with another [LargeInt] or a fully-flexible
     [Number] staying [LargeInt] (i64/f32/f64), or with a concrete i64/f32/f64 or a
     flexible float taking that type, but never with i32. A committed [Int], being
     integer-only, has i64 as its sole common type with a [LargeInt] — pin it
     there, so the join cannot later be coerced to a float the [Int] cannot be.
     Mirrors [check_int_bin_op]/[check_num_concrete]. *)
  | LargeInt, Int | Int, LargeInt ->
      Cell.merge ty1 ty2 (Valtype i64_valtype);
      Some ty1
  | LargeInt, (LargeInt | Number) ->
      Cell.merge ty1 ty2 LargeInt;
      Some ty1
  | Number, LargeInt ->
      Cell.merge ty1 ty2 LargeInt;
      Some ty2
  | LargeInt, (Float | Valtype { internal = I64 | F32 | F64; _ }) ->
      Cell.merge ty1 ty2 (Cell.get ty2);
      Some ty2
  | (Float | Valtype { internal = I64 | F32 | F64; _ }), LargeInt ->
      Cell.merge ty1 ty2 (Cell.get ty1);
      Some ty1
  | Valtype { typ = typ1; _ }, Valtype { typ = typ2; _ } -> (
      match val_lub ctx typ1 typ2 with
      | Some ty -> internalize ctx ty
      | None -> None)
  | Valtype { typ = Ref { typ; _ }; _ }, Null -> (
      match internalize ctx (Ref { typ; nullable = true }) with
      | Some ty ->
          Cell.set ty2 (Cell.get ty);
          Some ty
      | None -> None)
  | Null, Valtype { typ = Ref { typ; _ }; _ } -> (
      match internalize ctx (Ref { typ; nullable = true }) with
      | Some ty ->
          Cell.set ty1 (Cell.get ty);
          Some ty
      | None -> None)
  | _ -> None

let address_valtype (at : [ `I32 | `I64 ]) : inferred_valtype =
  match at with `I32 -> i32_valtype | `I64 -> i64_valtype

let address_cell at = valtype_cell (address_valtype at)
let simd_cell t = valtype_cell (Members.simd_valtype t)

(* Build the {!R_cont} descriptor of a receiver of declared continuation type
   [ct], rendering the method signatures from the type context. *)
let cont_receiver ctx ct =
  let render (t : Ast.valtype) = Output.valtype_string t in
  let sign =
    let*@ inner = lookup_cont_inner ctx ct in
    lookup_func_type ctx inner
  in
  let params, results =
    match sign with
    | Some sg ->
        ( Array.to_list (Array.map (fun p -> render (param_type p)) sg.params),
          Array.to_list (Array.map render sg.results) )
    | None -> ([], [])
  in
  let switch_results =
    match
      let*@ sg = sign in
      let n = Array.length sg.params in
      if n = 0 then None
      else
        match snd sg.params.(n - 1).Ast.desc with
        | Ast.Ref { typ = Type ct2 | Exact ct2; _ } ->
            let*@ inner2 = lookup_cont_inner ctx ct2 in
            let*@ sg2 = lookup_func_type ctx inner2 in
            Some
              (Array.to_list
                 (Array.map (fun p -> render (param_type p)) sg2.params))
        | _ -> None
    with
    | Some rs -> rs
    | None -> []
  in
  Members.R_cont
    (Members.cont_method_candidates ~params ~results ~switch_results)

(* Memory access method names. The value width is in the name; signedness and the
   i32/i64 result come from a surrounding [as iN_s/u] cast (see [to_wasm]). *)
let mem_load_result meth : inferred_type option =
  match meth with
  | "load8" -> Some Int8
  | "load16" -> Some Int16
  | "load32" -> Some (Valtype i32_valtype)
  | "load64" -> Some (Valtype i64_valtype)
  | "loadf32" -> Some (Valtype f32_valtype)
  | "loadf64" -> Some (Valtype f64_valtype)
  | _ -> None

let mem_store_method meth =
  match meth with
  | "store8" | "store16" | "store32" | "store64" | "storef32" | "storef64" ->
      true
  | _ -> false

let is_mem_method meth = mem_load_result meth <> None || mem_store_method meth

(* Natural alignment (in bytes) of a scalar memory access. *)
let mem_natural_align meth =
  match meth with
  | "load8" | "store8" -> 1
  | "load16" | "store16" -> 2
  | "load32" | "store32" | "loadf32" | "storef32" -> 4
  | "load64" | "store64" | "loadf64" | "storef64" -> 8
  | _ -> 1

(* The unsigned 64-bit value of an integer literal, or [None] if it is not an
   integer literal or does not fit u64. Parsed quietly (a plain [of_string] would
   print "Unsigned int overflow" before raising on an out-of-range value). *)
let int_literal a =
  match a.Ast.desc with
  | Ast.Int s ->
      (if String.starts_with ~prefix:"0x" s then Int64.of_string_opt s
       else Int64.of_string_opt ("0u" ^ s))
      |> Option.map Wax_utils.Uint64.of_int64
  | _ -> None

let max_offset_i32_exclusive =
  Wax_utils.Uint64.of_string "0x1_0000_0000" (* 2^32 *)

let max_align = Wax_utils.Uint64.of_int 16

(* Validate the trailing [align]/[offset] literals of a memory access against
   the access's natural alignment (in bytes) and the address type. Mirrors
   [Validation.check_memarg]. [align] and [offset] are the corresponding
   argument expressions, when present. *)
let check_memarg ctx ~address_type ~natural ~align ~offset =
  (let>@ offset = offset in
   match int_literal offset with
   | None ->
       (* The literal does not fit u64, so it cannot be a memory offset. *)
       Error.memory_immediate_too_large ctx.diagnostics
         ~location:(snd offset.info)
   | Some o ->
       if
         address_type = `I32
         && Wax_utils.Uint64.compare o max_offset_i32_exclusive >= 0
       then
         Error.memory_offset_too_large ctx.diagnostics
           ~location:(snd offset.info) max_offset_i32_exclusive);
  let>@ align = align in
  match int_literal align with
  | None ->
      Error.memory_immediate_too_large ctx.diagnostics
        ~location:(snd align.info)
  | Some a -> (
      if
        Wax_utils.Uint64.compare a max_align > 0
        || Wax_utils.Uint64.to_int a > natural
      then
        Error.memory_align_too_large ctx.diagnostics ~location:(snd align.info)
          natural
      else
        match Wax_utils.Uint64.to_int a with
        | 1 | 2 | 4 | 8 | 16 -> ()
        | _ -> Error.bad_memory_align ctx.diagnostics ~location:(snd align.info)
      )

(* Split a memory-access call's (typed) argument list into the positional
   stack operands and the labelled immediates. A positional argument after a
   labelled one is reported and kept positional, for recovery. *)
let split_labelled_args ctx args =
  let rec split positional labelled = function
    | [] -> (List.rev positional, List.rev labelled)
    | a :: rest -> (
        match a.Ast.desc with
        | Ast.Labelled (l, e) -> split positional ((l, e) :: labelled) rest
        | _ ->
            if labelled <> [] then
              Error.positional_argument_after_label ctx.diagnostics
                ~location:(snd a.Ast.info);
            split (a :: positional) labelled rest)
  in
  split [] [] args

(* Check the labelled immediates of a memory access against the label names
   [allowed] for it — an unknown or duplicate label is reported, and the
   payload of an accepted label must be an integer literal — and return a
   by-name lookup of the payloads. *)
let take_labels ctx ~allowed labelled =
  let take (seen, acc) ((l : Ast.ident), e) =
    if not (List.mem l.desc allowed) then (
      Error.unknown_argument_label ctx.diagnostics ~location:l.info
        ~suggestions:
          (Wax_utils.Spell_check.f (fun f -> List.iter f allowed) l.desc)
        l;
      (seen, acc))
    else
      match List.assoc_opt l.desc seen with
      | Some prev_loc ->
          Error.duplicate_argument_label ctx.diagnostics ~location:l.info
            ~prev_loc l;
          (seen, acc)
      | None -> (
          match e.Ast.desc with
          | Ast.Int _ -> ((l.desc, l.info) :: seen, (l.desc, e) :: acc)
          | _ ->
              (* Report it and drop the pair, so [check_memarg] (which would
                 also fail to read it as a literal) does not report it
                 again. *)
              Error.integer_literal_required ctx.diagnostics
                ~location:(snd e.Ast.info);
              ((l.desc, l.info) :: seen, acc))
  in
  let _, acc = List.fold_left take ([], []) labelled in
  fun name -> List.assoc_opt name acc

(* The [lane]/[align]/[offset] immediates of a memory access with [nstack]
   stack operands, from the label lookup [find]. Extra positional arguments
   are the pre-labelled-arguments syntax when they are integer literals — the
   targeted migration error is reported and they still fill the immediates in
   the old positional order ([lane,] align, offset), so old code gets exactly
   one error and no cascade — and an ordinary arity error otherwise. *)
let mem_immediates ctx ~location ~example ~nstack ~has_lane find positional =
  let nargs = List.length positional in
  let extra = List.filteri (fun k _ -> k >= nstack) positional in
  let nimms = if has_lane then 3 else 2 in
  (* The extras are the pre-labelled positional-immediate syntax only when they
     are all integer literals and no more than the immediate count; otherwise
     they are an ordinary arity error and must not be read as immediates (else a
     non-literal extra, e.g. a local, cascades into a bogus memarg error). *)
  let migration =
    extra <> []
    && List.length extra <= nimms
    && List.for_all
         (fun a -> match a.Ast.desc with Ast.Int _ -> true | _ -> false)
         extra
  in
  (if nargs < nstack then
     Error.operand_count_mismatch ctx.diagnostics ~location ~expected:nstack
       ~provided:nargs
   else
     match extra with
     | [] -> ()
     | a :: _ ->
         if migration then
           Error.positional_memory_immediate ctx.diagnostics
             ~location:(snd a.Ast.info) ~example
         else
           Error.operand_count_mismatch ctx.diagnostics ~location
             ~expected:nstack ~provided:nargs);
  let pick name k =
    match find name with
    | Some e -> Some e
    | None -> if migration then List.nth_opt extra k else None
  in
  if has_lane then (pick "lane" 0, pick "align" 1, pick "offset" 2)
  else (None, pick "align" 0, pick "offset" 1)

(* [min(2^bits - 1, 2^(bits - p))]; mirrors [Validation.max_memory_size]. *)
let max_memory_size address_type page_size_log2 =
  let p = match page_size_log2 with None -> 16 | Some p -> p in
  let bits, index_max =
    match address_type with
    | `I32 -> (32, Wax_utils.Uint64.of_string "0xffff_ffff")
    | `I64 -> (64, Wax_utils.Uint64.of_string "0xffff_ffff_ffff_ffff")
  in
  let e = bits - p in
  let by_page =
    if e >= 64 then index_max
    else if e <= 0 then Wax_utils.Uint64.zero
    else Wax_utils.Uint64.of_int64 (Int64.shift_left 1L e)
  in
  if Wax_utils.Uint64.compare index_max by_page <= 0 then index_max else by_page

let max_table_size address_type _page_size_log2 =
  match address_type with
  | `I32 -> Wax_utils.Uint64.of_string "0xffff_ffff"
  | `I64 -> Wax_utils.Uint64.of_string "0xffff_ffff_ffff_ffff"

(* Validate a memory/table size limit and page size. Mirrors [Validation.limits]. *)
let check_limits ctx ~location kind ~shared address_type page_size_log2 limits
    max_fn =
  (match page_size_log2 with
  | None | Some (0 | 16) -> ()
  | Some _ -> Error.invalid_page_size ctx.diagnostics ~location);
  if shared && match limits with Some (_, Some _) -> false | _ -> true then
    Error.shared_memory_without_max ctx.diagnostics ~location;
  match limits with
  | None -> ()
  | Some (mi, ma) -> (
      let max = max_fn address_type page_size_log2 in
      match ma with
      | None ->
          if Wax_utils.Uint64.compare mi max > 0 then
            Error.limit_too_large ctx.diagnostics ~location kind max
      | Some ma ->
          if Wax_utils.Uint64.compare mi ma > 0 then
            Error.limit_mismatch ctx.diagnostics ~location kind;
          if Wax_utils.Uint64.compare ma max > 0 then
            Error.limit_too_large ctx.diagnostics ~location kind max)

(* Management methods shared by memories and tables, dispatched by the receiver
   (a memory or table name). *)
let is_mgmt_method m =
  match m with "size" | "grow" | "fill" | "copy" | "init" -> true | _ -> false

(* No-argument instruction methods written as a call on a value, [x.sqrt()]:
   the integer and float unary operators, the [to_bits]/[from_bits] reinterpret
   casts, and [arr.length()]. They are parsed as [Call (StructGet …, [])] and
   kept in that form so they print back with their parentheses. *)
let is_unary_method m =
  match m with
  | "clz" | "ctz" | "popcnt" | "extend8_s" | "extend16_s" | "abs" | "ceil"
  | "floor" | "trunc" | "nearest" | "sqrt" | "to_bits" | "from_bits" | "length"
    ->
      true
  | _ -> false

(* The instruction methods whose result has the width of their RECEIVER: the
   integer and float unary operators plus the two-operand rotates and float
   pairs, as opposed to those that fix a width of their own ([to_bits]/
   [from_bits], whose result is the receiver's bit width in the other family, and
   [length]). A cast on such a call's RESULT propagates back through it to the
   receiver — which is how a width pin on [(5).clz()] makes it an [i64.clz], the
   very mechanism [From_wasm] relies on when it tags a method result with its
   receiver's flexibility. Used by {!defaulting_tree}. *)
let is_width_preserving_method m =
  match m with
  | "clz" | "ctz" | "popcnt" | "extend8_s" | "extend16_s" | "abs" | "ceil"
  | "floor" | "trunc" | "nearest" | "sqrt" | "rotl" | "rotr" | "min" | "max"
  | "copysign" ->
      true
  | _ -> false

(* Whether the node's printed form takes its numeric type by DEFAULTING: a tree of
   numeric literals, holes and width-PRESERVING operators with nothing in it that
   fixes a width — no local, call result, memory read or cast. A pin around such a
   tree grounds every literal in it and converts nothing, whereas a pin around a
   tree holding a
   real datum would be a numeric CONVERSION of that datum. Mirrors [From_wasm]'s
   anchor-free notion ([is_anchor]/[reparse_adaptive]), and is needed beside
   {!flexible_literal} because a cast FOLDS a still-flexible literal into its
   target type ([cast] above), so by the end of inference such a tree's cell looks
   concrete even though its width was never anchored by anything. *)
let rec defaulting_tree ?(holes_only = false) (i : _ instr) =
  let defaulting_tree = defaulting_tree ~holes_only in
  match i.desc with
  (* A hole — a value the Wasm side left polymorphic — or, unless [holes_only], a
     numeric literal. NOT a [Char], whose i32 value a cast would convert rather
     than ground. *)
  | Hole -> true
  | Int _ | Float _ -> not holes_only
  (* The operators whose result type IS their operands': a pin on the result
     grounds them. A comparison or [!] yields i32 whatever its operands, and a
     cast fixes its own type, so neither continues the tree. *)
  | UnOp ({ Annot.desc = Neg | Pos; _ }, a) -> defaulting_tree a
  | BinOp
      ( {
          Annot.desc =
            Add | Sub | Mul | Div _ | Rem _ | And | Or | Xor | Shl | Shr _;
          _;
        },
        a,
        b ) ->
      defaulting_tree a && defaulting_tree b
  | Select (_, a, b) -> defaulting_tree a && defaulting_tree b
  | Sequence (_ :: _ as l) -> defaulting_tree (List.nth l (List.length l - 1))
  (* A method whose result width is its receiver's ([(5).clz()],
     [(1).rotl(40)]): the pin on the result reaches the receiver through it. *)
  | Call ({ desc = StructGet (recv, meth); _ }, args)
    when is_width_preserving_method meth.Annot.desc ->
      defaulting_tree recv && List.for_all defaulting_tree args
  (* A NARROW atomic RMW takes its i32/i64 family from its value operand, whose
     cell the typer merges with the result's ([type_atomic_method_call]), so a pin
     on the result grounds it — its method name carries the access width only
     ([atomic_rmw_add8] spells both the i32 and the i64 op). It continues the tree
     through the value operands and not the memory receiver or the address, which
     fix no width of the result. A [`W64] RMW states its own width, and a narrow
     atomic LOAD resolves through its own [as iN_u] cast, so neither belongs here.
     Without this the width repair could not place the pin an [i64] narrow RMW in
     dead code needs — the value it merges with is a hole, so the printed form
     re-parsed at the i32 default and narrowed the opcode — and reported the
     disagreement as unrepairable instead (a wat-mutation-fuzzer finding). *)
  | Call ({ desc = StructGet (_, meth); _ }, args)
    when match Wax_wasm.Atomics.of_method_name meth.Annot.desc with
         | Some (Rmw (_, (`W8 | `W16 | `W32))) -> true
         | Some (Rmw (_, `W64) | Load _ | Store _ | Wait _ | Notify) | None ->
             false -> (
      (* The address is the first positional argument, the value operands follow
         (two for a [cmpxchg]); the memarg immediates are labelled. *)
      match
        List.filter
          (fun (a : _ instr) ->
            match a.desc with Labelled _ -> false | _ -> true)
          args
      with
      | _addr :: (_ :: _ as values) -> List.for_all defaulting_tree values
      | _ -> false)
  | _ -> false

(* Register (once) a type definition for an anonymous function signature and
   return the synthetic name standing for it — used when a cast or [call_ref]
   needs a named [func] type but the source wrote the signature inline. The name
   is a deterministic mangling of the signature, so identical signatures map to
   the same definition; [to_wasm] materialises it through the [<..>]
   synthetic-type path. *)
let anon_function_type ctx (sign : functype) =
  let buf = Buffer.create 32 in
  let rec vt (t : valtype) =
    match t with
    | I32 -> Buffer.add_char buf 'i'
    | I64 -> Buffer.add_char buf 'I'
    | F32 -> Buffer.add_char buf 'f'
    | F64 -> Buffer.add_char buf 'F'
    | V128 -> Buffer.add_char buf 'v'
    | Ref { nullable; typ } ->
        Buffer.add_char buf '&';
        if nullable then Buffer.add_char buf '?';
        ht typ
  and ht (h : heaptype) =
    Buffer.add_string buf
      (match h with
      | Func -> "func"
      | NoFunc -> "nofunc"
      | Exn -> "exn"
      | NoExn -> "noexn"
      | Cont -> "cont"
      | NoCont -> "nocont"
      | Extern -> "extern"
      | NoExtern -> "noextern"
      | Any -> "any"
      | Eq -> "eq"
      | I31 -> "i31"
      | Struct -> "struct"
      | Array -> "array"
      | None_ -> "none"
      | Type id -> "$" ^ id.desc
      | Exact id -> "!$" ^ id.desc)
  in
  Buffer.add_string buf "<fn:";
  Array.iter
    (fun p ->
      vt (param_type p);
      Buffer.add_char buf ';')
    sign.params;
  Buffer.add_string buf "->";
  Array.iter
    (fun t ->
      vt t;
      Buffer.add_char buf ';')
    sign.results;
  Buffer.add_char buf '>';
  let name = Ast.no_loc (Buffer.contents buf) in
  (* A pure existence check: [Tbl.exists] would also *report* a spurious
     "already bound" error on the second cast with the same signature. *)
  if Tbl.find_opt ctx.type_context.types name = None then
    ignore
      (add_type ctx.diagnostics ctx.type_context
         [|
           Ast.no_loc
             ( name,
               {
                 supertype = None;
                 typ = Func sign;
                 final = true;
                 descriptor = None;
                 describes = None;
               } );
         |]
        : Wax_wasm.Types.Id.t option);
  name

(* Peel a type-checked [dispatch] lowering (see [Ast_utils.lower_dispatch]) back
   apart: descend [k] case blocks, collecting each case body, and return the
   [br_table] index together with the bodies in arm order. Deterministic — the
   lowering we just type-checked guarantees the shape. *)
let extract_dispatch wrapper k =
  let body_of w =
    match w.desc with Ast.Block { block; _ } -> block.desc | _ -> assert false
  in
  let rec peel block n =
    if n = 0 then
      match block with
      | [ { desc = Ast.Br_table (_, idx); _ } ] -> (idx, [])
      | _ -> assert false
    else
      match block with
      | head :: tail ->
          let idx, bodies = peel (body_of head) (n - 1) in
          (idx, tail :: bodies)
      | [] -> assert false
  in
  peel (body_of wrapper) k

(* Rebuild a typed [dispatch] from the type-checked lowering [typed_list] (the
   outermost case block followed by its trailing body) and the original [arms]
   (for the labels). Arms are in fall-through order, the reverse of the block
   nesting (see [Ast_utils.lower_dispatch]), so we peel against the reversed arm
   list — outermost first — and reverse the result back. Returns the typed index
   and arms. *)
let rebuild_dispatch typed_list arms =
  match (List.rev arms, typed_list) with
  | [], [ { desc = Ast.Br_table (_, idx); _ } ] -> (idx, [])
  | (outer_label, outer_orig) :: rest_arms, outer :: outer_body ->
      let idx, rest_bodies = extract_dispatch outer (List.length rest_arms) in
      ( idx,
        List.rev
          ((outer_label, { outer_orig with Annot.desc = outer_body })
          :: List.map2
               (fun (l, (orig : (_ instr list, location) Ast.annotated)) b ->
                 (l, { orig with desc = b }))
               rest_arms rest_bodies) )
  | _ -> assert false

(* Peel a type-checked [while] lowering (see [Ast_utils.lower_while]) back to the
   typed condition, continue-expression and body, dropping the synthesised loop,
   [if] and back-edge. Deterministic — the lowering we just type-checked
   guarantees the shape. [stepped]/[labelled] pick which of the three shapes
   [lower_while] produced. *)
let rebuild_while ~stepped ~labelled typed_list =
  match typed_list with
  | [
   {
     desc =
       Ast.Loop
         { block = { desc = [ { desc = If { cond; if_block; _ }; _ } ]; _ }; _ };
     _;
   };
  ] -> (
      match (stepped, labelled) with
      (* Labelled step: [ block { body } ; step ; br ] *)
      | true, true -> (
          match if_block.desc with
          | [
           { desc = Ast.Block { block = { desc = body; _ }; _ }; _ };
           step;
           { desc = Br _; _ };
          ] ->
              (cond, Some step, body)
          | _ -> assert false)
      (* Unlabelled step: [ body… ; step ; br ]; else just [ body… ; br ]. *)
      | _ -> (
          match List.rev if_block.desc with
          | { desc = Ast.Br _; _ } :: step :: rev_body when stepped ->
              (cond, Some step, List.rev rev_body)
          | { desc = Ast.Br _; _ } :: rev_body -> (cond, None, List.rev rev_body)
          | _ -> assert false))
  | _ -> assert false

(* Peel a type-checked [match] lowering (see [Ast_utils.lower_match]) apart. The
   lowering nests one block per arm inside an outer void [escape] block, each
   wrapping the previous block (its result consumed for the previous arm) then
   that arm's body; the innermost block holds the threaded test chain and the
   [escape] branch, and the [default] follows the [escape] block as trailing
   code. Descending from the [escape] block consumes the arms in reverse source
   order. Returns the typed arm bodies (paired with the original patterns), the
   typed default, and the typed scrutinee (the innermost operand of the test
   chain) — [None] when there are no arms, so the scrutinee never appears in the
   lowering. *)
(* Raised by [rebuild_match] when the type-checked lowering is not the block
   nesting the lowering produces. That shape is guaranteed only when typing
   SUCCEEDS; an erroneous scrutinee (e.g. a hole that underflows, or one whose
   type failed to resolve) can make the checker recover into a different shape,
   so the callers catch this and fall back rather than crashing. *)
exception Match_shape

let rebuild_match typed_list arms =
  match arms with
  | [] -> ([], typed_list, None)
  | _ ->
      let block_body blk =
        match blk.desc with
        | Ast.Block { block; _ } -> block.desc
        | _ -> raise Match_shape
      in
      (* Strip a wrapper block's leading consume of its inner block, returning
         that inner block and the arm body following it. *)
      let unwrap pat stmts =
        match (pat, stmts) with
        | ( Ast.MatchCast (Some _, _),
            { desc = Ast.Let (_, Some inner); _ } :: body ) ->
            (inner, body)
        | ( Ast.MatchCast (None, _),
            { desc = Ast.Let ([ (None, _) ], Some inner); _ } :: body ) ->
            (inner, body)
        | Ast.MatchNull, inner :: body -> (inner, body)
        | _ -> raise Match_shape
      in
      let escape, default =
        match typed_list with x :: r -> (x, r) | [] -> raise Match_shape
      in
      (* The innermost block's body is [drop chain; br escape]; the chain wraps
         the scrutinee in one [br_on_cast]/[br_on_null] per arm, so descend that
         many levels to recover the typed scrutinee. *)
      let scrutinee_of_inner blk =
        match block_body blk with
        | { desc = Ast.Let (_, Some chain); _ } :: _ ->
            let rec descend k c =
              if k = 0 then c
              else
                match c.desc with
                | Ast.Br_on_cast (_, _, operand) | Ast.Br_on_null (_, operand)
                  ->
                    descend (k - 1) operand
                | _ -> c
            in
            descend (List.length arms) chain
        | _ -> raise Match_shape
      in
      let rec peel blk = function
        | [] ->
            (* [blk] is the innermost block (test chain + escape). *)
            ([], scrutinee_of_inner blk)
        | (pat, orig) :: rest_rev ->
            let inner, arm_body = unwrap pat (block_body blk) in
            let rest, scrut = peel inner rest_rev in
            ((pat, { orig with Annot.desc = arm_body }) :: rest, scrut)
      in
      let arms_rev, scrut = peel escape (List.rev arms) in
      (List.rev arms_rev, default, Some scrut)

(* Synthesise the block labels for a [match] lowering: one per arm, then the
   outer [escape] label ([n+1] in all). The [<…>] form is outside the source
   identifier grammar, so it cannot capture a user branch. *)
let match_labels info arms =
  List.init
    (List.length arms + 1)
    (fun k -> { desc = Printf.sprintf "<match%d>" k; info })

(* The scrutinee's external reference type, used as the arm blocks' result type
   (a failed test forwards the scrutinee there). [None] if it is not a single
   reference value. *)
let match_scrut_reftype ctx scrut' =
  match standalone_valtype ctx (expression_type ctx scrut') with
  | Some { typ = Ref _ as typ; _ } -> Some typ
  | _ -> None

(* Classify how a block's trailing instruction produces the block's value, as
   [(needs_context, self_resolving)]. [needs_context] is a construction whose
   type the surrounding context must pin (an ambiguous/named/default struct, an
   array, a string, a [null] cast, or a [?:] with such a branch): it is checked
   against the result, so a surrounding result annotation is load-bearing.
   [self_resolving] resolves its own type (a nested block with no parameters, a
   struct named unambiguously by its fields, or a descriptor construction, whose
   type the descriptor pins). Anything else — a plain statement, a parameterized
   block, a scalar [?:] — sets neither; a block then types it on the statement
   path rather than against its result. *)
let rec classify_trailing ctx desc =
  match desc with
  | Struct (_, fields) -> (
      match infer_struct_by_fields ctx fields with
      | Some _ -> (false, true)
      | None -> (true, false))
  (* A descriptor construction ([{descriptor(d) | ..}], [descriptor(d)::default])
     takes its type from the descriptor [d], not the surrounding context, and
     carries no droppable type name — so it resolves its own type regardless of
     whether its fields are unique, unlike the plain [Struct] above. *)
  | StructDesc _ | StructDefaultDesc _ -> (false, true)
  | StructDefault _ | Array _ | ArrayDefault _ | ArrayFixed _ | ArraySegment _
  | String _ ->
      (true, false)
  | If { typ; _ }
  | Block { typ; _ }
  | Loop { typ; _ }
  | TryTable { typ; _ }
  | Try { typ; _ }
  | TryCatch { typ; _ } ->
      if Array.length typ.params = 0 then (false, true) else (false, false)
  | Cast (e, _) -> (is_null_initializer e, false)
  | Select (_, a, b) ->
      (* Needs the context iff a branch does; a select is not itself a
         self-resolving nested block. *)
      ( fst (classify_trailing ctx a.desc) || fst (classify_trailing ctx b.desc),
        false )
  | _ -> (false, false)

(* The re-inference of a checked node: what an unannotated binding
   ([let x = <node>]) would infer its initializer to be, standalone — the
   information a surrounding binding annotation is redundant against.
   [check_instruction] returns it as its second component (the old keep-bool is
   [reinfer_needed] applied to it), and the [If]/[Select]/[Block] arms join their
   sub-nodes' compositionally. That is the fix the keep-bool needed: a nested
   construct reports its own re-inference upward rather than being read through
   its result cell, which the expected type has already flowed into — so a tail
   whose type came from the context no longer looks redundant. *)
type reinfer =
  | Diverges
      (** A [br]/[return]/[unreachable] tail: delivers no value, so it drops out
          of a join (the sibling arm decides). *)
  | Uninferrable
      (** Cannot be typed at all without the annotation — an un-named
          construction (an array literal, a field-ambiguous struct) whose type
          name has been dropped. Poisons a join: no sibling can rescue it. *)
  | Typ of inferred_type Cell.t
      (** Re-infers to this cell standalone, and safely narrows — an immutable
          binding may drop a mere-supertype annotation down to it
          ([drop_supertype]). Holds for scalars (a call, a literal) and
          constructions that re-infer their type structurally, without a written
          name (a field-unique struct, a descriptor construction): dropping the
          annotation then leaves a form that decompiles back to itself.

          A *snapshot* (a fresh copy, taken before any unification the expected
          type drove), holding the value's still-flexible type so a flexible
          literal absorbs into a concrete sibling under [join_reinfer] exactly
          as re-inference would; [join_reinfer] merges it, so it must not be
          shared with the typed AST. *)
  | Named of inferred_type Cell.t
      (** Re-infers to this cell via a *written type name* (an array literal
          [[t| ..]], a named struct-default) that the surrounding annotation
          does not itself pin. Such a construction drops its annotation only
          when the annotation is exactly its type, never by narrowing: narrowing
          an immutable binding to the (strict-subtype) construction type would
          make the written name redundant on the next cycle and the
          decompilation flip between "name, no annotation" and "annotation, no
          name" — so a strict-supertype annotation is load-bearing for
          round-trip stability. Same snapshot discipline as [Typ]. *)

(* Snapshot a cell into a fresh, mutation-safe [Typ]. *)
let reinfer_of_cell ty = Typ (Cell.make (Cell.get ty))

(* Snapshot a cell into a name-dependent [Named]. *)
let named_reinfer_of_cell ty = Named (Cell.make (Cell.get ty))

(* Join two branches' re-inference (an [if]'s arms, a [?:]'s values, a block's
   exits): a diverging branch drops out, an uninferrable one poisons the whole,
   and two typed branches join by [join_value_types] (a failed join is
   uninferrable). [join_value_types] absorbs a flexible literal into a concrete
   sibling, so a bare [1] alongside a typed [i64] joins to [i64] — the annotation
   is then redundant — while two flexible literals stay flexible and re-default
   the same on re-parse. A join is [Named] (equality-only) when either branch is:
   if a branch relies on a written name, narrowing the whole would flip it. *)
let join_reinfer ctx a b =
  match (a, b) with
  | Diverges, x | x, Diverges -> x
  | Uninferrable, _ | _, Uninferrable -> Uninferrable
  | (Typ ta | Named ta), (Typ tb | Named tb) -> (
      let named =
        match (a, b) with Named _, _ | _, Named _ -> true | _ -> false
      in
      match join_value_types ctx ta tb with
      | Some c -> if named then Named c else Typ c
      | None -> Uninferrable)

(* Whether a binding annotation [expected] is load-bearing given its
   initializer's re-inference: a diverging/uninferrable initializer keeps it (an
   unannotated binding could not re-derive the type); a typed one keeps it iff
   its standalone (re-defaulted) type differs from [expected]. [drop_supertype]
   loosens the test for an immutable binding to allow narrowing (see
   [annotation_needed]) — but only for a [Typ]; a [Named] drops only on exact
   equality, never by narrowing. This derives the old scalar keep-bool from the
   compositional re-inference. *)
let reinfer_needed ?(drop_supertype = false) ctx reinfer expected =
  match reinfer with
  | Diverges | Uninferrable -> true
  | Typ c ->
      annotation_needed ~drop_supertype ctx (standalone_valtype ctx c) expected
  | Named c -> annotation_needed ctx (standalone_valtype ctx c) expected

(*** The instruction type-checker ***)

(* Set to [true] to trace each instruction as it is type-checked. *)
let debug = false

(* Deliver the values below a [br_if]/[br_on_null] operand to the branch target
   and return their fall-through result types. Shared by both branches (their only
   difference is what each appends to the result afterward: [br_on_null] adds the
   non-null reference). [types] are the delivered values' types and [params] the
   target's parameter types, both at [loc].

   When the target is a block result being inferred, each delivered value is an
   [exact] exit: its natural type — snapshotted here, before the delivery below
   pins it — must equal the block's result, not merely be a subtype. A flexible
   numeric literal among them can be pinned to a non-default width by a downstream
   op on re-parse, so the annotation is kept ([cs.needed]). On the fall-through
   the values stay typed as the target's result ([resolve_declared]); when the
   target has no declared result that cell would leak, so fall back to the
   operands' own [types]. *)
let deliver_to_branch_target ctx ~loc ~types ~params =
  if Array.length types = Array.length params then
    Array.iter2
      (fun ty param ->
        match Cell.get param with
        | Collecting cs -> (
            cs.exacts <- (Some loc, Cell.make (Cell.get ty)) :: cs.exacts;
            match Cell.get ty with
            | Number | Int | LargeInt | Float -> cs.needed <- true
            | _ -> ())
        | _ -> ())
      types params;
  check_subtypes ctx ~location:loc types params;
  (* Guard the arity as the snapshot loop does: on a mismatch [check_subtypes]
     has reported the arity error, so [map2] would only crash on the unequal
     lengths — fall back to the target's params. *)
  if
    Array.exists is_inferring params && Array.length types = Array.length params
  then
    Array.map2
      (fun ty param ->
        match Cell.get param with
        | Collecting { declared = None; _ } -> ty
        | _ -> resolve_declared param)
      types params
  else params

(* Once a value-producing operand has been seen, record its location so a later
   hole in the same distribution can be flagged against it. *)
let bump_value_loc ctx st node =
  match st.value_loc with
  | Some _ -> st
  | None ->
      if emits_value ctx node then { st with value_loc = Some (snd node.info) }
      else st

let rec count_holes i =
  match i.desc with
  | Hole -> 1
  | BinOp (_, l, r)
  | Array (_, l, r)
  | ArraySegment (_, _, l, r)
  | ArrayGet (l, r) ->
      count_holes l + count_holes r
  | ArraySet (t, i, v) -> count_holes t + count_holes i + count_holes v
  | Call (f, args) | TailCall (f, args) ->
      count_holes f + List.fold_left (fun acc i -> acc + count_holes i) 0 args
  | If { cond = i; _ }
  | Let (_, Some i)
  | Set (_, _, i)
  | Tee (_, i)
  | Labelled (_, i)
  | UnOp (_, i)
  | Cast (i, _)
  | Test (i, _)
  | NonNull i
  | Br (_, Some i)
  | Br_if (_, i)
  | On (i, _)
  | Br_table (_, i)
  | Br_on_null (_, i)
  | Br_on_non_null (_, i)
  | Br_on_cast (_, _, i)
  | Br_on_cast_fail (_, _, i)
  | ArrayDefault (_, i)
  | ThrowRef i
  | ContNew (_, i)
  | Return (Some i)
  | StructDefaultDesc i
  | GetDescriptor i
  | StructGet (i, _) ->
      count_holes i
  | CastDesc (i1, _, i2)
  | Br_on_cast_desc_eq (_, _, i1, i2)
  | Br_on_cast_desc_eq_fail (_, _, i1, i2)
  | StructSet (i1, _, i2) ->
      count_holes i1 + count_holes i2
  (* A punned field ([None]) is a [Get], which contains no holes. *)
  | Struct (_, l) ->
      List.fold_left
        (fun acc (_, i) -> acc + Option.fold ~none:0 ~some:count_holes i)
        0 l
  | StructDesc (d, l) ->
      count_holes d
      + List.fold_left
          (fun acc (_, i) -> acc + Option.fold ~none:0 ~some:count_holes i)
          0 l
  | Sequence l
  | ArrayFixed (_, l)
  | ContBind (_, _, l)
  | Suspend (_, l)
  | Resume (_, _, l)
  | ResumeThrow (_, _, _, l)
  | ResumeThrowRef (_, _, l)
  | Switch (_, _, l)
  | Throw (_, l) ->
      List.fold_left (fun acc i -> acc + count_holes i) 0 l
  | Select (c, t, e) -> count_holes c + count_holes t + count_holes e
  (* [dispatch]/[match], [while] and [do]-[while] are block-like: their
     operands/scrutinee and bodies are checked inside the blocks they desugar
     to, so no hole at this level draws from the stack. *)
  | Block _ | Loop _ | While _ | TryTable _ | Try _ | TryCatch _
  | If_annotation _ | Dispatch _ | Match _ | StructDefault _ | Char _ | String _
  | Int _ | Float _ | Get _ | Path _ | Null | Unreachable | Nop
  | Let (_, None)
  | Br (_, None)
  | Return None ->
      0

(* Type one operand of a distribution point against exactly its own hole-slice —
   the front [count_holes child] pending values — and fold in the hole-order
   check (see [hole_st]). [run] is the child-typer applied to the child (an
   [instruction]/[check_instruction] action), [node_of] extracts the typed
   instruction from its result (identity, resp. [fst]). The child's own leftover
   is dropped: it receives its slice and nothing more, so it cannot desynchronise
   its siblings. Fast path — no pending values means the whole subtree is
   hole-free, so skip counting (but still note whether a value was emitted, for a
   later sibling's hole). *)
let hole_child ctx child node_of run st =
  match st.pending with
  | [] ->
      let st', r = run st in
      (bump_value_loc ctx st' (node_of r), r)
  | pending ->
      let n = count_holes child in
      let reported =
        if (not st.reported) && n > 0 && st.value_loc <> None then (
          Error.before_hole ctx.diagnostics ~location:(Option.get st.value_loc);
          true)
        else st.reported
      in
      let slice, rest = list_split n pending in
      let st', r = run { st with pending = slice; reported } in
      (bump_value_loc ctx { st' with pending = rest } (node_of r), r)

(* Type a trailing operand out of emission order, for a construct whose type flow
   runs backwards from it: [run ()] types the operand now — before the operands
   that precede it in emission — so its type can direct their checking (a call
   callee's parameters, a [StructDesc] descriptor's struct type).

   The hole slices already make this sound for the stack; this makes it sound for
   the initialized-locals analysis, which threads in emission order. Within a
   straight-line operand sequence that set only grows, so the state [run] sees is
   a SUBSET of the true state at the operand's emission slot: a read that succeeds
   now is sound; a read that fails is DEFERRED (collected, not reported); and the
   operand's own straight-line writes are captured and WITHHELD from
   [initialized_locals] until the emission slot, so an earlier operand — which
   runs first — cannot see them. Returns the typed operand and a [replay] thunk to
   run at that slot: it re-checks each deferred read against the now-current state
   (an earlier operand may have initialized the local), reporting or, under an
   outer deferral, re-deferring the survivors, then applies the withheld writes. *)
let type_trailing_operand ctx run =
  let saved = ctx.initialized_locals in
  let collector = ref [] in
  ctx.deferred_uninit <- collector :: ctx.deferred_uninit;
  let result =
    Fun.protect
      ~finally:(fun () -> ctx.deferred_uninit <- List.tl ctx.deferred_uninit)
      run
  in
  let delta = ctx.initialized_locals in
  ctx.initialized_locals <- saved;
  let deferred = List.rev !collector in
  let replay () =
    List.iter
      (fun idx ->
        if not (StringSet.mem idx.Annot.desc ctx.initialized_locals) then
          report_uninitialized ctx idx)
      deferred;
    ctx.initialized_locals <- StringSet.union ctx.initialized_locals delta
  in
  (result, replay)

(* Fold one already-typed operand [node] (untyped form [child]) into the running
   hole-order state, as [hole_child] does inline, but for an operand typed out of
   its emission position — a call callee or [StructDesc] descriptor, emitted last
   but typed first for its type. [st.value_loc] must already reflect the operands
   emitted before it. *)
let fold_operand ctx child node st =
  let st =
    if (not st.reported) && count_holes child > 0 && st.value_loc <> None then (
      Error.before_hole ctx.diagnostics ~location:(Option.get st.value_loc);
      { st with reported = true })
    else st
  in
  bump_value_loc ctx st node

(* Bridge from the statement (stack) monad to the expression monad: pop the
   [count_holes i] hole operands off the operand stack into the pending list and
   run [f] (an expression-monad action) with a fresh hole state, returning its
   result in the stack monad. Typing hands each hole its slice and the hole-order
   check runs inline ([hole_child]); the final expression state is discarded (a
   leftover pending is a recovery-only artefact, see [pop_parameter]). *)
let with_holes ctx i build =
  let* pending, batch = pop_many ctx (count_holes i) in
  let _st, r = build () { pending; value_loc = None; reported = false } in
  (* An underflow placeholder normally reaches a hole, which reports it at its
     own location ([report_missing_hole]); when recovery dropped it instead,
     report here, against the whole expression. *)
  (match !batch with
  | Some b ->
      ctx.missing_holes :=
        List.filter (fun (_, b') -> b' != b) !(ctx.missing_holes);
      if not b.hole_reported then begin
        b.hole_reported <- true;
        Error.short_stack ctx.diagnostics `Holes ~location:i.info
          ~actual:b.hole_actual ~expected:b.hole_expected
      end
  | None -> ());
  return r

(* A [match] scrutinee, [dispatch] index or [while] condition is evaluated inside
   the blocks the construct lowers to, whose stack excludes the enclosing
   statement's pending values — so a hole there has nothing to consume (and could
   not be re-consumed each iteration of a [while]). Reject it with a clear error
   rather than the stack-underflow cascade it would otherwise trigger, and replace
   the whole operand with [Unreachable] so the rest of the construct still
   type-checks for recovery. Returns the (possibly replaced) operand and whether
   it was rejected, so the caller can skip a follow-up check that would cascade.
   [from_wasm] never emits such a hole — a recovered [match] scrutinee is
   re-readable (see [Recover_match.same_scrut], never a hole) and a while
   condition sits in the leading test of a void loop — so this only rejects
   hand-written code. *)
let reject_control_holes ctx ~construct ~role ~recovery operand =
  if count_holes operand > 0 then (
    Error.hole_in_control_operand ctx.diagnostics ~location:operand.info
      ~construct ~role;
    (* Replace the whole operand with a hole-free value of the shape the
       construct expects ([recovery]: a null reference for a scrutinee, [0] for
       an [i32] index/condition), so the lowering type-checks without a
       stack-underflow or wrong-shape cascade on top of the reported error. *)
    ({ operand with desc = recovery }, true))
  else (operand, false)

(* The lattice type of a float(-valued) literal [s]: the flexible [Float] (either
   width, pinned by context) when [s] rounds to a valid f32, else concrete [f64].
   An out-of-f32-range magnitude must never be pinned to f32 — it would print as
   an out-of-range [f32.const] — so a later [as f32] lowers to a real [f64->f32]
   demote instead of folding into the literal. *)
let float_literal_lattice s =
  if Wax_wasm.Misc.is_float32 s then Float else Valtype f64_valtype

let rec instruction ctx i : _ hole_st -> _ hole_st * (_ array * _) instr =
  if debug then Wax_utils.Printer.run_err (fun p -> Printer_output.instr p i);
  match i.desc with
  | Block _ | Dispatch _ | Match _ | Loop _ | While _ | If _ | If_annotation _
  | TryTable _ | Try _ | TryCatch _ ->
      type_block_construct ctx i
  | (Unreachable | Nop) as desc ->
      (* [unreachable] and [nop] are statements that yield no value; they are
         only meaningful in statement (top-level) position, where
         [toplevel_instruction] handles them. Reaching here means one was used
         where a value is expected, so report it and recover with an unknown
         value. *)
      Error.not_an_expression ctx.diagnostics ~location:i.info 0;
      return_expression i desc (Cell.make Error)
  | Hole ->
      let* ty = pop_parameter in
      report_missing_hole ctx ~location:i.info ty;
      return_expression i Hole ty
  | Null -> return_expression i Null (Cell.make Null)
  | Get _ | Set _ | Tee _ -> type_variable_access ctx i
  | Path (ns, name) ->
      Error.intrinsic_not_called ctx.diagnostics ~location:i.info ns.desc
        name.desc;
      return_expression i (Path (ns, name)) (Cell.make Error)
  | Call _ -> call_instruction ctx i
  | TailCall (i', l) -> (
      (* Type it exactly as the corresponding call — reusing the whole intrinsic
         dispatch, so [become mem.grow(n)] etc. are accepted like [mem.grow(n)]
         — then re-tag it as a tail call and require the callee's results to be
         subtypes of this function's declared results. *)
      let* typed = call_instruction ctx { i with desc = Call (i', l) } in
      match typed.desc with
      | Call (i'', l') ->
          check_subtypes ctx ~location:i.info (fst typed.info) ctx.return_types;
          return_statement i (TailCall (i'', l')) [||]
      | Unreachable ->
          (* Typing the call already failed: a [let*!] on a [None] lookup yields
             an [Unreachable] node typed [Error] (with the error already
             reported). There is no tail call to form; propagate the failed
             result rather than re-reporting or [assert false]. *)
          return typed
      | _ ->
          (* The call type-checked but is not a [Call]: it is a stack-switching
             operation ([resume]/[resume_throw]/[resume_throw_ref]/[switch] on a
             continuation receiver, or [k::new]/[k::bind]), to which no tail call
             can apply. Report it rather than silently dropping the [become]
             marker (which would also skip the return-type check); recover with
             the plain operation. (A well-formed direct or indirect call is
             always a [Call], via [type_indirect_call].) *)
          Error.become_on_stack_switching ctx.diagnostics ~location:i.info;
          return typed)
  | Labelled (_, e) ->
      (* A labelled argument is only meaningful as a direct argument of a
         memory-access call, whose typers consume the labels before typing the
         rest; reaching here means it appeared anywhere else (a plain call, a
         non-memory method, …). Recover by typing the payload in place. *)
      Error.labelled_argument_not_allowed ctx.diagnostics ~location:i.info;
      instruction ctx e
  | Char _ as desc -> return_expression i desc i32_cell
  | Int s as desc ->
      (* Pick the lattice type from the magnitude (the sign is a separate [Neg],
         so this is unsigned): a value over the 32-bit range cannot be i32, so it
         is [LargeInt] (which defaults to i64) rather than the i32-defaulting
         [Number]; one that does not even fit u64 cannot be any integer type, so
         it is [Float] (representable only by f32/f64) — using it as an integer is
         then a clean type error rather than an [Int64.of_string] crash in the
         encoder. *)
      let lattice =
        match
          if String.starts_with ~prefix:"0x" s then Int64.of_string_opt s
          else Int64.of_string_opt ("0u" ^ s)
        with
        | None -> float_literal_lattice s
        | Some v when Int64.unsigned_compare v 0xFFFFFFFFL > 0 -> LargeInt
        | Some _ -> Number
      in
      return_expression i desc (Cell.make lattice)
  | Float s as desc ->
      return_expression i desc (Cell.make (float_literal_lattice s))
  | Cast _ | CastDesc _ | Test _ -> type_cast ctx i
  | Struct _ | StructDefault _ | StructDesc _ | StructDefaultDesc _ | Array _
  | ArrayDefault _ | ArrayFixed _ | ArraySegment _ | String _ ->
      let* i', _ = check_instruction ctx (Cell.make Unknown) i in
      return i'
  | StructGet _ | GetDescriptor _ | StructSet _ | ArrayGet _ | ArraySet _ ->
      type_aggregate_access ctx i
  | BinOp _ | UnOp _ -> type_arith ctx i
  | Let _ -> type_let ctx i
  | Br _ | Br_if _ | Br_table _ | Br_on_null _ | Br_on_non_null _ | Br_on_cast _
  | Br_on_cast_fail _ | Br_on_cast_desc_eq _ | Br_on_cast_desc_eq_fail _ ->
      type_branch ctx i
  | Throw _ | ThrowRef _ -> type_exception ctx i
  | ContNew _ | ContBind _ | Suspend _ | Resume _ | ResumeThrow _
  | ResumeThrowRef _ | Switch _ | On _ ->
      type_stack_switching ctx i
  | NonNull i' -> (
      let* i' = instruction ctx i' in
      match Cell.get (expression_type ctx i') with
      | Valtype
          {
            typ = Ref { nullable = _; typ; _ };
            internal = Ref { nullable = _; typ = ityp; _ };
            anon_comptype;
          } ->
          return_expression i (NonNull i')
            (Cell.make
               (Valtype
                  {
                    typ = Ref { nullable = false; typ };
                    internal = Ref { nullable = false; typ = ityp };
                    anon_comptype;
                  }))
      | Unknown | UnknownRef | Null ->
          (* A reference recovered from a polymorphic value — dead/branch code, a
             value already known only as a reference, or a bare [null]: the
             non-null bottom reference [UnknownRef], a subtype of every reference
             type (so it satisfies any consumer). [ref.as_non_null] of a null is
             valid Wasm (it just always traps), so a bare [null] is accepted here
             too — like [br_on_null] and [ref.is_null] on a bottom reference. *)
          return_expression i (NonNull i') (Cell.make UnknownRef)
      | Error -> return_expression i (NonNull i') (expression_type ctx i')
      | _ ->
          Error.expected_ref ctx.diagnostics ~location:(snd i'.info);
          return_expression i (NonNull i') (Cell.make Error))
  | Return i' ->
      let* i' =
        match i' with
        | Some i' ->
            let* i' = check_against ctx ctx.return_types i' in
            return (Some i')
        | None ->
            if ctx.return_types <> [||] then
              Error.value_count_mismatch ctx.diagnostics ~location:i.info
                ~expected:(Array.length ctx.return_types)
                ~provided:0;
            return None
      in
      return_statement i (Return i') [||]
  | Sequence l ->
      let* l' = instructions ctx l in
      return_statement i (Sequence l')
        (Array.map (expression_type ctx) (Array.of_list l'))
  | Select (i1, i2, i3) ->
      (* Emission order is the two branch values then the condition (the [select]
         pops the condition last), so type them in that order for the hole
         slices and hole-order check. *)
      let* i2' = typed ctx i2 in
      let* i3' = typed ctx i3 in
      let* i1' = typed ctx i1 in
      check_type ctx i1' i32_cell;
      let*! ty =
        let ty1 = expression_type ctx i2' in
        let ty2 = expression_type ctx i3' in
        (* A select's two branch values join exactly as the values reaching a
           block's exit do; reuse [join_value_types] and, on no common type,
           report it against the select. *)
        match join_value_types ctx ty1 ty2 with
        | Some _ as r -> r
        | None ->
            Error.select_type_mismatch ctx.diagnostics ~location:i.info
              ~loc1:i2.info ~loc2:i3.info ty1 ty2;
            None
      in
      return_expression i (Select (i1', i2', i3')) ty

and descriptor_target ctx ~location ~nullable d =
  (* The custom-descriptors casts/branches write only the descriptor operand [d];
     the target reference type is recovered from it. [d] is emitted last, on top
     of the value operand (see [CastDesc]/[Br_on_cast_desc_eq]), so [typed] slices
     and hole-order-checks it as the trailing operand. Returns the typed operand
     and the recovered target reftype. ([StructDesc] instead types the descriptor
     first — for the struct type — and folds it in last itself, so it uses
     [descriptor_reftype] directly.) *)
  let* d' = typed ctx d in
  return (d', descriptor_reftype ctx ~location ~nullable d')

(* Recover the target reference type of a descriptor cast/branch/allocation from
   the (typed) descriptor operand [d' : (ref null? (exact_1 Y))] with
   [Y describes X]: the target is [(ref nullable (exact_1 X))] — the described
   type [X] and the exactness [exact_1] come from [d'], only the result
   nullability is written. [None] (with [type_without_descriptor] reported) when
   [d'] is not a reference to a descriptor type. *)
and descriptor_reftype ctx ~location ~nullable d' =
  let target =
    match Cell.get (expression_type ctx d') with
    | Valtype { typ = Ref { typ = (Type y | Exact y) as yt; _ }; _ } -> (
        match Tbl.find_opt ctx.type_context.types y with
        | Some (_, { describes = Some x; _ }) ->
            let exact = match yt with Exact _ -> true | _ -> false in
            Some { nullable; typ = (if exact then Exact x else Type x) }
        | _ -> None)
    | _ -> None
  in
  (match target with
  | Some _ -> ()
  | None -> Error.type_without_descriptor ctx.diagnostics ~location);
  target

(* [typed]/[typed_check] wrap the two child-typers ([instruction]/
   [check_instruction]) in [hole_child], the slice + hole-order machinery defined
   before the recursion. *)
and typed ctx child = hole_child ctx child Fun.id (instruction ctx child)

and typed_check ctx expected child =
  hole_child ctx child fst (check_instruction ctx expected child)

and type_branch ctx i =
  (* The branch instructions: [br], [br_if], [br_table] and the [br_on_*]
     family, each checking its operand(s) against the target label's
     parameter types. *)
  match i.desc with
  | Br (label, i') ->
      (* Sequence of instructions *)
      let params = branch_target ctx label in
      (* An unbound label was already reported by [branch_target]; its [[||]]
         params are not a real arity, so skip the checks that would anchor
         derived errors here (see [label_in_scope]). *)
      let bound = label_in_scope ctx label in
      let* i' =
        match i' with
        | Some i' when bound ->
            let* i' = check_against ctx params i' in
            return (Some i')
        | Some i' ->
            let* i' = instruction ctx i' in
            return (Some i')
        | None ->
            if bound && params <> [||] then
              Error.value_count_mismatch ctx.diagnostics ~location:i.info
                ~expected:(Array.length params) ~provided:0;
            return None
      in
      return_statement i (Br (label, i')) [||]
  | Br_if (label, i') ->
      let* i' = instruction ctx i' in
      let loc = snd i'.info in
      let ty, types = split_on_last_type ctx ~location:loc i' in
      check_subtype ctx ~location:loc ty i32_cell;
      let params = branch_target ctx label in
      (* Unbound label (already reported): the fall-through passes the values
         through unchanged, with no checks against the [[||]] pseudo-params. *)
      let result =
        if label_in_scope ctx label then
          deliver_to_branch_target ctx ~loc ~types ~params
        else types
      in
      return_statement i (Br_if (label, i')) result
  | Br_table (labels, i') ->
      let* i' = instruction ctx i' in
      let loc = snd i'.info in
      let ty, types = split_on_last_type ctx ~location:loc i' in
      check_subtype ctx ~location:loc ty i32_cell;
      (* Resolve every target (an unbound one reports at its own span, and
         used-label marking runs per occurrence); check arity and types only
         against the bound ones — an unbound label's [[||]] is not a real
         arity — and only ONCE per DISTINCT target: the check is purely
         per-target, so a repeated one would only repeat an identical report
         (mirrors the validator's [Br_table] dedup). Labels are names within
         the one enclosing scope — there is no numeric spelling on the Wax
         side — so identical spellings resolve to the same frame and the name
         is the target's identity. The reference arity is the first BOUND
         target's. *)
      let targets =
        List.map
          (fun label ->
            (label, label_in_scope ctx label, branch_target ctx label))
          labels
      in
      (match List.find_opt (fun (_, bound, _) -> bound) targets with
      | Some (first_label, _, first) ->
          let len = Array.length first in
          (* The count of values the [br_table] itself provides is a single fact,
             checked once against the reference arity: a per-target check (via
             [check_subtypes] below) would repeat an identical "provides N but M
             expected" report for every distinct target. *)
          if Array.length types <> len then
            Error.value_count_mismatch ctx.diagnostics ~location:i.info
              ~expected:len ~provided:(Array.length types);
          let seen = Hashtbl.create 8 in
          (* The type checks below are keyed by the target's PARAMETER TYPES, not
             by its name: two distinct targets imposing the same types on the same
             values yield the same report at the same span (the values'), which
             would render as one repeated [line:col: message]. Their arity reports
             are still per name — those carry the label's own span. Compared
             through [standalone_valtype], which is pure; a parameter with no
             resolved type yet compares unequal, so it is checked rather than
             silently skipped. *)
          let checked = ref [] in
          let same_requirement a b =
            Array.length a = Array.length b
            && Array.for_all2
                 (fun x y ->
                   match
                     (standalone_valtype ctx x, standalone_valtype ctx y)
                   with
                   | Some x, Some y -> valtype_equal ctx x y
                   | _ -> false)
                 a b
          in
          List.iter
            (fun ((label : Ast.ident), bound, params) ->
              if bound && not (Hashtbl.mem seen label.desc) then begin
                Hashtbl.add seen label.desc ();
                (* A target whose arity disagrees with the reference one — a
                   distinct fact per target, so reported here. *)
                if Array.length params <> len then
                  Error.branch_arity_mismatch ctx.diagnostics
                    ~location:label.info ~first_loc:first_label.info first_label
                    ~expected:len ~provided:(Array.length params);
                (* Type-check the provided values against this target only when
                   the counts line up (the count mismatch is already reported
                   once, above). [~pin:false]: the same values are checked
                   against every target, so a polymorphic (bottom) value must
                   not be pinned to one target's type — it is a subtype of each
                   legitimately-different target (see {!check_subtypes}). *)
                if
                  Array.length types = Array.length params
                  && not (List.exists (same_requirement params) !checked)
                then begin
                  checked := params :: !checked;
                  (* The value is what has the wrong type, so it keeps the
                     primary span; the label says which target wants what, so two
                     reports on the same value from differently-typed targets read
                     apart. *)
                  check_subtypes ~pin:false ~expected_at:label.info ctx
                    ~location:loc types params
                end
              end)
            targets
      | None -> ());
      return_statement i (Br_table (labels, i')) [||]
  | Br_on_null (idx, i') ->
      let* i' = instruction ctx i' in
      let typ, types = split_on_last_type ctx ~location:(snd i'.info) i' in
      let typ = Cell.get typ in
      let typ' =
        match typ with
        | Valtype
            {
              typ = Ref { nullable = _; typ; _ };
              internal = Ref { nullable = _; typ = ityp; _ };
              anon_comptype;
            } ->
            Cell.make
              (Valtype
                 {
                   typ = Ref { nullable = false; typ };
                   internal = Ref { nullable = false; typ = ityp };
                   anon_comptype;
                 })
        | Unknown | UnknownRef | Null ->
            (* A reference recovered from a polymorphic value, or a bare [null]
               (always null, so the branch is always taken): the non-null
               fall-through value is the bottom reference type [UnknownRef].
               Unlike [null!], this is a well-defined branch, not a contradiction
               — so a bare null is accepted here. *)
            Cell.make UnknownRef
        | Error -> Cell.make Error
        | _ ->
            Error.expected_ref ctx.diagnostics ~location:(snd i'.info);
            Cell.make Error
      in
      let loc = snd i'.info in
      let params = branch_target ctx idx in
      (* Like [br_if]: the values below the reference are delivered to the target
         and continue on the non-null fall-through, and the recovered non-null
         reference is appended. An unbound label (already reported) delivers
         nothing; the values pass through unchecked. *)
      let result =
        if label_in_scope ctx idx then
          deliver_to_branch_target ctx ~loc ~types ~params
        else types
      in
      return_statement i (Br_on_null (idx, i')) (Array.append result [| typ' |])
  | Br_on_non_null (idx, i') ->
      let* i' = instruction ctx i' in
      let params = branch_target ctx idx in
      let bound = label_in_scope ctx idx in
      let typ, types = split_on_last_type ctx ~location:(snd i'.info) i' in
      let typ = Cell.get typ in
      (* An unbound label (already reported): skip the checks against the
         [[||]] pseudo-params; the fall-through keeps the below-values. *)
      (match typ with
      | _ when not bound -> ()
      | Unknown | Error | UnknownRef -> ()
      | Valtype
          {
            typ = Ref { nullable = _; typ; _ };
            internal = Ref { nullable = _; typ = ityp; _ };
            anon_comptype;
          } ->
          check_subtypes ctx ~location:(snd i'.info)
            (Array.append types
               [|
                 Cell.make
                   (Valtype
                      {
                        typ = Ref { nullable = false; typ };
                        internal = Ref { nullable = false; typ = ityp };
                        anon_comptype;
                      });
               |])
            params
      | Null ->
          (* A bare [null] is always null, so the branch is never taken; the
             popped value's non-null form is the [any]-hierarchy bottom [&none].
             (A non-[any] null keeps its [as &?H] annotation in [type_cast], so
             only [any]-hierarchy bare nulls reach here.) *)
          check_subtypes ctx ~location:(snd i'.info)
            (Array.append types
               [|
                 Cell.make
                   (Valtype
                      {
                        typ = Ref { nullable = false; typ = None_ };
                        internal = Ref { nullable = false; typ = None_ };
                        anon_comptype = None;
                      });
               |])
            params
      | _ -> Error.expected_ref ctx.diagnostics ~location:(snd i'.info));
      return_statement i
        (Br_on_non_null (idx, i'))
        (* The branch delivers [types ++ [ref]] to the target and the fall-through
           keeps all but that trailing ref. A target with no params is malformed
           (already reported by [check_subtypes] above); [max 0] avoids
           [Array.sub _ 0 (-1)] and leaves an empty fall-through. For an
           unbound label the below-values pass through unchanged. *)
        (if bound then Array.sub params 0 (max 0 (Array.length params - 1))
         else types)
  | Br_on_cast (label, ty, i') ->
      let* i' = instruction ctx i' in
      if is_cont_heaptype ctx ty.typ then
        Error.invalid_cast_type ctx.diagnostics ~location:i.info;
      let typ', types = split_on_last_type ctx ~location:(snd i'.info) i' in
      let params = branch_target ctx label in
      let bound = label_in_scope ctx label in
      (* Unbound label (already reported): no check against the [[||]]
         pseudo-params, and the fall-through keeps the below-values. *)
      (if bound then
         let>@ ityp = reftype ctx.diagnostics ctx.type_context ty in
         let typ =
           Cell.make
             (Valtype
                { typ = Ref ty; internal = Ref ityp; anon_comptype = None })
         in
         check_subtypes ctx ~location:(snd i'.info)
           (Array.append types [| typ |])
           params);
      (* On success the branch carries the cast target [ty] (via [params]); the
         fall-through keeps the value at its residual type [typ2] ([ty'] minus
         [ty]). [typ1] re-types the operand as the lub of its type and [ty]. *)
      let*! typ1, typ2 =
        match Cell.get typ' with
        | Valtype { typ = Ref ty'; _ } ->
            (* The fall-through residual must be [diff(source, ty)] for the source
               [to_wasm] emits — [lub(ty, operand)] — not the operand's own [ty'];
               see the matching note in [Br_on_cast_fail]. A no-op when [ty <: ty']
               (a plain cast), where the lub is [ty']. A failed [val_lub] means
               [ty] and the operand are in different hierarchies — an invalid
               cast; report it and recover with the cast target. *)
            let ty1 =
              match val_lub ctx (Ref ty) (Ref ty') with
              | Some t -> t
              | None ->
                  Error.invalid_cast ctx.diagnostics ~location:(snd i'.info)
                    typ';
                  Ref ty
            in
            let*@ typ1 = internalize ctx ty1 in
            let+@ typ2 =
              internalize ctx
                (match ty1 with
                | Ref lub -> Ref (diff_ref_type lub ty)
                | _ -> Ref (diff_ref_type ty' ty))
            in
            (typ1, typ2)
        (* A polymorphic operand (unreachable / branch code): [to_wasm] recovers the
           source type as the cast target [ty], so the fall-through is [ty \ ty]
           (as the [Valtype] case computes with the operand's own type) — a concrete
           reference matching the emitted instruction. Not [Unknown]: the residual is
           always a reference, and not the bottom [UnknownRef] either, or a chained
           [br_on_cast] would recover a source that mismatches this one. *)
        | Unknown | UnknownRef ->
            let+@ typ2 = internalize ctx (Ref (diff_ref_type ty ty)) in
            (typ', typ2)
        | Error -> Some (typ', Cell.make Error)
        | Null ->
            (* A bare [null] operand carries no type wider than the cast target,
               so [to_wasm] reconstructs the source as [ty] made nullable and
               emits [br_on_cast (ref null H) ty]; the residual must be
               [diff(source, ty)] to match what wasm validation derives from
               those immediates. A null always matches a nullable [ty] and falls
               through, so the residual is unreachable at runtime, but wasm types
               it from the immediates, not the operand's nullness — typing it as
               the [(ref none)] bottom instead would accept programs whose
               emitted wasm the validator rejects. *)
            let source = { ty with nullable = true } in
            let*@ typ1 = internalize ctx (Ref source) in
            let+@ typ2 = internalize ctx (Ref (diff_ref_type source ty)) in
            (typ1, typ2)
        | _ ->
            Error.expected_ref ctx.diagnostics ~location:(snd i'.info);
            None
      in
      return_statement i
        (Br_on_cast
           ( label,
             ty,
             { i' with info = (Array.append types [| typ1 |], snd i'.info) } ))
        (Array.append
           (if bound then Array.sub params 0 (max 0 (Array.length params - 1))
            else types)
           [| typ2 |])
  | Br_on_cast_fail (label, ty, i') ->
      let* i' = instruction ctx i' in
      if is_cont_heaptype ctx ty.typ then
        Error.invalid_cast_type ctx.diagnostics ~location:i.info;
      let typ', types = split_on_last_type ctx ~location:(snd i'.info) i' in
      let*! ityp = reftype ctx.diagnostics ctx.type_context ty in
      (* [br_on_cast_fail] branches when the cast fails, carrying the residual
         type [typ2] ([ty'] minus [ty]) to the label; the fall-through (cast
         succeeded) carries the cast target [ty]. [typ1] re-types the operand as
         the lub of its type and [ty]. *)
      let*! typ1, typ2 =
        match Cell.get typ' with
        | Valtype { typ = Ref ty'; _ } ->
            (* [to_wasm] emits the source as [lub(ty, operand)] — widened so the
               target [ty] is a subtype of it — and wasm then derives the branch
               residual as [diff(source, ty)]. Type the residual from that same
               [lub] source, not the operand's own [ty']: otherwise, when the
               operand and target are unrelated (a chained cast whose source
               widens to their common supertype), the residual the typer feeds
               the label's join is narrower than the one the emitted instruction
               delivers, and the block infers too narrow to accept it. When
               [ty <: ty'] (a plain cast) the lub is [ty'] and this is unchanged.
               A failed [val_lub] means different hierarchies — an invalid cast;
               report it and recover with the cast target. *)
            let ty1 =
              match val_lub ctx (Ref ty) (Ref ty') with
              | Some t -> t
              | None ->
                  Error.invalid_cast ctx.diagnostics ~location:(snd i'.info)
                    typ';
                  Ref ty
            in
            let*@ typ1 = internalize ctx ty1 in
            let+@ typ2 =
              internalize ctx
                (match ty1 with
                | Ref lub -> Ref (diff_ref_type lub ty)
                | _ -> Ref (diff_ref_type ty' ty))
            in
            (typ1, typ2)
        (* A polymorphic operand: as for [br_on_cast] above, [to_wasm] recovers the
           source as the cast target [ty], so the residual sent to the branch is
           [ty \ ty] — a concrete reference matching the emitted instruction, not
           [Unknown] (the residual is always a reference) nor the bottom [UnknownRef]
           (a chained cast would then recover a mismatching source). *)
        | Unknown | UnknownRef ->
            let+@ typ2 = internalize ctx (Ref (diff_ref_type ty ty)) in
            (typ', typ2)
        | Error -> Some (typ', Cell.make Error)
        | Null ->
            (* A bare [null] operand, as in [br_on_cast] above: [to_wasm] emits
               the source as [ty] made nullable, so the residual sent to the
               branch is [diff(source, ty)] — mirroring wasm validation rather
               than the narrower [(ref none)] bottom, which would let programs
               through whose emitted wasm the validator rejects. *)
            let source = { ty with nullable = true } in
            let*@ typ1 = internalize ctx (Ref source) in
            let+@ typ2 = internalize ctx (Ref (diff_ref_type source ty)) in
            (typ1, typ2)
        | _ ->
            Error.expected_ref ctx.diagnostics ~location:(snd i'.info);
            None
      in
      let params = branch_target ctx label in
      let bound = label_in_scope ctx label in
      (* Unbound label: as in [Br_on_cast] above. *)
      if bound then
        check_subtypes ctx ~location:(snd i'.info)
          (Array.append types [| typ2 |])
          params;
      let typ =
        Cell.make
          (Valtype { typ = Ref ty; internal = Ref ityp; anon_comptype = None })
      in
      return_statement i
        (Br_on_cast_fail
           ( label,
             ty,
             { i' with info = (Array.append types [| typ1 |], snd i'.info) } ))
        (Array.append
           (if bound then Array.sub params 0 (max 0 (Array.length params - 1))
            else types)
           [| typ |])
  | Br_on_cast_desc_eq (label, nullable, i', d) ->
      (* As [br_on_cast]; the target [ty] is recovered from the descriptor
         operand [d] ([d : (ref null? (exact_1 Y))], [Y describes X] ⇒ target
         [(ref nullable (exact_1 X))]). Type the value before the descriptor, as
         they are evaluated and lowered ([to_wasm]) and as the sibling [CastDesc]
         arm does, so hole ordering and uninitialized-local tracking match. *)
      let* i' = typed ctx i' in
      let* d, target = descriptor_target ctx ~location:i.info ~nullable d in
      let*! ty = target in
      if is_cont_heaptype ctx ty.typ then
        Error.invalid_cast_type ctx.diagnostics ~location:i.info;
      let typ', types = split_on_last_type ctx ~location:(snd i'.info) i' in
      let params = branch_target ctx label in
      let bound = label_in_scope ctx label in
      (* Unbound label (already reported): no check against the [[||]]
         pseudo-params, and the fall-through keeps the below-values. *)
      (if bound then
         let>@ ityp = reftype ctx.diagnostics ctx.type_context ty in
         let typ =
           Cell.make
             (Valtype
                { typ = Ref ty; internal = Ref ityp; anon_comptype = None })
         in
         check_subtypes ctx ~location:(snd i'.info)
           (Array.append types [| typ |])
           params);
      let*! typ1, typ2 =
        match Cell.get typ' with
        | Valtype { typ = Ref ty'; _ } ->
            (* The operand keeps its own type [typ'] (the descriptor already fixes
               the target's exactness); [ty] and the operand must share a
               supertype — a failed [val_lub] means different hierarchies. *)
            if Option.is_none (val_lub ctx (Ref ty) (Ref ty')) then
              Error.invalid_cast ctx.diagnostics ~location:(snd i'.info) typ';
            let+@ typ2 = internalize ctx (Ref (diff_ref_type ty' ty)) in
            (typ', typ2)
        | Unknown | UnknownRef ->
            let+@ typ2 = internalize ctx (Ref (diff_ref_type ty ty)) in
            (typ', typ2)
        | Error -> Some (typ', Cell.make Error)
        | _ ->
            Error.expected_ref ctx.diagnostics ~location:(snd i'.info);
            None
      in
      return_statement i
        (Br_on_cast_desc_eq
           ( label,
             nullable,
             { i' with info = (Array.append types [| typ1 |], snd i'.info) },
             d ))
        (Array.append
           (Array.sub params 0 (max 0 (Array.length params - 1)))
           [| typ2 |])
  | Br_on_cast_desc_eq_fail (label, nullable, i', d) ->
      (* Type the value before the descriptor, matching evaluation/lowering order
         and the [Br_on_cast_desc_eq] arm above. *)
      let* i' = typed ctx i' in
      let* d, target = descriptor_target ctx ~location:i.info ~nullable d in
      let*! ty = target in
      if is_cont_heaptype ctx ty.typ then
        Error.invalid_cast_type ctx.diagnostics ~location:i.info;
      let typ', types = split_on_last_type ctx ~location:(snd i'.info) i' in
      let*! ityp = reftype ctx.diagnostics ctx.type_context ty in
      let*! typ1, typ2 =
        match Cell.get typ' with
        | Valtype { typ = Ref ty'; _ } ->
            (* See [Br_on_cast_desc_eq]. *)
            if Option.is_none (val_lub ctx (Ref ty) (Ref ty')) then
              Error.invalid_cast ctx.diagnostics ~location:(snd i'.info) typ';
            let+@ typ2 = internalize ctx (Ref (diff_ref_type ty' ty)) in
            (typ', typ2)
        | Unknown | UnknownRef ->
            let+@ typ2 = internalize ctx (Ref (diff_ref_type ty ty)) in
            (typ', typ2)
        | Error -> Some (typ', Cell.make Error)
        | _ ->
            Error.expected_ref ctx.diagnostics ~location:(snd i'.info);
            None
      in
      let params = branch_target ctx label in
      check_subtypes ctx ~location:(snd i'.info)
        (Array.append types [| typ2 |])
        params;
      let typ =
        Cell.make
          (Valtype { typ = Ref ty; internal = Ref ityp; anon_comptype = None })
      in
      return_statement i
        (Br_on_cast_desc_eq_fail
           ( label,
             nullable,
             { i' with info = (Array.append types [| typ1 |], snd i'.info) },
             d ))
        (Array.append
           (Array.sub params 0 (max 0 (Array.length params - 1)))
           [| typ |])
  | _ -> assert false (* only invoked on a branch instruction *)

and type_stack_switching ctx i =
  (* The typed-continuation / stack-switching instructions: cont.new, cont.bind,
     suspend, resume(.throw), and switch. Two surfaces reach here: the parsed
     method / constructor forms ([c.resume(x) on […]], [k::new(f)]) arrive as
     [Call]/[On] nodes routed from [call_instruction] / the dispatch and are
     resolved into the dedicated nodes below (their type immediates inferred
     from the receiver, on the call_ref model); the dedicated nodes themselves
     arrive when re-typing a decompiled module. The [finish_*] helpers hold the
     shared checks. *)
  match i.desc with
  | ContNew (ct, f) ->
      let* f' = instruction ctx f in
      finish_cont_new ctx i ct f'
  | ContBind (src, dst, l) ->
      let* l' = instructions ctx l in
      finish_cont_bind ctx i src dst l'
  | On (inner, handlers) -> type_on_clause ctx i inner handlers
  | _ -> type_stack_switching_ops ctx i

and finish_cont_new ctx i ct f' =
  (let>@ ft = lookup_cont_inner ctx ct in
   let>@ fref = internalize ctx (Ref { nullable = true; typ = Type ft }) in
   check_type ctx f' fref);
  (* [cont.new] allocates a fresh continuation of exactly [ct], so its result
     is an exact reference. As for [struct.new]/[array.new], we type it exact
     only under custom-descriptors (exact reference types are part of that
     proposal); the Wasm validator always tracks it exact internally. *)
  let want_exact =
    Wax_utils.Feature.is_enabled ctx.type_context.features
      Wax_utils.Feature.Custom_descriptors
  in
  let*! cref =
    internalize ctx
      (Ref
         { nullable = false; typ = (if want_exact then Exact ct else Type ct) })
  in
  return_expression i (ContNew (ct, f')) cref

and finish_cont_bind ctx i src dst l' =
  let*! src_inner = lookup_cont_inner ctx src in
  let*! src_sig = lookup_func_type ctx src_inner in
  let*! dst_inner = lookup_cont_inner ctx dst in
  let*! dst_sig = lookup_func_type ctx dst_inner in
  let np = Array.length src_sig.params - Array.length dst_sig.params in
  (* The destination continuation must be [src] with its leading [np]
         parameters bound away: the unbound tail and the results must match.
         Mirrors [Validation]'s [ContBind] check. *)
  (if np < 0 then
     Error.stack_switching_type_mismatch ctx.diagnostics ~location:i.info
       ~descr:
         "the resulting continuation takes more parameters than the original \
          one"
   else
     let>@ src_ft = internal_functype ctx src_sig in
     let>@ dst_ft = internal_functype ctx dst_sig in
     let ts12 = Array.sub src_ft.params np (Array.length dst_ft.params) in
     if
       not
         (functype_matches (subtyping_info ctx)
            { params = ts12; results = src_ft.results }
            dst_ft)
     then
       Error.stack_switching_type_mismatch ctx.diagnostics ~location:i.info
         ~descr:
           "the bound parameters and results do not match between the two \
            continuation types");
  (let n = max 0 np in
   let>@ bound =
     array_map_opt
       (fun p -> internalize ctx (param_type p))
       (Array.sub src_sig.params 0 n)
   in
   let>@ srcref = internalize ctx (Ref { nullable = true; typ = Type src }) in
   check_operands ctx ~location:i.info l' (Array.append bound [| srcref |]));
  (* Like [cont.new], [cont.bind] yields a fresh continuation of exactly
         [dst], so an exact reference (gated on custom-descriptors as above). *)
  let want_exact =
    Wax_utils.Feature.is_enabled ctx.type_context.features
      Wax_utils.Feature.Custom_descriptors
  in
  let*! dstref =
    internalize ctx
      (Ref
         {
           nullable = false;
           typ = (if want_exact then Exact dst else Type dst);
         })
  in
  return_expression i (ContBind (src, dst, l')) dstref

and type_stack_switching_ops ctx i =
  match i.desc with
  | Suspend (tag, l) ->
      (* Fill an omitted result of a block-construct operand from the tag's
         parameter types so it lowers like the annotated form — the resume-family
         materialization (see [type_cont_method_call]) applied to [suspend], whose
         tag is an immediate so no operand reordering is needed. *)
      let l =
        annotate_omitted_blocks l
          (cont_operand_source_types ctx ~meth:"suspend" ~tag:(Some tag) None)
      in
      let* l' = instructions ctx l in
      let*! { params; results } = Tbl.find ctx.diagnostics ctx.tags tag in
      (let>@ ptypes =
         array_map_opt (fun p -> internalize ctx (param_type p)) params
       in
       check_operands ctx ~location:i.info l' ptypes);
      let*! rtypes = array_map_opt (internalize ctx) results in
      return_statement i (Suspend (tag, l')) rtypes
  | Resume (ct, handlers, l) ->
      let* l' = instructions ctx l in
      finish_resume ctx i ct handlers l'
  | ResumeThrow (ct, tag, handlers, l) ->
      let* l' = instructions ctx l in
      finish_resume_throw ctx i ct tag handlers l'
  | ResumeThrowRef (ct, handlers, l) ->
      let* l' = instructions ctx l in
      finish_resume_throw_ref ctx i ct handlers l'
  | Switch (ct, tag, l) ->
      let* l' = instructions ctx l in
      finish_switch ctx i ct tag l'
  | _ -> assert false (* only invoked on a stack-switching instruction *)

and finish_resume ctx i ct handlers l' =
  let*! inner = lookup_cont_inner ctx ct in
  let*! sg = lookup_func_type ctx inner in
  (let>@ ptypes =
     array_map_opt (fun p -> internalize ctx (param_type p)) sg.params
   in
   let>@ cref = internalize ctx (Ref { nullable = true; typ = Type ct }) in
   check_operands ctx ~location:i.info l' (Array.append ptypes [| cref |]));
  check_resume_handlers ctx ~result_types:sg.results handlers;
  let*! rtypes = array_map_opt (internalize ctx) sg.results in
  return_statement i (Resume (ct, handlers, l')) rtypes

and finish_resume_throw ctx i ct tag handlers l' =
  let*! inner = lookup_cont_inner ctx ct in
  let*! sg = lookup_func_type ctx inner in
  let*! { params = tparams; _ } = Tbl.find ctx.diagnostics ctx.tags tag in
  (let>@ ptypes =
     array_map_opt (fun p -> internalize ctx (param_type p)) tparams
   in
   let>@ cref = internalize ctx (Ref { nullable = true; typ = Type ct }) in
   check_operands ctx ~location:i.info l' (Array.append ptypes [| cref |]));
  check_resume_handlers ctx ~result_types:sg.results handlers;
  let*! rtypes = array_map_opt (internalize ctx) sg.results in
  return_statement i (ResumeThrow (ct, tag, handlers, l')) rtypes

and finish_resume_throw_ref ctx i ct handlers l' =
  let*! inner = lookup_cont_inner ctx ct in
  let*! sg = lookup_func_type ctx inner in
  (let>@ exnref = internalize ctx (Ref { nullable = true; typ = Exn }) in
   let>@ cref = internalize ctx (Ref { nullable = true; typ = Type ct }) in
   check_operands ctx ~location:i.info l' [| exnref; cref |]);
  check_resume_handlers ctx ~result_types:sg.results handlers;
  let*! rtypes = array_map_opt (internalize ctx) sg.results in
  return_statement i (ResumeThrowRef (ct, handlers, l')) rtypes

and finish_switch ctx i ct tag l' =
  let*! inner = lookup_cont_inner ctx ct in
  let*! sg = lookup_func_type ctx inner in
  let tag_sig = Tbl.find ctx.diagnostics ctx.tags tag in
  let np = Array.length sg.params in
  (if np >= 1 then
     let>@ lead =
       array_map_opt
         (fun p -> internalize ctx (param_type p))
         (Array.sub sg.params 0 (np - 1))
     in
     let>@ cref = internalize ctx (Ref { nullable = true; typ = Type ct }) in
     check_operands ctx ~location:i.info l' (Array.append lead [| cref |]));
  (* The last parameter of [ct]'s function type must itself be a
         continuation type; the result is that inner continuation's parameter
         types. *)
  let inner_sg =
    match if np = 0 then None else Some (snd sg.params.(np - 1).desc) with
    | Some (Ref { typ = Type ct2 | Exact ct2; _ }) ->
        let*@ inner2 = lookup_cont_inner ctx ct2 in
        lookup_func_type ctx inner2
    | _ -> None
  in
  (* The 'switch' tag must take no parameters and its results must match
         both continuation types. Mirrors [Validation]'s [Switch] check. *)
  let to_internal arr =
    array_map_opt
      (fun typ ->
        let+@ iv = internalize_valtype ctx typ in
        iv.internal)
      arr
  in
  let result_subtype a b =
    match (to_internal a, to_internal b) with
    | Some a, Some b ->
        Array.length a = Array.length b
        && Array.for_all Fun.id
             (Array.mapi
                (fun i t ->
                  Wax_wasm.Types.val_subtype (subtyping_info ctx) t b.(i))
                a)
    | _ -> true
  in
  (match inner_sg with
  | None ->
      Error.stack_switching_type_mismatch ctx.diagnostics ~location:i.info
        ~descr:
          "the continuation's last parameter must itself be a continuation type"
  | Some inner_sg -> (
      match tag_sig with
      | None -> ()
      | Some { params = tparams; results = tresults } ->
          if
            Array.length tparams <> 0
            || (not (result_subtype sg.results tresults))
            || not (result_subtype tresults inner_sg.results)
          then
            Error.stack_switching_type_mismatch ctx.diagnostics ~location:i.info
              ~descr:
                "the 'switch' tag must take no parameters and its results must \
                 match the two continuation types"));
  let result_params =
    match inner_sg with Some s2 -> s2.params | None -> [||]
  in
  let*! rtypes =
    array_map_opt (fun p -> internalize ctx (param_type p)) result_params
  in
  return_statement i (Switch (ct, tag, l')) rtypes

(* The declared continuation type of a stack-switching receiver (or of
   [bind]'s continuation operand): the type immediate, inferred from the
   operand's static type on the call_ref model. An abstract [&cont] cannot
   supply it and must be cast to a declared type first, as an abstract
   function reference must be at a call. [None] after reporting. *)
and cont_operand_type ctx e' =
  match Cell.get (expression_type ctx e') with
  | Valtype { typ = Ref { typ = Type ct | Exact ct; _ }; _ } -> (
      match Tbl.find_opt ctx.type_context.types ct with
      | Some (_, { typ = Cont _; _ }) -> Some ct
      | _ ->
          Error.expected_cont_type ctx.diagnostics ~location:(snd e'.info);
          None)
  | Valtype { typ = Ref { typ = Cont | NoCont; _ }; _ } ->
      Error.abstract_cont_receiver ctx.diagnostics ~location:(snd e'.info);
      None
  | Error -> None (* the operand already failed to type; recover silently *)
  | Unknown | UnknownRef ->
      Error.unknown_operand_type ctx.diagnostics ~location:(snd e'.info);
      None
  | _ ->
      Error.expected_cont_type ctx.diagnostics ~location:(snd e'.info);
      None

(* The source types of a stack-switching call's value operands — everything
   preceding the receiver. Used to fill in an omitted result of a block-construct
   operand (see [annotate_omitted_block]) so it types exactly like the annotated
   form: [resume_throw_ref]'s single operand is always [exnref]; [resume_throw]'s
   come from the invoked tag; [resume]/[switch]'s from the receiver's continuation
   signature ([ct], from [cont_operand_type]). [None] (an unresolved receiver /
   tag, or a form that takes no anchoring operand) leaves the operands as written.
   Silent — [finish_*] re-derives and checks the internalized types and remains
   the sole reporter — so it uses the non-reporting [_opt] lookups. *)
and cont_func_params ctx ct =
  (* The parameters of continuation type [ct]'s underlying function type, looked
     up silently ([None] if [ct] is unresolved or not a continuation). *)
  let*@ _, sub = Tbl.find_opt ctx.type_context.types ct in
  match sub.typ with
  | Cont ft -> (
      match Tbl.find_opt ctx.type_context.types ft with
      | Some (_, { typ = Func f; _ }) -> Some f.params
      | _ -> None)
  | _ -> None

and cont_operand_source_types ctx ~meth ~tag ct : Ast.valtype array option =
  let cont_params () =
    let*@ ct = ct in
    cont_func_params ctx ct
  in
  match meth with
  | "resume_throw_ref" -> Some [| Ref { nullable = true; typ = Exn } |]
  | "resume_throw" | "suspend" ->
      (* Both take the invoked tag's parameters as their value operands. *)
      let*@ tag = tag in
      let+@ { params; _ } = Tbl.find_opt ctx.tags tag in
      Array.map (fun p -> param_type p) params
  | "resume" ->
      let+@ params = cont_params () in
      Array.map (fun p -> param_type p) params
  | "switch" ->
      let+@ params = cont_params () in
      let np = Array.length params in
      Array.map (fun p -> param_type p) (Array.sub params 0 (max 0 (np - 1)))
  | _ -> None

(* The types of the bound (leading) operands of a [cont.bind] from source
   continuation [src] to result [dst]: the first [|src| - |dst|] parameters of
   [src] (the ones bound away). Non-reporting — [finish_cont_bind] re-derives and
   checks these and stays the sole reporter — so a still-unresolved type, or a
   negative difference (a malformed bind [finish_cont_bind] will reject), yields
   [None] and leaves the operands as written. *)
and bind_bound_types ctx ~src ~dst =
  let*@ sp = cont_func_params ctx src in
  let*@ dp = cont_func_params ctx dst in
  let np = Array.length sp - Array.length dp in
  if np < 0 then None
  else Some (Array.map (fun p -> param_type p) (Array.sub sp 0 np))

(* Fill in an omitted result type of a block-construct operand from the type its
   consumer expects, so it types through the annotated block path (a concrete
   result flowing into the body — [type_block_construct]'s non-inference branch)
   rather than the checking / synthesis paths, which route a trailing nested
   block through an inferring cell and so never materialize the result its
   consumer needs. This is what makes an unannotated stack-switching operand
   ['h: do { … }] lower identically to the explicitly annotated ['h: do &?t { … }]
   (see the repros in the resume-family typers). Non-block operands and blocks
   whose result is already written are returned unchanged. *)
and annotate_omitted_block src (operand : location instr) : location instr =
  let fill typ =
    if typ.results = [||] then { typ with results = [| src |] } else typ
  in
  let desc =
    match operand.desc with
    | Block b -> Ast.Block { b with typ = fill b.typ }
    | Loop b -> Loop { b with typ = fill b.typ }
    | TryTable b -> TryTable { b with typ = fill b.typ }
    | Try b -> Try { b with typ = fill b.typ }
    | TryCatch b -> TryCatch { b with typ = fill b.typ }
    | If b -> If { b with typ = fill b.typ }
    | d -> d
  in
  { operand with desc }

(* Fill in each omitted block-construct operand's result from the expected
   operand types, when they are known and their count matches (a mismatched
   count is left for [finish_*] to report as an arity error). *)
and annotate_omitted_blocks args = function
  | Some srcs when Array.length srcs = List.length args ->
      List.mapi (fun k a -> annotate_omitted_block srcs.(k) a) args
  | _ -> args

(* A stack-switching method call [c.resume(x)], [c.resume_throw(exc(p))],
   [c.resume_throw_ref(e)], [c.switch(x, tag: t)], with [handlers] from a
   wrapping [on] clause. The receiver compiles last (Wasm stack order, as for
   call_ref), so the arguments are typed first and the receiver appended. *)
and type_cont_method_call ctx i ~handlers recv (meth : Ast.ident) args =
  (* [switch]'s enabling tag is a required labelled immediate, extracted before
     the arguments are typed (it names a tag, not a value); [resume_throw]'s
     tag is invoked with its payload, as in [throw exc(p)] — the callee is
     resolved in the tag namespace, so a function of the same name does not
     conflict. *)
  let tag, args =
    match meth.desc with
    | "switch" -> (
        let tags, rest =
          List.partition_map
            (fun a ->
              match a.Ast.desc with
              | Ast.Labelled ({ desc = "tag"; _ }, { desc = Get t; _ }) ->
                  Either.Left t
              | _ -> Either.Right a)
            args
        in
        match tags with
        | [ t ] -> (Some t, rest)
        | t :: dup :: _ ->
            Error.duplicate_argument_label ctx.diagnostics ~location:dup.info
              ~prev_loc:t.info { dup with desc = "tag" };
            (Some t, rest)
        | [] ->
            (* Anchor at the [switch] method, not the whole call expression: a
               chained [c.switch().switch()] would otherwise report this at the
               shared chain-start column twice — two genuine (each switch needs a
               tag), identically-rendered errors. *)
            Error.switch_needs_tag ctx.diagnostics ~location:meth.info;
            (None, rest))
    | "resume_throw" -> (
        match args with
        | [ { desc = Call ({ desc = Get t; _ }, payload); _ } ] ->
            (Some t, payload)
        | _ ->
            (* At the method, not the call expression: as for [switch_needs_tag]
               above, a chained [c.resume_throw().resume_throw()] would otherwise
               report this twice at the shared chain-start column. *)
            Error.resume_throw_needs_tag ctx.diagnostics ~location:meth.info;
            (None, args))
    | _ -> (None, args)
  in
  (* Emission order: the payload arguments, then the continuation receiver (on
     top), then the resume/switch. The receiver is TYPED first (out of emission
     order, made sound for the stack by the explicit hole slices and for the
     initialized-local analysis by [type_trailing_operand]) so its continuation
     signature supplies the value operands' expected types; an omitted result of
     a block-construct operand is then filled from that type so it lowers exactly
     like the annotated form ([annotate_omitted_blocks]). The operands are still
     typed in emission order over the front hole slice and the receiver is folded
     in last, exactly as [type_indirect_call] handles a callee. *)
  fun st ->
    let front_holes =
      List.fold_left (fun acc a -> acc + count_holes a) 0 args
    in
    let front_pending, tail_pending = list_split front_holes st.pending in
    let recv', replay =
      type_trailing_operand ctx (fun () ->
          let _, recv' =
            instruction ctx recv
              { pending = tail_pending; value_loc = None; reported = false }
          in
          recv')
    in
    let ct = cont_operand_type ctx recv' in
    let args =
      annotate_omitted_blocks args
        (cont_operand_source_types ctx ~meth:meth.desc ~tag ct)
    in
    let type_body =
      let* args' = instructions ctx args in
      let l' = args' @ [ recv' ] in
      let*! ct = ct in
      match meth.desc with
      | "resume" -> finish_resume ctx i ct handlers l'
      | "resume_throw" ->
          let*! tag = tag in
          finish_resume_throw ctx i ct tag handlers l'
      | "resume_throw_ref" -> finish_resume_throw_ref ctx i ct handlers l'
      | _ ->
          let*! tag = tag in
          finish_switch ctx i ct tag l'
    in
    let st1, node = type_body { st with pending = front_pending } in
    let st2 = fold_operand ctx recv' recv' { st1 with pending = [] } in
    replay ();
    (st2, node)

(* The postfix handler clause [e on [t -> 'l, …]]: fold the handlers into the
   resume-family call it wraps; any other wrapped expression is an error (the
   grammar attaches the clause to any expression). *)
and type_on_clause ctx i inner handlers =
  match inner.desc with
  | Call
      ( {
          desc =
            StructGet
              ( recv,
                ({ desc = "resume" | "resume_throw" | "resume_throw_ref"; _ } as
                 meth) );
          _;
        },
        args ) ->
      type_cont_method_call ctx i ~handlers recv meth args
  | _ ->
      Error.on_clause_context ctx.diagnostics ~location:i.info;
      (* Recover by typing the wrapped expression and carrying its result. *)
      let* inner' = instruction ctx inner in
      return_statement i (On (inner', handlers)) (fst inner'.info)

(* The [T::new] / [T::bind] constructors of a declared continuation type: the
   [T::] namespace constructs a [&T]. [bind]'s source type — the type
   immediate — is inferred from its continuation operand (the last argument),
   as the method receivers' types are. *)
and type_cont_construct_call ctx i func ns (name : Ast.ident) args =
  match (name.desc, List.rev args) with
  | "bind", cont_arg :: rev_bound ->
      (* [cont.bind]'s bound (leading) operands take their types from the SOURCE
         continuation, which is the last operand. Type it first (out of emission
         order, via the same hole-slice / [type_trailing_operand] / [fold_operand]
         machinery as [type_cont_method_call] / [type_indirect_call] — the
         emission order stays bound-operands then continuation) so its signature
         lets [annotate_omitted_blocks] fill an omitted block-operand result,
         exactly as for the resume family. *)
      let bound = List.rev rev_bound in
      fun st ->
        let front_holes =
          List.fold_left (fun acc a -> acc + count_holes a) 0 bound
        in
        let front_pending, tail_pending = list_split front_holes st.pending in
        let c', replay =
          type_trailing_operand ctx (fun () ->
              let _, c' =
                instruction ctx cont_arg
                  { pending = tail_pending; value_loc = None; reported = false }
              in
              c')
        in
        let src = cont_operand_type ctx c' in
        let bound =
          annotate_omitted_blocks bound
            (let*@ src = src in
             bind_bound_types ctx ~src ~dst:ns)
        in
        let type_body =
          let* bound' = instructions ctx bound in
          let*! src = src in
          finish_cont_bind ctx i src ns (bound' @ [ c' ])
        in
        let st1, node = type_body { st with pending = front_pending } in
        let st2 = fold_operand ctx c' c' { st1 with pending = [] } in
        replay ();
        (st2, node)
  | _ -> (
      let* args' = instructions ctx args in
      let recover () =
        return_statement i
          (Call
             ( {
                 desc = Path (ns, name);
                 info = ([||], func.info);
                 hints = Wax_wasm.Hints.none;
                 expected = Unset;
               },
               args' ))
          [| Cell.make Error |]
      in
      match name.desc with
      | "new" -> (
          match args' with
          | [ f' ] -> finish_cont_new ctx i ns f'
          | _ ->
              Error.operand_count_mismatch ctx.diagnostics ~location:func.info
                ~expected:1 ~provided:(List.length args');
              recover ())
      | "bind" ->
          (* Reached only with no operands — the with-operands case is handled
             above; [cont.bind] needs at least the continuation. *)
          Error.operand_count_mismatch ctx.diagnostics ~location:func.info
            ~expected:1 ~provided:0;
          recover ()
      | _ ->
          Error.unknown_intrinsic ctx.diagnostics ~location:func.info ns.desc
            name.desc;
          recover ())

and type_arith ctx i =
  (* Arithmetic, comparison and conversion operators in binary ([a + b]) and
     unary ([-a], [a as i64]) form. *)
  match i.desc with
  | BinOp (op, i1, i2) ->
      let* i1' = typed ctx i1 in
      let* i2' = typed ctx i2 in
      (* Snapshot BEFORE the arms below: they unify an [Error] operand cell onto
         the other operand's type (recovery), which erases the poison. *)
      let poisoned_operand =
        let poisoned c =
          match Cell.get (expression_type ctx c) with
          | Error -> true
          | _ -> false
        in
        poisoned i1' || poisoned i2'
      in
      let ty =
        let ty1 = expression_type ctx i1' in
        let ty2 = expression_type ctx i2' in
        let mismatch () =
          (* Point at the operator itself, not the whole expression. *)
          Error.binop_type_mismatch ctx.diagnostics ~location:op.info ty1 ty2
        in
        (* Split on how many operands are still abstract ([Unknown]/[Error]).
           Both abstract: unify the two cells to the operator's default type so a
           result is still produced. One abstract: unify it onto the known
           operand's type and validate that. Both concrete (the arms below):
           just validate. The abstract arms unify operand cells in place. *)
        match (Cell.get ty1, Cell.get ty2) with
        | (Unknown | Error), (Unknown | Error) -> (
            match op.desc with
            | Add | Sub | Mul ->
                Cell.merge ty1 ty2 Number;
                ty1
            | Div (Some _) | Rem _ | And | Or | Xor | Shl | Shr _ ->
                Cell.merge ty1 ty2 Int;
                ty1
            | Lt (Some _) | Gt (Some _) | Le (Some _) | Ge (Some _) | Eq | Ne ->
                Cell.merge ty1 ty2 (Valtype i32_valtype);
                i32_cell
            | Div None ->
                Cell.merge ty1 ty2 Float;
                ty1
            | Lt None | Gt None | Le None | Ge None ->
                Cell.merge ty1 ty2 (Valtype f32_valtype);
                i32_cell)
        | typ, (Unknown | Error) | (Unknown | Error), typ -> (
            Cell.merge ty1 ty2 typ;
            match op.desc with
            | Eq | Ne ->
                (* [==]/[!=] on references are both [ref.eq] (the latter negated
                   in lowering), so they take the same operands: [eqref] or a
                   number. *)
                (match typ with
                | Valtype { internal = Ref _ as ty; _ } ->
                    if
                      not
                        (Wax_wasm.Types.val_subtype (subtyping_info ctx) ty
                           (Ref { nullable = true; typ = Eq }))
                    then mismatch ()
                | Null ->
                    Cell.set ty1
                      (Valtype
                         {
                           typ = Ref { nullable = true; typ = Eq };
                           internal = Ref { nullable = true; typ = Eq };
                           anon_comptype = None;
                         })
                | Valtype { internal = I32; _ }
                | Valtype { internal = I64; _ }
                | Valtype { internal = F32; _ }
                | Valtype { internal = F64; _ }
                | Number | Int | LargeInt | Float ->
                    ()
                (* The bottom reference is [eqref], so [ref.eq] accepts it. *)
                | UnknownRef -> ()
                | _ -> mismatch ());
                i32_cell
            | Add | Sub | Mul ->
                (match typ with
                | Valtype { internal = I32; _ }
                | Valtype { internal = I64; _ }
                | Valtype { internal = F32; _ }
                | Valtype { internal = F64; _ }
                | Number | Int | LargeInt | Float ->
                    ()
                | _ -> mismatch ());
                ty1
            | Div (Some _) | Rem _ | And | Or | Xor | Shl | Shr _ ->
                check_int_bin_op ctx ~location:op.info ty1 ty2
            | Div None -> check_float_bin_op ctx ~location:op.info ty1 ty2
            | Lt (Some _) | Gt (Some _) | Le (Some _) | Ge (Some _) ->
                (match typ with
                | Valtype { internal = I32; _ }
                | Valtype { internal = I64; _ }
                | Int ->
                    ()
                | Number -> Cell.set ty1 Int
                (* A signed integer comparison forces a [LargeInt] operand to i64
                   (it cannot be i32, and this is an integer op), pinning it rather
                   than leaving it float-capable. *)
                | LargeInt -> Cell.set ty1 (Valtype i64_valtype)
                | _ -> mismatch ());
                i32_cell
            | Lt None | Gt None | Le None | Ge None ->
                (match typ with
                | Valtype { internal = F32; _ }
                | Valtype { internal = F64; _ }
                | Float ->
                    ()
                (* A float comparison takes a [LargeInt] operand as a float (it is
                   a numeric literal, so float-capable), like a [Number]. *)
                | Number | LargeInt -> Cell.set ty1 Float
                | _ -> mismatch ());
                i32_cell)
        | _ -> (
            match op.desc with
            | Eq | Ne ->
                (match (Cell.get ty1, Cell.get ty2) with
                | ( Valtype { internal = Ref _ as ty1; _ },
                    Valtype { internal = Ref _ as ty2; _ } ) ->
                    if
                      not
                        (Wax_wasm.Types.val_subtype (subtyping_info ctx) ty1
                           (Ref { nullable = true; typ = Eq })
                        && Wax_wasm.Types.val_subtype (subtyping_info ctx) ty2
                             (Ref { nullable = true; typ = Eq }))
                    then mismatch ()
                | Valtype { internal = Ref _ as typ1; _ }, Null ->
                    if
                      not
                        (Wax_wasm.Types.val_subtype (subtyping_info ctx) typ1
                           (Ref { nullable = true; typ = Eq }))
                    then mismatch ();
                    Cell.merge ty1 ty2 (Cell.get ty2)
                | Null, Valtype { internal = Ref _ as typ2; _ } ->
                    if
                      not
                        (Wax_wasm.Types.val_subtype (subtyping_info ctx) typ2
                           (Ref { nullable = true; typ = Eq }))
                    then mismatch ();
                    Cell.merge ty1 ty2 (Cell.get ty2)
                (* [ref.eq] needs both operands [eqref]; the bottom reference
                   [UnknownRef] always is, so only a concrete side is checked. *)
                | Valtype { internal = Ref _ as ty; _ }, UnknownRef
                | UnknownRef, Valtype { internal = Ref _ as ty; _ } ->
                    if
                      not
                        (Wax_wasm.Types.val_subtype (subtyping_info ctx) ty
                           (Ref { nullable = true; typ = Eq }))
                    then mismatch ()
                (* Two nulls compare as [ref.eq (ref.null none) (ref.null none)],
                   both bottom (hence [eqref]); accept them like the
                   bottom-reference cases rather than falling into the numeric
                   comparison below. *)
                | UnknownRef, (UnknownRef | Null) | Null, (UnknownRef | Null) ->
                    ()
                (* Any non-reference operands are the ordinary numeric comparison.
                   [check_num_concrete] reports the same mismatch otherwise. *)
                | _ -> check_num_concrete ctx ~location:op.info ty1 ty2);
                i32_cell
            | Add | Sub | Mul ->
                check_num_concrete ctx ~location:op.info ty1 ty2;
                ty1
            | Div (Some _) | Rem _ | And | Or | Xor | Shl | Shr _ ->
                check_int_bin_op ctx ~location:op.info ty1 ty2
            | Div None -> check_float_bin_op ctx ~location:op.info ty1 ty2
            | Lt (Some _) | Gt (Some _) | Le (Some _) | Ge (Some _) ->
                ignore (check_int_bin_op ctx ~location:op.info ty1 ty2);
                i32_cell
            | Lt None | Gt None | Le None | Ge None ->
                ignore (check_float_bin_op ctx ~location:op.info ty1 ty2);
                i32_cell)
      in
      if ctx.warn_unused then begin
        (* Deferred: the shift lint reads the operand width from [ty], which a
           later context can still widen (e.g. [1 << 40] pinned [i64]). *)
        ctx.deferred_lints :=
          (fun () -> Typing_lint.lint_shift ctx op ty i2')
          :: !(ctx.deferred_lints);
        Typing_lint.lint_division ctx op i2';
        Typing_lint.lint_comparison ctx op i1' i2';
        Typing_lint.lint_redundant ctx op i1' i2'
      end;
      (* An operand that already FAILED poisons the result. The arms above treat
         [Error] like [Unknown] on purpose — unifying it onto the other operand's
         type so the operand cells still get a usable recovery type — but the
         VALUE this produces is derived from a reported failure, so a consumer
         must not report about it again: without this, calling the result of
         [0x1p+1() - 1] said "Expected function" a second time, at the same start
         column as the inner call's own report (a duplicated diagnostic the
         mutation fuzzer caught). A callee, receiver or argument typed [Error] is
         absorbed silently, as it is for a failed call or cast. *)
      let ty = if poisoned_operand then Cell.make Error else ty in
      return_expression i (BinOp (op, i1', i2')) ty
  | UnOp (op, i') ->
      let* i' = instruction ctx i' in
      let typ = expression_type ctx i' in
      let ty =
        match Cell.get typ with
        | Error -> (
            match op.desc with Not -> i32_cell | Neg | Pos -> Cell.make Number)
        | Unknown -> (
            match op.desc with
            | Not -> i32_cell
            | Neg | Pos ->
                (* Unify the result with the operand's own cell (as the committed
                   case below and [Add]/[Sub]/[Mul] do), rather than handing back
                   a fresh [Number]. [-e] preserves width, so a later pin on the
                   result — e.g. an [as f64] promote consuming the negation of a
                   [select] of holes on the polymorphic dead-code stack — must pin
                   the operand too. A disconnected result cell lets the operand
                   stay [Unknown] (so [to_wasm] lowers it at the i32 default)
                   while the result is pinned to another width, an incoherent
                   negation that lowers to [i32.sub] annotated as that width. *)
                Cell.set typ Number;
                typ)
        | _ -> (
            match op.desc with
            | Not ->
                (match Cell.get typ with
                (* [!] is [i32.eqz] on an integer and [ref.is_null] on a
                   reference; [UnknownRef] is a (bottom) reference, so it takes
                   the [ref.is_null] reading like any other ref. *)
                | Valtype { internal = I32 | I64 | Ref _; _ }
                | Null | Int | UnknownRef ->
                    ()
                | Number -> Cell.set typ Int
                (* [!] on a [LargeInt] is [i64.eqz]; pin it to i64 so it cannot be
                   left float-capable (there is no float [eqz]). *)
                | LargeInt -> Cell.set typ (Valtype i64_valtype)
                | _ ->
                    Error.expression_type_mismatch ctx.diagnostics
                      ~location:(snd i'.info) ~provided:typ
                      ~expected:(Cell.make Int));
                i32_cell
            | Neg | Pos ->
                (match Cell.get typ with
                | Valtype { internal = I32 | I64 | F32 | F64; _ }
                | Int | LargeInt | Float | Number ->
                    ()
                | _ ->
                    Error.expression_type_mismatch ctx.diagnostics
                      ~location:(snd i'.info) ~provided:typ
                      ~expected:(Cell.make Number));
                typ)
      in
      if ctx.warn_unused then Typing_lint.lint_redundant_unop ctx op i';
      return_expression i (UnOp (op, i')) ty
  | _ -> assert false (* only invoked on BinOp/UnOp *)

and type_cast ctx i =
  (* Type casts ([e as t]) and type tests ([e is t]). *)
  match i.desc with
  | Cast (i', typ) ->
      (* An inner cast [(e as t) as u] that [simplify]/[--faithful] would drop as
         redundant, but which is load-bearing: dropping the NODE collapses the
         PRINTED form to [e as u], and a re-parse then re-defaults [e] and loses
         the instruction the double cast lowered to. Remember the inner cast's
         type [t] here (the only thing captured before the inner is typed — not its
         operand's shape, which may be a [select], a call, …); if the inner cast is
         dropped below, decide from the RESULT whether to re-ground it:

         - a NULL whose cast type differs from the expected outer type
           ([(null as &?any) as &?extern] and its mirror): the inner cast types the
           null as an anyref so the outer lowers to the cross-hierarchy
           [extern.convert_any]; dropped (a bare null satisfies any any-hierarchy
           consumer) it collapses to [null as &?extern] = [ref.null extern],
           dropping the convert. Per the rule "keep a null's cast when the expected
           type differs from the cast type": [is_null_initializer] on the RESULT is
           robust (a [select] etc. is not a null), and [t <> u] is the difference.

         - [f32.demote_f64] of a width-flexible float ([(sqrt() as f64) as f32]):
           the inner [as f64] pins the operand f64 so the outer [as f32] is a
           genuine demote; dropped as redundant (f64 IS the float re-parse
           default), the width-flexible operand re-defaults toward the outer [f32]
           and the demote collapses into an [f32.sqrt] (a precision change). A
           bare-literal result is excluded here: its demote is value-inert
           ([f64.const] then demote equals the [f32.const]). That exclusion is now
           inert in practice — the width reconciliation
           ({!reconcile_widths}) re-grounds such a literal from the width
           [From_wasm] recorded on it, so the inner cast comes back anyway and the
           demote round-trips exactly (which is the better answer: rounding a
           decimal once to f64 and then demoting is not always the f32 rounding of
           that decimal). *)
      let inner_cast_type =
        match i'.desc with Cast (_, t) -> Some t | _ -> None
      in
      let* i' = instruction ctx i' in
      (* The inner cast type to RE-INSERT if it was dropped below (i.e. the result
         is no longer a cast) and dropping it would lose the outer instruction. The
         wrap is applied at the final kept-cast return, NOT here, so it does not
         perturb the cast-fusion / redundancy logic in between. *)
      let restore_inner =
        (* [any] <-> [extern] are different hierarchies: a null cast to one, then
           cast to the other, is the cross-hierarchy [extern.convert_any] /
           [any.convert_extern] — dropping the inner would re-default the null and
           collapse the convert to a plain [ref.null]. A same-hierarchy "different
           type" null cast is instead a [ref.cast] (which [--faithful] does not
           compare and [simplify] legitimately prunes), so only the cross-hierarchy
           case is kept. *)
        let cross a b =
          match (top_heap_type ctx a, top_heap_type ctx b) with
          | Some Any, Some Extern | Some Extern, Some Any -> true
          | _ -> false
        in
        match inner_cast_type with
        | Some inner_t when match i'.desc with Cast _ -> false | _ -> true -> (
            match (inner_t, typ) with
            | ( Valtype (Ref { typ = inner_ht; _ }),
                Valtype (Ref { typ = outer_ht; _ }) )
              when reparse_adaptive i' && cross inner_ht outer_ht ->
                (* The operand re-parses type-adaptively (a null, a dead-code hole,
                   a [select]/[if] of adaptives): under the outer cast it would
                   take the extern/any hierarchy and collapse the convert into a
                   plain [ref.null], so keep the inner any/extern cast. The operand
                   is an anyref by validity, so this is always type-valid. An
                   anchored (concrete-ref) operand fixes the convert on its own and
                   is excluded, so the DEFAULT path is not perturbed with a
                   spurious pin; a wrongly-restored inner on such an operand would
                   be inert but noisy. *)
                Some inner_t
            | Valtype F64, Valtype F32 -> (
                match i'.desc with Int _ | Float _ -> None | _ -> Some inner_t)
            | _ -> None)
        | _ -> None
      in
      if ctx.warn_unused then
        Typing_lint.lint_conversion ctx ~location:i.info typ i';
      (* When converting from Wasm, fuse two casts whose inserted intermediate
         type is superfluous (only when [ctx.simplify]); [to_wasm] re-expands
         each single cast to the same instructions:
         - [(e as i32_X) as i64_X] -> [e as i64_X]: a narrow [i32]-producing
           read widened to [i64]. [e] is a packed [Int8]/[Int16] read (the
           [i32] is [i64.extend_i32_X]) or a reference (the [i32] is [i31.get],
           the [i64] [i64.extend_i32_X]).
         - [(e as &i31) as i32_X] -> [e as i32_X]: a [ref.cast] feeding
           [i31.get]. A reference already typed [&i31]/[&?i31] never reaches
           here (its [&i31] cast is dropped as redundant first); an [i31] built
           from an [i32] ([ref.i31]) is excluded by the [is_*_ref] guard.
         - [(e as i32) as &i31] -> [e as &i31]: an [i64] wrapped to [i32]
           before [ref.i31] (which takes an [i32]).
         - [(e as &any) as &T] -> [e as &T]: an [extern] converted to the
           [any] hierarchy ([any.convert_extern]) before a [ref.cast] to a
           concrete [any]-hierarchy type [T].
         - [(e as &i31) as &extern] -> [e as &extern]: an [i32] boxed as an
           [i31] ([ref.i31]) before [extern.convert_any]. *)
      let is_packed_read e =
        match Cell.get (expression_type ctx e) with
        | Int8 | Int16 -> true
        | _ -> false
      in
      let is_ref e =
        match Cell.get (expression_type ctx e) with
        | Valtype { internal = Ref _; _ } -> true
        | _ -> false
      in
      (* A non-[i31] reference in the [any] hierarchy — the operand of a plain
         [ref.cast] to [&i31]. [extern]/[noextern] are excluded: [e as &i31] for an
         [extern] is not a [ref.cast] but a cross-hierarchy convert then cast
         ([any.convert_extern]; [ref.cast]), so fusing it with a trailing [i31.get]
         into [e as i32] would leave an untranslatable [&extern as i32]. *)
      let is_non_i31_ref e =
        match Cell.get (expression_type ctx e) with
        | Valtype { internal = Ref { typ = I31 | Extern | NoExtern; _ }; _ } ->
            false
        | Valtype { internal = Ref _; _ } -> true
        | _ -> false
      in
      let is_i64 e =
        match Cell.get (expression_type ctx e) with
        | Valtype { internal = I64; _ } -> true
        | _ -> false
      in
      let is_i32 e =
        match Cell.get (expression_type ctx e) with
        | Valtype { internal = I32; _ } -> true
        | _ -> false
      in
      let is_extern e =
        match Cell.get (expression_type ctx e) with
        | Valtype { internal = Ref { typ = Extern | NoExtern; _ }; _ } -> true
        | _ -> false
      in
      let i', typ =
        match (typ, i'.desc) with
        | ( Signedtype { typ = `I64; signage = s2; strict = false },
            Cast (e, Signedtype { typ = `I32; signage = s1; strict = false }) )
          when ctx.simplify && s1 = s2 && (is_packed_read e || is_ref e) ->
            (e, typ)
        | ( Signedtype { typ = `I32; _ },
            Cast (e, Valtype (Ref { typ = I31; nullable = false })) )
          when ctx.simplify && is_non_i31_ref e ->
            (e, typ)
        | Valtype (Ref { typ = I31; nullable = false }), Cast (e, Valtype I32)
          when ctx.simplify && is_i64 e ->
            (e, typ)
        | ( Valtype (Ref ({ typ = Extern; _ } as r)),
            Cast (e, Valtype (Ref { typ = I31; nullable = false })) )
          when ctx.simplify && is_i32 e ->
            (* [ref.i31] is non-null and [extern.convert_any] preserves that,
               so the fused [i32 as &extern] is non-null. *)
            (e, Valtype (Ref { r with nullable = false }))
        | ( Valtype
              (Ref { typ = Any | Eq | I31 | Struct | Array | None_ | Type _; _ }),
            Cast (e, Valtype (Ref { typ = Any; _ })) )
          when ctx.simplify && is_extern e ->
            (e, typ)
        | _ -> (i', typ)
      in
      let ty' = expression_type ctx i' in
      (* Snapshot the inner type *before* [cast]/[signed_cast] below concretize it
         to the cast target: this is the type the inner expression would settle on
         if the cast were removed (see [load_bearing_literal]). *)
      let ty'_natural = Cell.get ty' in
      (* [extern.convert_any]/[any.convert_extern] preserve non-nullness, so a
         cast to [&?extern]/[&?any] of a non-nullable argument actually yields
         [&extern]/[&any]; refine the target accordingly. Like the
         redundant-cast removal below, this only applies when converting from
         Wasm ([ctx.simplify]); otherwise the cast is kept as written. *)
      let arg_non_nullable =
        match Cell.get ty' with
        | Valtype { typ = Ref { nullable = false; _ }; _ } -> true
        | _ -> false
      in
      let typ =
        match typ with
        | Valtype (Ref ({ typ = Extern | Any; nullable = true } as r))
          when ctx.simplify && arg_non_nullable ->
            Ast.Valtype (Ref { r with nullable = false })
        | _ -> typ
      in
      (* The cast target as a valtype, resolving an inline function type
         [&fn(..)] to a minted anonymous function type. The AST node keeps the
         original [typ] (so an inline function-type cast prints and lowers
         faithfully); only [ty]/validation use the resolved type. *)
      let target_valtype =
        match typ with
        | Valtype t -> Some t
        | Functype { nullable; sign } ->
            Some (Ref { nullable; typ = Type (anon_function_type ctx sign) })
        | Signedtype _ -> None
      in
      (* A continuation carries no RTT, so there is no [ref.cast] into a
         continuation type: [as &k] with a continuation target is a
         compile-time ascription, accepted (below) exactly when it lowers to
         no instruction. *)
      let cont_target =
        match target_valtype with
        | Some (Ref { typ; _ }) -> is_cont_heaptype ctx typ
        | _ -> false
      in
      (* An inline function-type cast target [&fn(..)] is lowered through a
         synthesized type (see [anon_function_type]); carry its signature so the
         result renders as [&fn(..)] rather than that synthetic name. *)
      let inline : comptype option =
        match typ with Functype { sign; _ } -> Some (Func sign) | _ -> None
      in
      let*! ty =
        internalize ?inline ctx
          (match target_valtype with
          | Some t -> t
          | None -> (
              match typ with
              | Signedtype { typ = `I32; _ } -> I32
              | Signedtype { typ = `I64; _ } -> I64
              | Signedtype { typ = `F32; _ } -> F32
              | Signedtype { typ = `F64; _ } -> F64
              | Valtype _ | Functype _ -> assert false))
      in
      let cast_failed =
        match target_valtype with
        | Some _ when cont_target ->
            (* Accepted exactly when it is a provable no-op — the cases
               [subtype] validates: the operand's static type is already a
               subtype of the target (identity or upcast, letting a [resume]
               go through a supertype signature), a [null] literal with a
               nullable target ([ref.null], no cast), or a stack-polymorphic
               operand (dead code, or an unconstrained inference cell the
               ascription pins). NOT the general [cast] castability check
               below, which admits runtime downcasts. *)
            if not (subtype ctx ty' ty) then
              Error.cont_cast_not_ascription ctx.diagnostics ~location:i.info;
            false
        | Some t ->
            if cast ctx ty' t then false
            else begin
              Error.invalid_cast ctx.diagnostics ~location:(snd i'.info) ty';
              true
            end
        | None -> (
            match typ with
            | Signedtype { typ = target; signage; _ } -> (
                (* An atomic narrow load has no sign-extending form (only the
                   zero-extending [_u] instructions exist), so reject [as iN_s]
                   on one outright — with the [_u]-then-extend spelling to use —
                   rather than quietly compiling a load + sign-extend pair. *)
                match (signage, target, atomic_narrow_load_width ctx i') with
                | Signed, ((`I32 | `I64) as t), Some w ->
                    Error.atomic_signed_load ctx.diagnostics ~location:i.info
                      ~cast:
                        ("as "
                        ^ (match t with `I32 -> "i32" | `I64 -> "i64")
                        ^ "_u")
                      ~extend:
                        (match w with
                        | `W8 -> ".extend8_s()"
                        | `W16 -> ".extend16_s()");
                    false
                | _ ->
                    if signed_cast ctx ty' target then false
                    else begin
                      Error.invalid_cast ctx.diagnostics ~location:(snd i'.info)
                        ty';
                      true
                    end)
            | Valtype _ | Functype _ -> assert false)
      in
      (* Poison the result of a failed cast (or one whose operand a prior failed
         cast already poisoned) with [Error]. A chain of casts each anchors its
         "cannot be cast" error at the shared leftmost operand location, so
         without this a single unlowerable operand reports one identical error
         per cast in the chain; [Error] is castable to anything ([cast] /
         [signed_cast] return [true] for it), so only the first failure is
         reported and the rest are absorbed. *)
      let poisoned =
        cast_failed || match ty'_natural with Error -> true | _ -> false
      in
      if poisoned then Cell.set ty Error;
      (* Lint the cast against its operand's natural type (snapshotted before
         [cast] above concretised it to the target). Skipped for from-Wasm input
         ([simplify]), whose casts are compiler-inserted and whose redundant ones
         are dropped below — and for a continuation target, whose "redundant"
         upcast is the intended use (a compile-time ascription). *)
      if ctx.warn_unused && (not ctx.simplify) && not cont_target then
        lint_ref_cast ~operand_location:(snd i'.info) ctx ~location:i.info
          ~is_test:false ty'_natural (Cell.get ty);
      (* A cast is load-bearing when its target differs from the type the inner
         expression would settle on if the cast were removed — its natural
         default, read from [ty'_natural] (the inner type *before* [cast] above
         concretized it to the target). A still-abstract numeric value re-parses
         at its default width (int -> i32, an out-of-i32-range int -> i64,
         float -> f64), so a cast to any other width must be kept or the value
         changes on the round-trip. This keeps e.g. [(nan as f32).to_bits()] /
         [(5 as i64).from_bits()] from losing the operand's type. Only an abstract
         numeric inner has such a default; a concrete inner (numeric or reference)
         is already pinned, so [subtype] below is the right redundancy test. *)
      let natural_typ =
        match ty'_natural with
        | Number | Int | Int8 | Int16 -> Some I32
        | LargeInt -> Some I64
        | Float -> Some F64
        | Null | UnknownRef | Valtype _ | Unknown | Error | Collecting _ -> None
      in
      let load_bearing_literal =
        match (natural_typ, Cell.get ty) with
        | Some d, Valtype { typ; _ } -> d <> typ
        | _ -> false
      in
      (* A cast on a tree of HOLES is load-bearing whatever its target, even when
         that target is the operand's own default width. The rule above reasons that
         a still-flexible operand "re-parses at its default", which holds for a
         literal tree — but a HOLE carries no value of its own: on a re-parse it
         re-connects to the value stranded above it, and what the two settle on is
         whatever the ENCLOSING context grounds them to. Dropping the cast hands
         that decision to the context: [(_ as f64).floor() as f32] without the
         [as f64] re-parses with the demote grounding the whole chain, i.e. as an
         [f32.floor] of an [f32.const] — the f64 operation AND its demote both lost
         (a wasm-smith round-trip finding, where an interposed [data.drop] made the
         receiver a hole). This cast is the only thing stating the type in the
         printed form, so it stays. *)
      let load_bearing_hole =
        match natural_typ with
        | Some _ -> defaulting_tree ~holes_only:true i'
        | None -> false
      in
      (* So is a cast whose operand is pending a width repair: [From_wasm]
         recorded a width for it ([Ast.instr]'s [expected]) that its own defaulting
         does not give, so {!reconcile_widths} will pin it — and the pin lands
         INSIDE this cast. Dropping the cast as a no-op (its operand having just
         folded to the target) would both lose the instruction it lowers to (the
         [i32.wrap_i64] of an unpinned [i64] tree) and leave the repair nowhere to
         attach. Never true on a decompile whose own pins are in place: the
         operand's recorded width is then the width it settles on. *)
      let operand_pin_pending =
        match (i'.expected, natural_typ) with
        | Ast.Recorded w, Some d -> w <> d
        | _ -> false
      in
      (* A cast of a bare [null] to a non-[any]-hierarchy reference is also load
         bearing: dropping it leaves a bare [null], whose non-null / branch
         consumers ([null!], [br_on_*]) fall back to the [any]-hierarchy bottom
         [&none] — not a subtype of a func/extern/exn/cont type — so the
         reconstructed module no longer type-checks. (An [any]-hierarchy null is
         safe to drop: [&none] satisfies every [any]-hierarchy consumer.) *)
      let load_bearing_null =
        match (ty'_natural, Cell.get ty) with
        | Null, Valtype { typ = Ref { typ = ht; _ }; _ } ->
            top_heap_type ctx ht <> Some Any
        | _ -> false
      in
      (* Likewise a cast of a bottom reference (the residual of a polymorphic
         [br_on_cast] in dead code, or [ref.null nofunc]) to a type the bottom
         cannot stand in for. The bottom heap type carries no usable type, so
         dropping the cast leaves a value that no longer names one: a [(ref
         nofunc)] feeding [call_ref] has no function type to resolve (any
         non-[any]-hierarchy target), and — even in the [any] hierarchy — a
         bottom [&none] feeding a struct/array field access ([s.f], [a[i]])
         names no concrete type for the field to resolve against (Wasm's
         [struct.get] carries the type index; Wax's [.f] recovers it from the
         receiver). An *abstract* [any]-hierarchy target ([any]/[eq]/[struct]/…)
         is still safe: [&none] satisfies those consumers. *)
      let load_bearing_bottom_ref =
        match (ty'_natural, Cell.get ty) with
        | ( Valtype { typ = Ref { typ = bot; _ }; _ },
            Valtype { typ = Ref { typ = ht; _ }; _ } )
          when is_bottom_heaptype bot && not (is_bottom_heaptype ht) -> (
            top_heap_type ctx ht <> Some Any
            || match ht with Type _ -> true | _ -> false)
        | _ -> false
      in
      (* A continuation-target ascription is load-bearing unless it names the
         operand's own type: [From_wasm] wraps every resume/switch/bind
         continuation operand in one to pin the instruction's type immediate,
         and dropping a strict upcast would re-infer the operand's own
         (narrower) type and change the immediate on the round trip. *)
      let load_bearing_cont =
        cont_target
        &&
        match (ty'_natural, Cell.get ty) with
        | ( Valtype { typ = Ref { typ = Type a | Exact a; _ }; _ },
            Valtype { typ = Ref { typ = Type b | Exact b; _ }; _ } ) ->
            a.desc <> b.desc
        | _ -> true
      in
      (* Drop a cast the inferred types already make redundant. This is only
         desirable when converting from Wasm ([ctx.simplify]): there casts are
         inserted to pin types and precise inference makes some unnecessary. For
         hand-written Wax (formatting, or compiling to Wasm) we keep casts as
         written.

         [--faithful] ([ctx.faithful]) keeps [simplify] off so a redundant
         *source* [ref.cast] survives and re-emits, but the decompiler also
         inserts type-pin SCAFFOLDING casts — a member-access receiver, a
         [call_ref] callee — that [simplify] would drop and that otherwise
         re-lower to a spurious [ref.cast] the original lacked. Those pins are
         nullable ([cast_ref] / the callee pin in [From_wasm] use
         [nullable = true]); a hand-visible redundant up-cast worth keeping is
         the non-null form ([ref.cast (ref any)] -> [_ as &any]). So under
         [--faithful] the drop still fires for a redundant cast to a NULLABLE ref
         target, pruning the common scaffolding, while a non-null redundant cast
         is kept. (Compiler-inserted pins and source casts cannot be told apart
         in general without provenance — see the [FAITHDRIFT] leg, which does not
         compare the cast family for this reason.) *)
      let target_nullable_ref =
        match Cell.get ty with
        | Valtype { typ = Ref { nullable = true; _ }; _ } -> true
        | _ -> false
      in
      let unnecessary_cast =
        (* A poisoned cast (it failed, or its operand was already poison) is
           never redundant, and its [ty] is now [Error] — a type that must not
           reach [subtype]'s expected side (whose right-hand assertion excludes
           it). This is only reachable on the from-Wasm paths: a hand-written
           cast is not simplified, and a failed one exits on the diagnostic. *)
        (not poisoned)
        && (ctx.simplify || (ctx.faithful && target_nullable_ref))
        && (not load_bearing_literal) && (not load_bearing_hole)
        && (not operand_pin_pending) && (not load_bearing_null)
        && (not load_bearing_bottom_ref)
        && (not load_bearing_cont)
        && (not (is_unknown_or_error ty'))
        && subtype ctx ty' ty
      in
      if unnecessary_cast then return { i' with info = ([| ty |], snd i'.info) }
      else
        (* Re-insert a dropped-but-load-bearing inner cast (see [restore_inner]):
           the outer cast is kept here, so wrap its operand back in the inner cast
           the drop removed, keeping the printed double cast. [i'] already carries
           the inner cast's (result) type in its [info], so the wrapper is
           consistent. *)
        let i' =
          match restore_inner with
          | Some inner_t -> { i' with desc = Cast (i', inner_t) }
          | None -> i'
        in
        return_expression i (Cast (i', typ)) ty
  | CastDesc (value, nullable, d) ->
      (* [value as [?]descriptor(d)]: a descriptor-equality cast. The target type
         is recovered from [d] ([d : (ref null? (exact_1 Y))], [Y describes X] ⇒
         target [(ref nullable (exact_1 X))]). The value is pushed first, the
         descriptor on top of it, so type them in that (emission) order. *)
      let* value' = typed ctx value in
      let* d', target = descriptor_target ctx ~location:i.info ~nullable d in
      let*! t = target in
      let*! ty = internalize ctx (Ref t) in
      let ty' = expression_type ctx value' in
      if not (cast ctx ty' (Ref t)) then
        Error.invalid_cast ctx.diagnostics ~location:(snd value'.info) ty';
      return_expression i (CastDesc (value', nullable, d')) ty
  | Test (operand, ty) ->
      let* i' = instruction ctx operand in
      if is_cont_heaptype ctx ty.typ then
        Error.invalid_cast_type ctx.diagnostics ~location:i.info;
      (* The operand's natural type, before the check below concretises it. *)
      let op_natural = Cell.get (expression_type ctx i') in
      (* Check the operand, and poison the result on failure (below), as the
         chained SIMD lane op does: [is] yields an [i32], so a chain
         [(x is &s) is &s] hands the outer [is] a non-reference operand of its
         own and — both anchored at the shared leftmost operand — reports an
         identical error at the same location. The innermost is the one to fix.
         An operand that is ALREADY poison satisfies the check silently and
         poisons the result too, so the chain stays quiet past its first link. *)
      let operand_ok =
        match
          let*@ typ = top_heap_type ctx ty.typ in
          internalize ctx (Ref { nullable = true; typ })
        with
        | Some typ ->
            let ty' = expression_type ctx i' in
            let ok = subtype ctx ty' typ in
            if not ok then
              Error.expression_type_mismatch ctx.diagnostics
                ~location:(snd i'.info) ~provided:ty' ~expected:typ;
            ok
        | None -> true
      in
      let poisoned =
        (not operand_ok) || match op_natural with Error -> true | _ -> false
      in
      (if ctx.warn_unused && not ctx.simplify then
         let>@ target = internalize ctx (Ref ty) in
         lint_ref_cast ~operand_location:(snd i'.info) ctx ~location:i.info
           ~is_test:true op_natural (Cell.get target));
      return_expression i
        (Test (i', ty))
        (if poisoned then Cell.make Error else i32_cell)
  (* Construction literals carry an optional type name that can be inferred from
     an expected type. Their typing lives in [check_instruction]; in synthesis position
     there is no expectation, so [check_instruction] against the [Unknown] sentinel keeps a
     present name and reports [cannot_infer_*] when one is omitted. *)
  | _ -> assert false (* only invoked on Cast/Test *)

and type_aggregate_access ctx i =
  (* Field and element access: struct field reads/writes ([s.f], [s.f = v]) and
     array or table indexing ([a[i]], [a[i] = v]). *)
  match i.desc with
  | StructGet (i', field) ->
      let* i' = instruction ctx i' in
      let*! ty =
        let ty = expression_type ctx i' in
        (* The receiver this access is on, for member completion: a memory /
           table name (that object's methods), else a numeric value (its
           methods). A reference receiver's struct fields / array [length] are
           recorded in the arms below. Only the receiver kind and type are
           recorded; the editor derives the candidate list on demand. *)
        (if ctx.member_completions <> None then
           match i'.desc with
           | Get name when memory_receiver ctx name ->
               let _, at = Option.get (Tbl.find_opt ctx.memories name) in
               record_members ctx.member_completions field.info
                 (Members.R_memory at)
           | Get name when table_receiver ctx name ->
               let at, rt = Option.get (Tbl.find_opt ctx.tables name) in
               record_members ctx.member_completions field.info
                 (Members.R_table (at, rt))
           | _ -> (
               match Members.numeric_receiver_kind (Cell.get ty) with
               | Some r -> record_members ctx.member_completions field.info r
               | None -> ()));
        match (Cell.get ty, field.desc) with
        | Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ }, _ -> (
            let*@ _, def = Tbl.find_opt ctx.type_context.types ty in
            match def.typ with
            | Struct fields -> (
                record_members ctx.member_completions field.info
                  (Members.R_struct fields);
                match
                  Array.find_map
                    (fun f ->
                      let nm = field_name f and typ = field_type f in
                      if nm.desc = field.desc then Some typ else None)
                    fields
                with
                | Some typ -> field_read_type ctx typ
                | None ->
                    Error.missing_field ctx.diagnostics ~location:field.info
                      field;
                    None)
            | Func _ | Array _ | Cont _ ->
                (match def.typ with
                | Array elem ->
                    record_members ctx.member_completions field.info
                      (Members.R_array elem)
                | Cont _ ->
                    if ctx.member_completions <> None then
                      record_members ctx.member_completions field.info
                        (cont_receiver ctx ty)
                | _ -> ());
                if is_unary_method field.desc then
                  Error.method_needs_parentheses ctx.diagnostics
                    ~location:field.info field.desc
                else
                  Error.expected_struct ctx.diagnostics ~location:(snd i'.info);
                None)
        (* Leave a receiver that already failed to type alone (its error is
           reported elsewhere): keep the access with an error result type rather
           than giving up, which would drop a hole receiver and desync hole
           counting. *)
        | Error, _ -> Some (Cell.make Error)
        (* The receiver's type is unknown (unreachable / branch code) or only a
           reference (its struct type cannot be resolved), so the field cannot
           be read. *)
        | (Unknown | UnknownRef), _ ->
            Error.unknown_operand_type ctx.diagnostics ~location:(snd i'.info);
            Some (Cell.make Error)
        (* A name that is an instruction method was likely meant as the
           parenthesised call [x.sqrt()]; any other field access on a non-struct
           type has no fields to find. *)
        | _ when is_unary_method field.desc ->
            Error.method_needs_parentheses ctx.diagnostics ~location:field.info
              field.desc;
            None
        | _ ->
            Error.expected_struct ctx.diagnostics ~location:(snd i'.info);
            None
      in
      return_expression i (StructGet (i', field)) ty
  | GetDescriptor i' ->
      let* i' = instruction ctx i' in
      let*! ty =
        match Cell.get (expression_type ctx i') with
        | Valtype { typ = Ref { typ = (Type ty | Exact ty) as ht; _ }; _ } -> (
            let exact = match ht with Exact _ -> true | _ -> false in
            let*@ _, def = Tbl.find_opt ctx.type_context.types ty in
            match def.descriptor with
            | None ->
                Error.type_without_descriptor ctx.diagnostics
                  ~location:(snd i'.info);
                None
            | Some descname ->
                internalize ctx
                  (Ref
                     {
                       nullable = false;
                       typ = (if exact then Exact descname else Type descname);
                     }))
        | Error -> Some (Cell.make Error)
        | Unknown | UnknownRef ->
            Error.unknown_operand_type ctx.diagnostics ~location:(snd i'.info);
            Some (Cell.make Error)
        | _ ->
            Error.expected_struct ctx.diagnostics ~location:(snd i'.info);
            None
      in
      return_expression i (GetDescriptor i') ty
  | StructSet (i1, field, i2) ->
      (* Emission order: the struct receiver, then the stored value. *)
      let* i1' = typed ctx i1 in
      (* Resolve the field's declared type (pure, reporting any field error)
         before typing the value, so the value can be checked against it and a
         struct/array literal can drop its name. The value is then typed on
         every path, so its holes are always consumed. *)
      let expected =
        match Cell.get (expression_type ctx i1') with
        | Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ } -> (
            match lookup_struct_type ctx ty with
            | None -> None
            | Some fields -> (
                record_members ctx.member_completions field.info
                  (Members.R_struct fields);
                match
                  Array.find_map
                    (fun f ->
                      let nm = field_name f in
                      if nm.desc = field.desc then Some (field_type f) else None)
                    fields
                with
                | None ->
                    Error.missing_field ctx.diagnostics ~location:field.info
                      field;
                    None
                | Some ftyp ->
                    if not ftyp.mut then
                      Error.immutable ctx.diagnostics ~location:field.info
                        "field";
                    internalize ctx (unpack_type ftyp)))
        | Error ->
            (* Receiver already failed to type; recover without a spurious
               "expected struct type". *)
            None
        | Unknown | UnknownRef ->
            (* The receiver's type is unknown (unreachable / branch code) or
               only a reference (its struct type cannot be resolved), so the
               field cannot be written. *)
            Error.unknown_operand_type ctx.diagnostics ~location:i1.info;
            None
        | _ ->
            Error.expected_struct ctx.diagnostics ~location:i1.info;
            None
      in
      let* i2' =
        match expected with
        | Some cell ->
            let* i2', _ = typed_check ctx cell i2 in
            return i2'
        | None -> typed ctx i2
      in
      return_statement i (StructSet (i1', field, i2')) [||]
  (* [tab[i]] on a table name is [table.get]; the receiver is not a value. *)
  | ArrayGet (({ desc = Get tabname; _ } as recv), i2)
    when table_receiver ctx tabname ->
      let at, rt = Option.get (Tbl.find_opt ctx.tables tabname) in
      let* i2' = instruction ctx i2 in
      check_type ctx i2' (address_cell at);
      let*! typ = internalize ctx (Ref rt) in
      return_expression i
        (ArrayGet
           ( {
               desc = Get tabname;
               info = ([||], recv.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             i2' ))
        typ
  | ArrayGet (i1, i2) -> (
      (* Emission order: the array, then the index. *)
      let* i1' = typed ctx i1 in
      let* i2' = typed ctx i2 in
      check_type ctx i2' i32_cell;
      match Cell.get (expression_type ctx i1') with
      | Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ } ->
          let*! typ = lookup_array_type ~location:i1.info ctx ty in
          let*! ty = field_read_type ctx typ in
          return_expression i (ArrayGet (i1', i2')) ty
      | Error ->
          (* Receiver already failed to type; recover silently. *)
          return_expression i (ArrayGet (i1', i2')) (Cell.make Error)
      | Unknown | UnknownRef ->
          (* The receiver's type is unknown (unreachable / branch code) or only
             a reference (its array type cannot be resolved), so the element
             cannot be read. *)
          Error.unknown_operand_type ctx.diagnostics ~location:i1.info;
          return_expression i (ArrayGet (i1', i2')) (Cell.make Error)
      | _ ->
          Error.expected_array ctx.diagnostics ~location:i1.info;
          return_expression i (ArrayGet (i1', i2')) (Cell.make Error))
  (* [tab[i] = v] on a table name is [table.set]; the receiver is not a value. *)
  | ArraySet (({ desc = Get tabname; _ } as recv), i2, i3)
    when table_receiver ctx tabname ->
      let at, rt = Option.get (Tbl.find_opt ctx.tables tabname) in
      (* The table name is a static immediate; the index then the value are the
         emitted operands. *)
      let* i2' = typed ctx i2 in
      check_type ctx i2' (address_cell at);
      (* Check the stored value against the table's element type, so a
         struct/array literal can drop its name. *)
      let* i3' =
        match internalize ctx (Ref rt) with
        | Some cell ->
            let* i3', _ = typed_check ctx cell i3 in
            return i3'
        | None -> typed ctx i3
      in
      return_statement i
        (ArraySet
           ( {
               desc = Get tabname;
               info = ([||], recv.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             i2',
             i3' ))
        [||]
  | ArraySet (i1, i2, i3) -> (
      (* Emission order: the array, the index, then the stored value. *)
      let* i1' = typed ctx i1 in
      let* i2' = typed ctx i2 in
      check_type ctx i2' i32_cell;
      match Cell.get (expression_type ctx i1') with
      | Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ } ->
          (* Resolve the element type (pure) before typing the value, so a
             struct/array literal value can drop its name. *)
          let expected =
            match lookup_array_type ~location:i1.info ctx ty with
            | None -> None
            | Some typ ->
                if not typ.mut then
                  Error.immutable ctx.diagnostics ~location:i1.info "array";
                internalize ctx (unpack_type typ)
          in
          let* i3' =
            match expected with
            | Some cell ->
                let* i3', _ = typed_check ctx cell i3 in
                return i3'
            | None -> typed ctx i3
          in
          return_statement i (ArraySet (i1', i2', i3')) [||]
      | Error ->
          (* Receiver already failed to type; recover silently (still type the
             value so its holes are consumed). *)
          let* i3' = typed ctx i3 in
          return_statement i (ArraySet (i1', i2', i3')) [||]
      | Unknown | UnknownRef ->
          (* The receiver's type is unknown (unreachable / branch code) or only
             a reference (its array type cannot be resolved), so the element
             cannot be written. Still type the value so its holes are
             consumed. *)
          let* i3' = typed ctx i3 in
          Error.unknown_operand_type ctx.diagnostics ~location:i1.info;
          return_statement i (ArraySet (i1', i2', i3')) [||]
      | _ ->
          let* i3' = typed ctx i3 in
          Error.expected_array ctx.diagnostics ~location:i1.info;
          return_statement i (ArraySet (i1', i2', i3')) [||])
  | _ -> assert false (* only invoked on a struct/array access *)

and type_variable_access ctx i =
  (* Reading and assigning a local or global: [x] ([Get]), [x = v] ([Set]) and
     the tee form [Tee] that also leaves the value on the stack. *)
  match i.desc with
  | Get idx as desc ->
      let ty =
        match resolve_variable ctx idx with
        | Local (ty, def) ->
            ctx.read_locals :=
              IntSet.add def.loc_start.pos_cnum !(ctx.read_locals);
            if not (StringSet.mem idx.desc ctx.initialized_locals) then
              report_uninitialized ctx idx;
            (* A poison local ([None]) reads as [Error] so its uses don't
               cascade. *)
            Cell.make (match ty with Some ity -> Valtype ity | None -> Error)
        | Global (_, ty) ->
            Cell.make (match ty with Some ity -> Valtype ity | None -> Error)
        | Func_ref (ty, ty', exact) ->
            let name = Ast.no_loc ty' in
            Cell.make
              (Valtype
                 {
                   typ =
                     Ref
                       {
                         nullable = false;
                         typ = (if exact then Exact name else Type name);
                       };
                   internal =
                     Ref
                       {
                         nullable = false;
                         typ = (if exact then Exact ty else Type ty);
                       };
                   anon_comptype = inline_comptype ctx name;
                 })
        | Poisoned ->
            (* Already reported at the definition; the Error poison keeps the
               use quiet. *)
            Cell.make Error
        | Unbound ->
            Error.unbound_name ctx.diagnostics ~location:idx.info
              ~suggestions:(get_suggestions ctx idx.desc)
              "variable" idx;
            Cell.make Error
      in
      return_expression i desc ty
  | Set (idx, op, i') ->
      (* Resolve the target first (a pure lookup) so the value can be checked
         against its type, letting a struct/array literal drop its name. The
         local is marked initialized only after the value is typed, so an
         assignment reading the same local (e.g. [x = x + 1]) still sees its
         pre-assignment state. *)
      let resolved = resolve_variable ctx idx in
      (* A compound assignment [x op= e] is type-checked as [x = x op e]: reading
         [x] requires it to be initialized already, and the operator is validated
         against its type by the ordinary [BinOp] path. The compound form is kept
         in the typed AST (so it round-trips and lowers back to a get/op/set); the
         typed right-hand side is the [BinOp]'s second operand. *)
      let to_check =
        match op with
        | None -> i'
        | Some op ->
            {
              i' with
              desc =
                BinOp
                  ( op,
                    {
                      desc = Get idx;
                      info = idx.info;
                      hints = Wax_wasm.Hints.none;
                      expected = Unset;
                    },
                    i' );
            }
      in
      let* checked =
        match resolved with
        | Local (Some ity, _) | Global (_, Some ity) ->
            let* c, _ = check_instruction ctx (valtype_cell ity) to_check in
            return c
        | Local (None, _) | Global (_, None) | Func_ref _ | Poisoned | Unbound
          ->
            instruction ctx to_check
      in
      let value =
        match (op, checked.desc) with
        | None, _ -> checked
        (* A numeric [BinOp] is never wrapped by [check_instruction], so its typed
           right operand is recoverable directly. *)
        | Some _, BinOp (_, _, rhs) -> rhs
        | Some _, _ -> assert false
      in
      (match resolved with
      | Local _ -> mark_initialized ctx idx.desc
      | Global (mut, _) ->
          if not mut then
            Error.immutable ctx.diagnostics ~location:idx.info "global"
          else
            (* The only place a global is written, so also where a [mut] global is
               recorded as actually assigned (for [unnecessary-mut]). *)
            Hashtbl.replace ctx.assigned_globals idx.desc ()
      | Func_ref _ ->
          Error.not_assignable ctx.diagnostics ~location:idx.info idx
      | Poisoned -> (* already reported at the definition *) ()
      | Unbound ->
          (* A compound assignment's desugared read (the [Get idx] injected
             into [to_check] above) already reported the unbound name at this
             same span; reporting the write too would duplicate it. *)
          if op = None then
            Error.unbound_name ctx.diagnostics ~location:idx.info
              ~suggestions:(set_suggestions ctx idx.desc)
              "variable" idx);
      (if ctx.suggest && op = None then
         match resolved with
         | Local _ | Global _ ->
             Typing_suggest.suggest_compound_assignment ctx ~location:i.info idx
               i'
         | Func_ref _ | Poisoned | Unbound -> ());
      return_statement i (Set (idx, op, value)) [||]
  | Tee (idx, i') -> (
      (* Only a local is assignable. Resolve it first so the value can be
         checked against the local's type (letting a struct/array literal drop
         its name); anything else is an error, after which we recover with the
         operand's own type rather than [Unknown], which [check_type] cannot
         match against. *)
      match resolve_variable ctx idx with
      | Local (Some ity, _) ->
          let typ = valtype_cell ity in
          let* i', _ = check_instruction ctx typ i' in
          mark_initialized ctx idx.desc;
          return_expression i (Tee (idx, i')) typ
      | Local (None, _) ->
          (* Poison local: recover with the operand's own type, no check. *)
          let* i' = instruction ctx i' in
          mark_initialized ctx idx.desc;
          return_expression i (Tee (idx, i')) (expression_type ctx i')
      | Global _ | Func_ref _ ->
          let* i' = instruction ctx i' in
          Error.not_assignable ctx.diagnostics ~location:idx.info idx;
          return_expression i (Tee (idx, i')) (expression_type ctx i')
      | Poisoned ->
          (* Already reported at the definition; recover like a poison local. *)
          let* i' = instruction ctx i' in
          return_expression i (Tee (idx, i')) (expression_type ctx i')
      | Unbound ->
          let* i' = instruction ctx i' in
          Error.unbound_name ctx.diagnostics ~location:idx.info
            ~suggestions:(local_suggestions ctx idx.desc)
            "variable" idx;
          return_expression i (Tee (idx, i')) (expression_type ctx i'))
  | _ -> assert false (* only invoked on Get/Set/Tee *)

and type_let ctx i =
  (* Let bindings: a single annotated binding, a multi-value binding, and a bare
     declaration ([let x: t;]). *)
  match i.desc with
  | Let ([ (name_opt, Some annot) ], Some i') -> (
      (* Bidirectional single annotated binding: type the initializer in
         checking mode against the annotation, so an omitted struct/array name
         is inferred from it; the keep-bool then says whether the annotation is
         load-bearing. Dropping a present annotation stays gated on [simplify]
         (Wasm->Wax), so hand-written Wax is never rewritten. A binding no later
         assignment writes is effectively immutable, so — like a [const] global
         — it also drops an annotation that is a mere supertype of the
         initializer's type ([drop_supertype]), narrowing to that subtype. *)
      match internalize_valtype ctx annot with
      | None ->
          let* i' = instruction ctx i' in
          return_statement i (Let ([ (name_opt, Some annot) ], Some i')) [||]
      | Some ity ->
          let drop_supertype =
            match name_opt with
            | Some name -> not (StringSet.mem name.desc ctx.assigned_locals)
            | None -> true
          in
          let* i', reinfer = check_instruction ctx (valtype_cell ity) i' in
          let needed =
            reinfer_needed ~drop_supertype ctx reinfer (valtype_cell ity)
          in
          Option.iter
            (fun name ->
              ctx.locals <-
                StringMap.add name.Annot.desc (Some ity, name.info) ctx.locals;
              ctx.local_decls := name :: !(ctx.local_decls);
              mark_initialized ctx name.desc)
            name_opt;
          let drop = ctx.simplify && not needed in
          (* The same redundancy, offered as a quick fix for hand-written Wax:
             delete the ': t', underlining just the type. The name's end anchors
             the deletion; for the anonymous [_: t = e] drop the name is the
             single-character [_] at the statement's start. *)
          (if ctx.suggest && not needed then
             let name_end =
               match name_opt with
               | Some name -> name.info.loc_end
               | None ->
                   {
                     i.info.loc_start with
                     pos_cnum = i.info.loc_start.pos_cnum + 1;
                   }
             in
             Typing_suggest.suggest_redundant_annotation ctx ~name_end
               ~boundary:(snd i'.info).loc_start);
          return_statement i
            (Let ([ (name_opt, if drop then None else Some annot) ], Some i'))
            [||])
  | Let (bindings, Some i') ->
      let* i' = instruction ctx i' in
      let bindings =
        match bindings with
        | [ binding ] ->
            (* Single binding: the initializer must be a one-value expression;
               [expression_type] reports it if it is not. A single binding with
               an annotation is handled by the branch above, so any annotation
               here is absent — no redundancy to suggest. *)
            [
              fst
                (bind_let_value ctx ~location:(snd i'.info)
                   (expression_type ctx i') binding);
            ]
        | _ ->
            (* Each name takes one value off a multi-value initializer, left to
               right (the names match the values in order). *)
            let result_types = fst i'.info in
            let n = List.length bindings in
            if Array.length result_types <> n then
              Error.value_count_mismatch ctx.diagnostics ~location:(snd i'.info)
                ~expected:n
                ~provided:(Array.length result_types);
            let src = Array.of_list bindings in
            List.mapi
              (fun idx binding ->
                let result_ty =
                  if idx < Array.length result_types then result_types.(idx)
                  else Cell.make Error
                in
                let binding', redundant =
                  bind_let_value ctx ~location:(snd i'.info) result_ty binding
                in
                (* Suggest dropping a redundant annotation in a tuple binding
                   ([let (a: t, b) = e] -> [let (a, b) = e]). The span after this
                   binding's type is the next binding's name (or, for the last,
                   the initializer); [annotation_spans] finds where the type ends
                   before that boundary. *)
                (if ctx.suggest && redundant then
                   match fst binding with
                   | Some name ->
                       let boundary =
                         if idx + 1 < n then
                           match fst src.(idx + 1) with
                           | Some nm -> Some nm.info.loc_start
                           | None -> None
                         else Some (snd i'.info).loc_start
                       in
                       Option.iter
                         (fun boundary ->
                           Typing_suggest.suggest_redundant_annotation ctx
                             ~name_end:name.info.loc_end ~boundary)
                         boundary
                   | None -> ());
                binding')
              bindings
      in
      return_statement i (Let (bindings, Some i')) [||]
  | Let (bindings, None) ->
      (* No initializer: each annotated name declares a local at its zero
         value; an unannotated name has no type to take and is left out. *)
      List.iter
        (fun (name, typ) ->
          match (name, typ) with
          | Some name, Some typ ->
              let>@ ity = internalize_valtype ctx typ in
              ctx.locals <-
                StringMap.add name.Annot.desc (Some ity, name.info) ctx.locals;
              ctx.local_decls := name :: !(ctx.local_decls);
              (* A defaultable local holds its zero value; a non-defaultable one
                 stays uninitialized until assigned. *)
              if is_defaultable typ then mark_initialized ctx name.desc
          | _ -> ())
        bindings;
      return_statement i (Let (bindings, None)) [||]
  | _ -> assert false (* only invoked on Let *)

and type_exception ctx i =
  (* Raising exceptions: [throw tag(..)] ([Throw]) and re-raising a caught
     exnref ([ThrowRef]). *)
  match i.desc with
  | Throw (tag, l) ->
      let* l' = instructions ctx l in
      (let>@ { params; results } = Tbl.find ctx.diagnostics ctx.tags tag in
       if results <> [||] then
         Error.tag_with_results ctx.diagnostics ~location:tag.info;
       let>@ types =
         array_map_opt (fun p -> internalize ctx (param_type p)) params
       in
       (* An argument may itself produce several values (a multi-result call),
          so check the flattened values against the tag's parameters, each at
          its own argument's location. *)
       let provided =
         List.concat_map
           (fun a ->
             List.map (fun ty -> (ty, snd a.info)) (Array.to_list (fst a.info)))
           l'
       in
       if List.length provided <> Array.length types then
         Error.operand_count_mismatch ctx.diagnostics ~location:tag.info
           ~expected:(Array.length types) ~provided:(List.length provided)
       else
         List.iteri
           (fun k (ty', location) -> check_subtype ctx ~location ty' types.(k))
           provided);
      return_statement i (Throw (tag, l')) [||]
  | ThrowRef i' ->
      let* i' = instruction ctx i' in
      (let>@ typ = internalize ctx (Ref { nullable = true; typ = Exn }) in
       check_type ctx i' typ);
      return_statement i (ThrowRef i') [||]
  | _ -> assert false (* only invoked on Throw/ThrowRef *)

and type_block_construct ctx i =
  (* The block-like control constructs (block, loop, while, if, dispatch, match,
     try, try_table), which type their bodies and results through the
     block-inference helpers. *)
  match i.desc with
  | Block { label; typ; block = { desc = instrs; _ } as blkloc } -> (
      (* An expression-position block draws nothing from a stack, so a parameter
         type has no source; report it, then recover by supplying the declared
         parameters anyway so the body does not underflow into spurious "stack
         empty" errors. (With no parameters this is the empty stack, unchanged.) *)
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      (* The block's value is consumed here, so it is value-producing: infer (and
         on [simplify] drop) its result type, admitting branches to its own
         label (unlike [if]). An omitted annotation is therefore always a dropped
         single result, never a void block. *)
      match block_inference ctx i label typ ~instrs:blkloc with
      | Some (desc, results) -> return_statement i desc results
      | None ->
          let*! params =
            array_map_opt (fun p -> internalize ctx (param_type p)) typ.params
          in
          let*! results = array_map_opt (internalize ctx) typ.results in
          let instrs' = block ctx i.info label params results results instrs in
          return_statement i
            (Block { label; typ; block = { blkloc with desc = instrs' } })
            results)
  | Dispatch { index; cases; default; arms } ->
      (* The case (arm) labels become distinct block labels in the lowering and
         key the arm bodies, so they must be distinct. *)
      let rec check_dups seen = function
        | [] -> ()
        | ((l : Ast.ident), _) :: r ->
            (match List.assoc_opt l.desc seen with
            | Some prev_loc ->
                Error.dispatch_duplicate_arm ctx.diagnostics ~location:l.info
                  ~prev_loc l
            | None -> ());
            check_dups ((l.desc, l.info) :: seen) r
      in
      check_dups [] arms;
      let index, _ =
        reject_control_holes ctx ~construct:"dispatch" ~role:"index"
          ~recovery:(Ast.Int "0") index
      in
      (* Type-check against the equivalent blocks (see [Ast_utils.lower_dispatch])
         as a void block body — the outermost case block followed by the first
         arm's trailing body. This validates the index is an [i32], every
         [br_table] target resolves to a 0-ary label, and each case body is
         well-typed. Then rebuild a typed [Dispatch], preserving the high-level
         form for the formatter and for the identical re-lowering in [To_wasm]. *)
      let lowered =
        Ast_utils.lower_dispatch ~block_info:i.info ~index ~cases ~default ~arms
      in
      (* In expression position the dispatch is checked in isolation (a void
         block body); a divergence in the trailing case body is propagated only
         in statement position — see [toplevel_instruction]. *)
      let typed = block ctx i.info None [||] [||] [||] lowered in
      let index', arms' = rebuild_dispatch typed arms in
      return_statement i
        (Dispatch { index = index'; cases; default; arms = arms' })
        [||]
  | Match { scrutinee; arms; default } ->
      (* Type-check against the nested type-test ladder (see
         [Ast_utils.lower_match]): the scrutinee is threaded once through a
         [br_on_cast]/[br_on_null] chain whose tests branch out to the arm
         blocks. The arm bodies must diverge (a block's result is supplied only
         on the matching-branch path); the lowered block check enforces this.
         Rebuild a typed [Match] for the formatter and the identical re-lowering
         in [To_wasm]. The scrutinee is threaded into the lowering and typed
         there (so a hole draws its type from the enclosing test); it is then
         recovered from the typed form rather than typed a second time. *)
      let scrutinee, scrut_had_holes =
        reject_control_holes ctx ~construct:"match" ~role:"scrutinee"
          ~recovery:Ast.Null scrutinee
      in
      let labels = match_labels i.info arms in
      let lowered =
        Ast_utils.lower_match ~block_info:i.info ~labels ~scrutinee ~arms
          ~default
      in
      let typed = block ctx i.info None [||] [||] [||] lowered in
      let arms', default', scrut_opt =
        (* On an erroneous scrutinee the typed lowering may not peel apart into
           the expected block nesting; recover with empty arm/default bodies (the
           module is already being rejected — the rebuilt node only feeds the
           formatter/editor) and type the scrutinee on its own, rather than
           crashing. *)
        try rebuild_match typed arms
        with Match_shape ->
          ( List.map
              (fun (pat, (orig : (_ instr list, location) Ast.annotated)) ->
                (pat, { orig with desc = [] }))
              arms,
            [],
            None )
      in
      let scrut' = match_recover_scrutinee ctx scrutinee scrut_opt in
      (* The chain's casts require a reference scrutinee; flag a non-reference
         here (the failed cast in the lowered form reports at the same spot).
         Skip it when the scrutinee was a rejected hole — the replacement
         [Unreachable] is not a reference and would cascade a spurious error. *)
      (if not scrut_had_holes then
         match match_scrut_reftype ctx scrut' with
         | Some _ -> ()
         | None ->
             Error.expected_ref ctx.diagnostics ~location:(snd scrut'.info));
      return_statement i
        (Match
           {
             scrutinee = scrut';
             arms = arms';
             default = { default with desc = default' };
           })
        [||]
  | Loop { label; typ; block = { desc = instrs; _ } as blkloc } -> (
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      match loop_inference ctx i label typ ~instrs:blkloc with
      | Some (desc, results) -> return_statement i desc results
      | None ->
          let*! params =
            array_map_opt (fun p -> internalize ctx (param_type p)) typ.params
          in
          let*! results = array_map_opt (internalize ctx) typ.results in
          let instrs' = block ctx i.info label params results params instrs in
          return_statement i
            (Loop { label; typ; block = { blkloc with desc = instrs' } })
            results)
  | While { label; cond; step; block = { desc = instrs; _ } as blkloc } ->
      (* Type-check the equivalent loop (see [Ast_utils.lower_while]): this
         validates that [cond] is an [i32], the continue-expression and body are
         well-typed, and — for a labelled step — that a [br] to the loop label
         (continue) runs the step. Then rebuild a typed [While], keeping the
         high-level form for the formatter and for the identical re-lowering in
         [To_wasm]. *)
      let cond, _ =
        reject_control_holes ctx ~construct:"while" ~role:"condition"
          ~recovery:(Ast.Int "0") cond
      in
      let lowered =
        Ast_utils.lower_while ~block_info:i.info
          ~fresh_loop:(Ast.no_loc Ast_utils.synthetic_loop_label)
          ~label ~cond ~step ~block:instrs
      in
      let typed = block ctx i.info None [||] [||] [||] lowered in
      let cond', step', instrs' =
        rebuild_while ~stepped:(step <> None) ~labelled:(label <> None) typed
      in
      return_statement i
        (While
           {
             label;
             cond = cond';
             step = step';
             block = { blkloc with desc = instrs' };
           })
        [||]
  | If { label; typ; cond; if_block; else_block } -> (
      let* cond' = instruction ctx cond in
      check_type ctx cond' i32_cell;
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      match if_inference ctx i label typ ~cond:cond' ~if_block ~else_block with
      | Some (desc, results) -> return_statement i desc results
      | None ->
          let*! params =
            array_map_opt (fun p -> internalize ctx (param_type p)) typ.params
          in
          let*! results = array_map_opt (internalize ctx) typ.results in
          let if_block' =
            {
              if_block with
              desc = block ctx i.info label params results results if_block.desc;
            }
          in
          let else_block' =
            match else_block with
            | Some b ->
                Some
                  {
                    b with
                    desc = block ctx i.info label params results results b.desc;
                  }
            | None ->
                if not (missing_else_ok ctx params results) then
                  Error.if_without_else ctx.diagnostics ~location:i.info;
                None
          in
          return_statement i
            (If
               {
                 label;
                 typ;
                 cond = cond';
                 if_block = if_block';
                 else_block = else_block';
               })
            results)
  | If_annotation { cond; then_body; else_body } ->
      (* Type each branch as an isolated block, under the branch's assumption so
         names resolve per branch (a name may be declared only in, or with a
         different type in, the matching configuration). *)
      let then_body' =
        {
          then_body with
          desc =
            with_cond ctx ~location:i.info cond true (fun () ->
                block ctx i.info None [||] [||] [||] then_body.desc);
        }
      in
      let else_body' =
        Option.map
          (fun b ->
            {
              b with
              Annot.desc =
                with_cond ctx ~location:i.info cond false (fun () ->
                    block ctx i.info None [||] [||] [||] b.Annot.desc);
            })
          else_body
      in
      return_statement i
        (If_annotation { cond; then_body = then_body'; else_body = else_body' })
        [||]
  | TryTable { label; typ; block = { desc = body; _ } as blkloc; catches } -> (
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      match trytable_inference ctx i label typ ~body:blkloc ~catches with
      | Some (desc, results) -> return_statement i desc results
      | None ->
          let*! params =
            array_map_opt
              (fun (p : (_, location) Ast.annotated) ->
                internalize ctx (snd p.desc))
              typ.params
          in
          let*! results = array_map_opt (internalize ctx) typ.results in
          let body' = block ctx i.info label params results results body in
          check_trytable_catches ctx catches;
          return_statement i
            (TryTable
               { label; typ; block = { blkloc with desc = body' }; catches })
            results)
  | TryCatch { label; typ; block = { desc = body; _ } as blkloc; arms } -> (
      (* The structured try (see [Ast_utils.lower_trycatch] for the lowering):
         the body's normal completion escapes past all arms (one implicit
         branch to the join, carrying the try's value); the arms are honest
         trailing code in clause order — arm [k] enters on its tag's payload
         (plus the [&exn] for a [&] arm) and its completion must be arm
         [k+1]'s entry, the last arm's the try's result. The label is the
         join, a block-like exit carrying the result. *)
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      match trycatch_inference ctx i label typ ~body:blkloc ~arms with
      | Some (desc, results) -> return_statement i desc results
      | None ->
          let*! results = array_map_opt (internalize ctx) typ.results in
          let body' = block ctx i.info label [||] results results body in
          let arms' = type_trycatch_arms ctx label ~results arms in
          return_statement i
            (TryCatch
               {
                 label;
                 typ;
                 block = { blkloc with desc = body' };
                 arms = arms';
               })
            results)
  | Try { label; typ; block = { desc = body; _ } as blkloc; catches; catch_all }
    -> (
      assert (typ.params = [||]);
      match try_inference ctx i label typ ~body:blkloc ~catches ~catch_all with
      | Some (desc, results) -> return_statement i desc results
      | None ->
          let*! results = array_map_opt (internalize ctx) typ.results in
          let body' = block ctx i.info label [||] results results body in
          let catches, catch_all =
            type_try_catches ctx label ~results catches catch_all
          in
          return_statement i
            (Try
               {
                 label;
                 typ;
                 block = { blkloc with desc = body' };
                 catches;
                 catch_all;
               })
            results)
  | _ -> assert false (* only invoked on a block-like construct *)

and type_mem_method_call ctx i func recv memname (meth : Ast.ident) args =
  let _, address_type = Option.get (Tbl.find_opt ctx.memories memname) in
  let addr_vt = address_cell address_type in
  let is_store = mem_store_method meth.desc in
  let nstack = if is_store then 2 else 1 in
  let* args' = mem_call_arguments ctx args in
  let positional, labelled = split_labelled_args ctx args' in
  let find = take_labels ctx ~allowed:[ "offset"; "align" ] labelled in
  let example =
    memname.desc ^ "." ^ meth.desc ^ "(..., offset: 16, align: 1)"
  in
  let _, align, offset =
    mem_immediates ctx ~location:i.info ~example ~nstack ~has_lane:false find
      positional
  in
  (match positional with
  | addr' :: rest -> (
      check_type ctx addr' addr_vt;
      if is_store then
        match rest with
        | value' :: _ -> (
            let vty = expression_type ctx value' in
            match meth.desc with
            | "store64" -> check_type ctx value' i64_cell
            | "storef32" -> check_type ctx value' f32_cell
            | "storef64" -> check_type ctx value' f64_cell
            | _ -> (
                match Cell.get vty with
                | Valtype { internal = I32 | I64; _ }
                | Int | Number | LargeInt | Unknown | Error ->
                    (* A narrowing store ([store8]/[store16]/[store32]) wraps, so
                       it also accepts an i64-wide value, including a [LargeInt]
                       literal too big for i32. *)
                    ()
                | _ ->
                    Error.expression_type_mismatch ctx.diagnostics
                      ~location:(snd value'.info) ~provided:vty
                      ~expected:(Cell.make Int)))
        | [] -> ())
  | [] -> ());
  check_memarg ctx ~address_type
    ~natural:(mem_natural_align meth.desc)
    ~align ~offset;
  let result =
    if is_store then [||]
    else
      match mem_load_result meth.desc with
      | Some t -> [| Cell.make t |]
      | None -> [||]
  in
  return_statement i
    (Call
       ( {
           desc =
             StructGet
               ( {
                   desc = Get memname;
                   info = ([||], recv.info);
                   hints = Wax_wasm.Hints.none;
                   expected = Unset;
                 },
                 meth );
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         args' ))
    result

and type_atomic_method_call ctx i func recv memname (meth : Ast.ident) family
    args =
  let module A = Wax_wasm.Atomics in
  let _, address_type = Option.get (Tbl.find_opt ctx.memories memname) in
  (* The address, then the value operands; then optional labelled immediates. *)
  let n_values =
    match family with
    | A.Load _ -> 0
    | A.Store _ | A.Notify -> 1
    | A.Rmw (Wax_wasm.Ast.AtomicCmpxchg, _) | A.Wait _ -> 2
    | A.Rmw _ -> 1
  in
  let nstack = 1 + n_values in
  let* args' = mem_call_arguments ctx args in
  let positional, labelled = split_labelled_args ctx args' in
  let find = take_labels ctx ~allowed:[ "offset"; "align" ] labelled in
  let example = memname.desc ^ "." ^ meth.desc ^ "(..., offset: 16)" in
  let _, align, offset =
    mem_immediates ctx ~location:i.info ~example ~nstack ~has_lane:false find
      positional
  in
  let rest =
    match positional with
    | addr' :: rest ->
        check_type ctx addr' (address_cell address_type);
        rest
    | [] -> []
  in
  (* The value operand of a narrow (8/16/32-bit) store or RMW picks the i32/i64
     family by its type, so it accepts either — pinned to the integer group,
     with a still-flexible literal defaulting to i32 as usual; the merged cell
     is the RMW's result (the returned old value). A 64-bit access is
     necessarily i64. An [Unknown] operand (a hole on the polymorphic dead-code
     stack) is pinned to the flexible [Int] rather than left [Unknown]: the RMW
     is a concrete op that [To_wasm] must emit, so an [Unknown] result — unlike a
     flexible literal tree — cannot be re-parsed at a cast's width and would drop
     the cast ([(m.atomic_rmw32(_, _) as i64_u)] losing its extend). As [Int] it
     defaults to i32 like any flexible integer, yet a consumer can still pin it to
     i64 (e.g. an i64 memory address), so both round-trip. [Error] (already
     reported) stays the untouched bottom. *)
  let check_value v =
    let vty = expression_type ctx v in
    match Cell.get vty with
    | Unknown ->
        Cell.set vty Int;
        vty
    | Error -> vty
    | _ -> check_int_bin_op ctx ~location:(snd v.info) vty (Cell.make Int)
  in
  let result =
    match family with
    | A.Load `W8 -> [| Cell.make Int8 |]
    | A.Load `W16 -> [| Cell.make Int16 |]
    | A.Load `W32 -> [| i32_cell |]
    | A.Load `W64 -> [| i64_cell |]
    | A.Store `W64 ->
        List.iter (fun v -> check_type ctx v i64_cell) rest;
        [||]
    | A.Store _ ->
        List.iter (fun v -> ignore (check_value v)) rest;
        [||]
    | A.Rmw (op, w) -> (
        match rest with
        | [] -> [| Cell.make Error |]
        | v :: more -> (
            match w with
            | `W64 ->
                List.iter (fun v -> check_type ctx v i64_cell) rest;
                [| i64_cell |]
            | _ ->
                let vty = check_value v in
                (match (op, more) with
                | Wax_wasm.Ast.AtomicCmpxchg, r :: _ -> (
                    (* The expected and replacement values must agree on the
                       family; merge their cells (as a binary operator does). *)
                    let rty = expression_type ctx r in
                    match (Cell.get vty, Cell.get rty) with
                    | (Unknown | Error), _ | _, (Unknown | Error) -> ()
                    | _ ->
                        ignore
                          (check_int_bin_op ctx ~location:(snd r.info) vty rty))
                | _ -> ());
                [| vty |]))
    | A.Wait t ->
        (match rest with
        | e :: more ->
            check_type ctx e
              (match t with `I32 -> i32_cell | `I64 -> i64_cell);
            List.iter (fun v -> check_type ctx v i64_cell) more
        | [] -> ());
        [| i32_cell |]
    | A.Notify ->
        List.iter (fun v -> check_type ctx v i32_cell) rest;
        [| i32_cell |]
  in
  let natural = A.family_bytes family in
  (* Only the offset immediate is range-checked here; an atomic access requires
     exactly its natural alignment (the access width from the name, independent
     of the i32/i64 family), not merely at most, so check that below. *)
  check_memarg ctx ~address_type ~natural ~align:None ~offset;
  (match align with
  | Some a -> (
      match int_literal a with
      | Some v
        when Wax_utils.Uint64.compare v (Wax_utils.Uint64.of_int natural) = 0 ->
          ()
      | _ ->
          Error.atomic_alignment ctx.diagnostics ~location:(snd a.info) natural)
  | None -> ());
  return_statement i
    (Call
       ( {
           desc =
             StructGet
               ( {
                   desc = Get memname;
                   info = ([||], recv.info);
                   hints = Wax_wasm.Hints.none;
                   expected = Unset;
                 },
                 meth );
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         args' ))
    result

and type_simd_mem_method_call ctx i func recv memname (meth : Ast.ident) args =
  let mop = Option.get (Simd.mem_method meth.desc) in
  let _, address_type = Option.get (Tbl.find_opt ctx.memories memname) in
  let addr_vt = address_cell address_type in
  let nstack = List.length mop.m_operands in
  let* args' = mem_call_arguments ctx args in
  let positional, labelled = split_labelled_args ctx args' in
  let allowed =
    if mop.m_lane then [ "lane"; "offset"; "align" ] else [ "offset"; "align" ]
  in
  let find = take_labels ctx ~allowed labelled in
  let example =
    memname.desc ^ "." ^ meth.desc
    ^ if mop.m_lane then "(..., lane: 0, offset: 16)" else "(..., offset: 16)"
  in
  let lane, align, offset =
    mem_immediates ctx ~location:i.info ~example ~nstack ~has_lane:mop.m_lane
      find positional
  in
  List.iteri
    (fun k a ->
      if k = 0 then check_type ctx a addr_vt
      else if k < nstack then
        check_type ctx a (simd_cell (List.nth mop.m_operands k)))
    positional;
  (if mop.m_lane then
     match lane with
     | None ->
         (* Only when the stack operands are exactly accounted for and no
            (possibly ill-formed, already reported) [lane:] was written: too
            few or extra positional arguments were reported just above, a
            non-constant lane payload by [take_labels]. *)
         if
           List.length positional = nstack
           && not
                (List.exists
                   (fun ((l : Ast.ident), _) -> l.desc = "lane")
                   labelled)
         then Error.missing_lane_immediate ctx.diagnostics ~location:meth.info
     | Some lane -> (
         let max_lane = 16 / mop.m_nat_align in
         (* Compare unsigned, and reject an [Ast.Int] too large even for [u64]
            ([int_literal] = [None]): otherwise it slips past this check and
            crashes [to_wasm]'s [int_of_string] (as for the SIMD lane index in
            [type_simd_method_call]). A non-constant lane is reported by
            [take_labels]. *)
         match lane.desc with
         | Ast.Int _ -> (
             match int_literal lane with
             | Some l
               when Wax_utils.Uint64.compare l
                      (Wax_utils.Uint64.of_int max_lane)
                    < 0 ->
                 ()
             | _ ->
                 Error.invalid_lane_index ctx.diagnostics
                   ~location:(snd lane.info) max_lane)
         | _ -> ()));
  check_memarg ctx ~address_type ~natural:mop.m_nat_align ~align ~offset;
  let result =
    match mop.m_result with Some t -> [| simd_cell t |] | None -> [||]
  in
  return_statement i
    (Call
       ( {
           desc =
             StructGet
               ( {
                   desc = Get memname;
                   info = ([||], recv.info);
                   hints = Wax_wasm.Hints.none;
                   expected = Unset;
                 },
                 meth );
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         args' ))
    result

and type_mem_mgmt_call ctx i func recv name (meth : Ast.ident) args =
  let _, at = Option.get (Tbl.find_opt ctx.memories name) in
  let addr () = address_cell at in
  let i32 () = i32_cell in
  let recv' =
    {
      desc = Get name;
      info = ([||], recv.info);
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  let mk args' =
    Ast.Call
      ( {
          desc = StructGet (recv', meth);
          info = ([||], func.info);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        },
        args' )
  in
  let bad () =
    Error.invalid_management_call ctx.diagnostics ~location:i.info meth.desc;
    (* The (method, args) form matched nothing, so the result type is unknown;
       recover with an [Error] value rather than [||] — some of these methods
       ([size], [grow]) produce a value, and claiming none would cascade into a
       spurious value-count error where the call is used as an expression. *)
    return_statement i (mk []) [| Cell.make Error |]
  in
  match (meth.desc, args) with
  | "size", [] -> return_expression i (mk []) (addr ())
  | "grow", [ d ] ->
      let* d' = instruction ctx d in
      check_type ctx d' (addr ());
      return_expression i (mk [ d' ]) (addr ())
  | "fill", [ d; v; n ] ->
      let* d' = instruction ctx d in
      let* v' = instruction ctx v in
      let* n' = instruction ctx n in
      check_type ctx d' (addr ());
      check_type ctx v' (i32 ());
      check_type ctx n' (addr ());
      return_statement i (mk [ d'; v'; n' ]) [||]
  | "copy", [ d; s; n ] ->
      let* d' = instruction ctx d in
      let* s' = instruction ctx s in
      let* n' = instruction ctx n in
      check_type ctx d' (addr ());
      check_type ctx s' (addr ());
      check_type ctx n' (addr ());
      return_statement i (mk [ d'; s'; n' ]) [||]
  | "copy", { desc = Get src; info = sinfo; _ } :: ([ _; _; _ ] as rest)
    when memory_receiver ctx src ->
      let src_at =
        match Tbl.find_opt ctx.memories src with Some (_, a) -> a | None -> at
      in
      let addr_of a = address_cell a in
      (* The length [n] indexes both the source and destination, so it is typed
         at the narrower of the two address types ([I32] if either is 32-bit). *)
      let min_at =
        match (at, src_at) with `I32, _ | _, `I32 -> `I32 | `I64, `I64 -> `I64
      in
      let src' =
        {
          desc = Get src;
          info = ([||], sinfo);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }
      in
      let* rest' = instructions ctx rest in
      (match rest' with
      | [ d'; s'; n' ] ->
          check_type ctx d' (addr_of at);
          check_type ctx s' (addr_of src_at);
          check_type ctx n' (addr_of min_at)
      | _ -> ());
      return_statement i (mk (src' :: rest')) [||]
  | "init", { desc = Get seg; info = sinfo; _ } :: ([ _; _; _ ] as rest) ->
      ignore (Tbl.find ctx.diagnostics ctx.datas seg : unit option);
      let seg' =
        {
          desc = Get seg;
          info = ([||], sinfo);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }
      in
      let* rest' = instructions ctx rest in
      (match rest' with
      | [ d'; s'; n' ] ->
          check_type ctx d' (addr ());
          check_type ctx s' (i32 ());
          check_type ctx n' (i32 ())
      | _ -> ());
      return_statement i (mk (seg' :: rest')) [||]
  | _ -> bad ()

and type_table_mgmt_call ctx i func recv name (meth : Ast.ident) args =
  let at, rt = Option.get (Tbl.find_opt ctx.tables name) in
  let addr () = address_cell at in
  let i32 () = i32_cell in
  let check_elt e =
    let>@ t = internalize ctx (Ref rt) in
    check_type ctx e t
  in
  let recv' =
    {
      desc = Get name;
      info = ([||], recv.info);
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  let mk args' =
    Ast.Call
      ( {
          desc = StructGet (recv', meth);
          info = ([||], func.info);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        },
        args' )
  in
  let bad () =
    Error.invalid_management_call ctx.diagnostics ~location:i.info meth.desc;
    (* The (method, args) form matched nothing, so the result type is unknown;
       recover with an [Error] value rather than [||] — some of these methods
       ([size], [grow]) produce a value, and claiming none would cascade into a
       spurious value-count error where the call is used as an expression. *)
    return_statement i (mk []) [| Cell.make Error |]
  in
  match (meth.desc, args) with
  | "size", [] -> return_expression i (mk []) (addr ())
  | "grow", [ v; n ] ->
      let* v' = instruction ctx v in
      let* n' = instruction ctx n in
      check_elt v';
      check_type ctx n' (addr ());
      return_expression i (mk [ v'; n' ]) (addr ())
  | "fill", [ d; v; n ] ->
      let* d' = instruction ctx d in
      let* v' = instruction ctx v in
      let* n' = instruction ctx n in
      check_type ctx d' (addr ());
      check_elt v';
      check_type ctx n' (addr ());
      return_statement i (mk [ d'; v'; n' ]) [||]
  | "copy", [ d; s; n ] ->
      let* d' = instruction ctx d in
      let* s' = instruction ctx s in
      let* n' = instruction ctx n in
      check_type ctx d' (addr ());
      check_type ctx s' (addr ());
      check_type ctx n' (addr ());
      return_statement i (mk [ d'; s'; n' ]) [||]
  | "copy", { desc = Get src; info = sinfo; _ } :: ([ _; _; _ ] as rest)
    when table_receiver ctx src ->
      let src_at =
        match Tbl.find_opt ctx.tables src with
        | Some (a, src_rt) ->
            check_elem_subtype ctx ~location:i.info ~src:src_rt ~dst:rt;
            a
        | None -> at
      in
      let addr_of a = address_cell a in
      (* The length [n] indexes both the source and destination, so it is typed
         at the narrower of the two address types ([I32] if either is 32-bit). *)
      let min_at =
        match (at, src_at) with `I32, _ | _, `I32 -> `I32 | `I64, `I64 -> `I64
      in
      let src' =
        {
          desc = Get src;
          info = ([||], sinfo);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }
      in
      let* rest' = instructions ctx rest in
      (match rest' with
      | [ d'; s'; n' ] ->
          check_type ctx d' (addr_of at);
          check_type ctx s' (addr_of src_at);
          check_type ctx n' (addr_of min_at)
      | _ -> ());
      return_statement i (mk (src' :: rest')) [||]
  | "init", { desc = Get seg; info = sinfo; _ } :: ([ _; _; _ ] as rest) ->
      (let>@ src_rt = Tbl.find ctx.diagnostics ctx.elems seg in
       check_elem_subtype ctx ~location:i.info ~src:src_rt ~dst:rt);
      let seg' =
        {
          desc = Get seg;
          info = ([||], sinfo);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }
      in
      let* rest' = instructions ctx rest in
      (match rest' with
      | [ d'; s'; n' ] ->
          check_type ctx d' (addr ());
          check_type ctx s' (i32 ());
          check_type ctx n' (i32 ())
      | _ -> ());
      return_statement i (mk (seg' :: rest')) [||]
  | _ -> bad ()

and type_array_fill_call ctx i func a (meth : Ast.ident) j v n =
  (* Emission order: the array receiver, then index, value, count. *)
  let* a' = typed ctx a in
  let* j' = typed ctx j in
  let* v' = typed ctx v in
  let* n' = typed ctx n in
  check_type ctx n' i32_cell;
  check_type ctx j' i32_cell;
  (match Cell.get (expression_type ctx a') with
  | Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ } ->
      let>@ typ = lookup_array_type ~location:a.info ctx ty in
      if not typ.mut then
        Error.immutable ctx.diagnostics ~location:a.info "array";
      let>@ ty = internalize ctx (unpack_type typ) in
      let ty' = expression_type ctx v' in
      if not (subtype ctx ty' ty) then
        Error.expression_type_mismatch ctx.diagnostics ~location:(snd v'.info)
          ~provided:ty' ~expected:ty
  | Error -> (* receiver already failed to type; recover silently *) ()
  | Unknown | UnknownRef ->
      (* The receiver's type is unknown (unreachable / branch code) or only a
         reference (its array type cannot be resolved), so the operation cannot
         be compiled. *)
      Error.unknown_operand_type ctx.diagnostics ~location:a.info
  | _ -> Error.expected_array ctx.diagnostics ~location:a.info);
  return_statement i
    (Call
       ( {
           desc = StructGet (a', meth);
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         [ j'; v'; n' ] ))
    [||]

and type_array_copy_call ctx i func a1 (meth : Ast.ident) i1 a2 i2 n =
  (* Emission order: dest array, dest index, src array, src index, count. *)
  let* a1' = typed ctx a1 in
  let* i1' = typed ctx i1 in
  let* a2' = typed ctx a2 in
  let* i2' = typed ctx i2 in
  let* n' = typed ctx n in
  check_type ctx n' i32_cell;
  check_type ctx i2' i32_cell;
  let ty' = expression_type ctx a2' in
  check_type ctx i1' i32_cell;
  let ty = expression_type ctx a1' in
  (match (Cell.get ty, Cell.get ty') with
  (* Either array already failed to type; recover silently. *)
  | Error, _ | _, Error -> ()
  (* An array's type is unknown (unreachable / branch code): its element type
     cannot be resolved, so the copy cannot be compiled. Point at the offending
     array. *)
  | (Unknown | UnknownRef), _ ->
      Error.unknown_operand_type ctx.diagnostics ~location:a1.info
  | _, (Unknown | UnknownRef) ->
      Error.unknown_operand_type ctx.diagnostics ~location:a2.info
  | ( Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ },
      Valtype { typ = Ref { typ = Type ty' | Exact ty'; _ }; _ } ) ->
      let>@ typ = lookup_array_type ~location:a1.info ctx ty in
      let>@ typ' = lookup_array_type ~location:a2.info ctx ty' in
      if not typ.mut then
        Error.immutable ctx.diagnostics ~location:a1.info "array";
      if not (storage_subtype ctx typ'.typ typ.typ) then
        Error.incompatible_array_elements ctx.diagnostics ~location:a2.info
  | _ -> Error.expected_array ctx.diagnostics ~location:a1.info);
  return_statement i
    (Call
       ( {
           desc = StructGet (a1', meth);
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         [ i1'; a2'; i2'; n' ] ))
    [||]

and type_array_init_call ctx i func a (meth : Ast.ident) arg1 rest =
  (* Emission order: the array receiver, then the dest/src/len operands (the
     segment [arg1] is a static immediate typed below). *)
  let* a' = typed ctx a in
  match arg1.desc with
  | Get seg ->
      let sinfo = arg1.info in
      let* rest' = instructions ctx rest in
      let i32 = i32_cell in
      (match rest' with
      | [ d'; s'; n' ] ->
          check_type ctx d' i32;
          check_type ctx s' i32;
          check_type ctx n' i32
      | _ -> ());
      (match Cell.get (expression_type ctx a') with
      | Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ } -> (
          let>@ field = lookup_array_type ~location:a.info ctx ty in
          if not field.mut then
            Error.immutable ctx.diagnostics ~location:a.info "array";
          match field.typ with
          | Value (Ref dst) ->
              let>@ src = Tbl.find ctx.diagnostics ctx.elems seg in
              check_elem_subtype ctx ~location:a.info ~src ~dst
          | _ -> ignore (Tbl.find ctx.diagnostics ctx.datas seg : unit option))
      | Error -> (* receiver already failed to type; recover silently *) ()
      | Unknown | UnknownRef ->
          (* The receiver's type is unknown (unreachable / branch code) or only
             a reference (its array type cannot be resolved), so the operation
             cannot be compiled. *)
          Error.unknown_operand_type ctx.diagnostics ~location:a.info
      | _ -> Error.expected_array ctx.diagnostics ~location:a.info);
      let seg' =
        {
          desc = Get seg;
          info = ([||], sinfo);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }
      in
      return_statement i
        (Call
           ( {
               desc = StructGet (a', meth);
               info = ([||], func.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             seg' :: rest' ))
        [||]
  | _ ->
      (* [array.init_data]/[array.init_elem] name a data or element segment as
         their first argument; the lowering requires that name, so anything else
         (a [null], a computed value) cannot be compiled. Type the arguments for
         recovery, then reject. *)
      let* args' = instructions ctx (arg1 :: rest) in
      (* Not when the RECEIVER is already poison: a failed call recovers with an
         [Error] value, so a chained [m.init(…).init(…)] would report the same
         rejection once per link — and, sharing the chain's start column, the
         reports render as one repeated [line:col: message]. The innermost
         failure is the one to fix; the rest follow from it. This is the poison
         convention the cast chain uses, read through the error-free
         [expression_type_opt] so the check itself reports nothing. *)
      (match Option.map Cell.get (Typing_env.expression_type_opt a') with
      | Some Error -> ()
      | _ ->
          Error.invalid_management_call ctx.diagnostics ~location:i.info
            meth.desc);
      return_statement i
        (Call
           ( {
               desc = StructGet (a', meth);
               info = ([||], func.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             args' ))
        [||]

(* An array bulk method ([fill]/[copy]/[init]) on an array receiver but with the
   wrong argument count — in practice the empty [a.fill()] an auto-closed call
   leaves while being typed. The exact-arity forms are handled above; this types
   the receiver and arguments and reports the arity, but keeps the method node so
   recovery and editor features (signature help) still see the call. Gated on an
   array receiver, so a struct field of the same name stays an indirect call. *)
and type_array_method_recovery ctx i func recv (meth : Ast.ident) args =
  let* recv' = typed ctx recv in
  let* args' = instructions ctx args in
  let expected = match meth.desc with "fill" -> 3 | _ -> 4 in
  if List.length args' <> expected then
    Error.operand_count_mismatch ctx.diagnostics ~location:func.info ~expected
      ~provided:(List.length args');
  return_statement i
    (Call
       ( {
           desc = StructGet (recv', meth);
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         args' ))
    [||]

and type_binary_intrinsic_call ctx i func i1 (meth : Ast.ident) op args =
  (* A scalar binary intrinsic on a value receiver ([x.min(y)]): the receiver is
     pushed first, then the operand. *)
  let* i1' = typed ctx i1 in
  let* args' = instructions ctx args in
  let is_int = match op with "rotl" | "rotr" -> true | _ -> false in
  let call args'' =
    Ast.Call
      ( {
          desc = StructGet (i1', meth);
          info = ([||], func.info);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        },
        args'' )
  in
  match args' with
  | [ i2' ] ->
      let ty1 = expression_type ctx i1' in
      let ty2 = expression_type ctx i2' in
      let check ty1 ty2 =
        if is_int then check_int_bin_op ctx ~location:meth.info ty1 ty2
        else check_float_bin_op ctx ~location:meth.info ty1 ty2
      in
      (* An abstract operand (a hole on the polymorphic stack of unreachable /
         branch code) is unified onto the other operand's type; two abstract
         operands take the operator's family default (int for [rotl]/[rotr],
         float for [copysign]/[min]/[max]). [check_int_bin_op]/
         [check_float_bin_op] leave the [Unknown]/[Error] arms to their caller,
         as the [BinOp] arms of [type_arith] do. *)
      let ty =
        match (Cell.get ty1, Cell.get ty2) with
        | (Unknown | Error), (Unknown | Error) ->
            Cell.merge ty1 ty2 (if is_int then Int else Float);
            ty1
        | (Unknown | Error), _ ->
            Cell.merge ty1 ty2 (Cell.get ty2);
            check ty1 ty2
        | _, (Unknown | Error) ->
            Cell.merge ty1 ty2 (Cell.get ty1);
            check ty1 ty2
        | _ -> check ty1 ty2
      in
      return_expression i (call [ i2' ]) ty
  | _ ->
      (* Wrong arity (e.g. the empty [x.min()] an auto-closed call being typed
         leaves): report it, but still produce the method node with the receiver
         typed — its result is the receiver's type — so recovery keeps the call
         (editor features like signature help see it). *)
      Error.operand_count_mismatch ctx.diagnostics ~location:func.info
        ~expected:1 ~provided:(List.length args');
      return_expression i (call args') (expression_type ctx i1')

and type_unary_intrinsic_call ctx i func recv (meth : Ast.ident) =
  let* recv' = instruction ctx recv in
  let*! ty =
    let ty = expression_type ctx recv' in
    match (Cell.get ty, meth.desc) with
    | Valtype { typ = Ref { typ = Type t | Exact t; _ }; _ }, "length" -> (
        let*@ _, def = Tbl.find_opt ctx.type_context.types t in
        match def.typ with
        | Array _ -> Some i32_cell
        | Struct _ | Func _ | Cont _ ->
            Error.expected_array ctx.diagnostics ~location:(snd recv'.info);
            None)
    (* [array.len] accepts any subtype of [(ref null array)]: the abstract
       array, a bare [null], and the bottom reference [&none] (which is below
       [array]). A concrete array is handled above. *)
    | (Null | Valtype { typ = Ref { typ = Array | None_; _ }; _ }), "length" ->
        Some i32_cell
    | Valtype { typ = I32; _ }, "from_bits" -> Some f32_cell
    | Valtype { typ = I64; _ }, "from_bits" -> Some f64_cell
    | Valtype { typ = F32; _ }, "to_bits" -> Some i32_cell
    | Valtype { typ = F64; _ }, "to_bits" -> Some i64_cell
    (* An abstract numeric receiver (e.g. a bare float literal whose redundant
       cast [simplify] dropped) defaults like any other operation: [to_bits] on a
       [Float] is f64->i64, [from_bits] on an integer is i32->f32 (or i64->f64
       for a [LargeInt]). The non-default widths keep their cast (load-bearing),
       so they reach the concrete arms above. A fully-polymorphic [Unknown]
       receiver (a value taken off the polymorphic stack of unreachable code) is
       resolved the same way: the method alone fixes the int/float family, so it
       defaults to that family's natural width rather than failing to compile.
       [to_bits] needs a float receiver, so an integer-valued float constant
       decompiled to a bare integer literal ([Number]/[LargeInt]) coerces to
       [f64] too (like the [LargeInt] coercion in a float binop). A receiver
       already committed to the integer family ([Int], e.g. the result of
       [clz]/[extend8_s]) is *not* coerced: [to_bits] on an integer is
       meaningless, and coercing its shared cell to [f64] would make the
       integer-producing operation below it lower against an [f64] operand. It
       falls through to the receiver-type error, mirroring [from_bits] rejecting
       a [Float] receiver. *)
    | (Float | Number | LargeInt | Unknown), "to_bits" ->
        Cell.set ty (Valtype f64_valtype);
        Some i64_cell
    | (Number | Int | Unknown), "from_bits" ->
        Cell.set ty (Valtype i32_valtype);
        Some f32_cell
    | LargeInt, "from_bits" ->
        Cell.set ty (Valtype i64_valtype);
        Some f64_cell
    | ( ((Number | Int | LargeInt | Unknown | Valtype { typ = I32 | I64; _ }) as
         ty'),
        ("clz" | "ctz" | "popcnt" | "extend8_s" | "extend16_s") ) ->
        if ty' = Number || ty' = Unknown then Cell.set ty Int
        else if ty' = LargeInt then Cell.set ty (Valtype i64_valtype);
        Some ty
    | ( ((Number | Float | Unknown | LargeInt | Valtype { typ = F32 | F64; _ })
         as ty'),
        ("abs" | "ceil" | "floor" | "trunc" | "nearest" | "sqrt") ) ->
        (* A [LargeInt] receiver is a float here (a float intrinsic), like a
           [Number]/[Unknown] one. *)
        if ty' = Number || ty' = Unknown || ty' = LargeInt then
          Cell.set ty Float;
        Some ty
    | Error, _ -> Some (Cell.make Error)
    | (Unknown | UnknownRef), _ ->
        (* The receiver is only a reference (its method cannot be resolved), or it
           is [Unknown] with a method that fixes no numeric family, so the call
           cannot be compiled. *)
        Error.unknown_operand_type ctx.diagnostics ~location:(snd recv'.info);
        Some (Cell.make Error)
    | _ ->
        Error.invalid_method_receiver ctx.diagnostics ~location:meth.info ty;
        None
  in
  return_expression i
    (Call
       ( {
           desc = StructGet (recv', meth);
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         [] ))
    ty

and type_simd_vector_op_call ctx i func recv (meth : Ast.ident) args =
  let op = Option.get (Simd.classify meth.desc) in
  let nimm = match op.imm with No_imm -> 0 | Lane _ -> 1 | Shuffle -> 16 in
  (* Emission order: the v128 (or scalar, for splat) receiver, then the trailing
     stack operands. The leading [nimm] lane immediates are static — not pushed,
     never holes — so type them plainly, between the two, without a hole slice or
     a hole-order contribution. *)
  let* recv' = typed ctx recv in
  let imms, stack_args = list_split nimm args in
  let* imms' = plain_instructions ctx imms in
  let* stack_args' = instructions ctx stack_args in
  let args' = imms' @ stack_args' in
  let nstack_extra = List.length op.operands - 1 in
  let nargs = List.length args' in
  if nargs <> nimm + nstack_extra then
    Error.operand_count_mismatch ctx.diagnostics ~location:func.info
      ~expected:(nimm + nstack_extra) ~provided:nargs;
  (* Check the receiver, and poison the result on failure (below). A chained
     lane op [x.extract_lane_i32x4(0).extract_lane_s_i16x8(7)] anchors each
     receiver mismatch at the shared leftmost operand, so without poisoning both
     the inner receiver (x) and the outer receiver (the inner call's result)
     report an identical error at the same location. *)
  let recv_ty = expression_type ctx recv' in
  let recv_expected = simd_cell (List.hd op.operands) in
  let recv_ok = subtype ctx recv_ty recv_expected in
  if not recv_ok then
    Error.expression_type_mismatch ctx.diagnostics ~location:(snd recv'.info)
      ~provided:recv_ty ~expected:recv_expected;
  let recv_poisoned =
    (not recv_ok) || match Cell.get recv_ty with Error -> true | _ -> false
  in
  let lane_bound =
    match op.imm with
    | No_imm -> None
    | Lane shape -> Some (Simd.lane_count shape)
    | Shuffle -> Some 32
  in
  List.iteri
    (fun k a ->
      if k < nimm then
        (* A lane immediate must be a constant integer in range. Unsigned
           compare, and reject an [Ast.Int] too large even for [u64]
           ([int_literal] = [None]) — otherwise it reaches [to_wasm]'s
           [int_of_string] and crashes (as for the memory lane index in
           [type_simd_mem_method_call]). *)
        match a.desc with
        | Ast.Int _ -> (
            let>@ bound = lane_bound in
            match int_literal a with
            | Some l
              when Wax_utils.Uint64.compare l (Wax_utils.Uint64.of_int bound)
                   < 0 ->
                ()
            | _ ->
                Error.invalid_lane_index ctx.diagnostics ~location:(snd a.info)
                  bound)
        | _ ->
            Error.integer_literal_required ctx.diagnostics
              ~location:(snd a.info)
      else
        let operand = 1 + (k - nimm) in
        if operand < List.length op.operands then
          check_type ctx a (simd_cell (List.nth op.operands operand)))
    args';
  let result =
    if recv_poisoned then [| Cell.make Error |]
    else match op.result with Some t -> [| simd_cell t |] | None -> [||]
  in
  return_statement i
    (Call
       ( {
           desc = StructGet (recv', meth);
           info = ([||], func.info);
           hints = Wax_wasm.Hints.none;
           expected = Unset;
         },
         args' ))
    result

and type_simd_free_intrinsic_call ctx i func ns (name : Ast.ident) args =
  let full = Simd.free_full name.desc in
  let callee =
    {
      desc = Path (ns, name);
      info = ([||], func.info);
      hints = Wax_wasm.Hints.none;
      expected = Unset;
    }
  in
  let* args' = instructions ctx args in
  if not (Simd.is_free_intrinsic full) then (
    Error.unknown_intrinsic ctx.diagnostics ~location:func.info ns.desc
      name.desc;
    return_expression i (Call (callee, args')) (Cell.make Error))
  else (
    (match Simd.const_shape_of_name full with
    | Some shape ->
        let arity = Simd.const_arity shape in
        if List.length args' <> arity then
          Error.operand_count_mismatch ctx.diagnostics ~location:func.info
            ~expected:arity ~provided:(List.length args');
        (* Each lane of an integer shape must fit its width, accepting both the
         signed and unsigned range [-2^(b-1), 2^b-1] (so an i8 lane is
         [-128, 255]). Beyond rejecting a malformed const, this stops an
         out-of-[int]-range literal from later crashing [V128.to_string]'s
         [int_of_string] in the binary encoder. *)
        let bits =
          match shape with
          | I8x16 -> Some 8
          | I16x8 -> Some 16
          | I32x4 -> Some 32
          | I64x2 -> Some 64
          | F32x4 | F64x2 -> None
        in
        List.iter
          (let lane_in_range b neg l =
             match int_literal l with
             | None -> false (* exceeds u64 *)
             | Some v ->
                 let v = Wax_utils.Uint64.to_int64 v in
                 if neg then
                   (* magnitude <= 2^(b-1) *)
                   Int64.unsigned_compare v (Int64.shift_left 1L (b - 1)) <= 0
                 else if b = 64 then true
                 else
                   Int64.unsigned_compare v
                     (Int64.sub (Int64.shift_left 1L b) 1L)
                   <= 0
           in
           fun a ->
             match (bits, a.desc) with
             | Some b, Ast.Int _ ->
                 if not (lane_in_range b false a) then
                   Error.lane_value_out_of_range ctx.diagnostics
                     ~location:(snd a.info) b
             | ( Some b,
                 Ast.UnOp ({ desc = Neg; _ }, ({ desc = Ast.Int _; _ } as l)) )
               ->
                 if not (lane_in_range b true l) then
                   Error.lane_value_out_of_range ctx.diagnostics
                     ~location:(snd a.info) b
             | ( Some b,
                 ( Ast.Float _
                 | Ast.UnOp ({ desc = Neg; _ }, { desc = Ast.Float _; _ }) ) )
               ->
                 (* a float literal is not a valid integer lane *)
                 Error.lane_value_out_of_range ctx.diagnostics
                   ~location:(snd a.info) b
             | ( None,
                 ( Ast.Int _ | Ast.Float _
                 | Ast.UnOp
                     ({ desc = Neg; _ }, { desc = Ast.Int _ | Ast.Float _; _ })
                   ) ) ->
                 () (* a float shape accepts any numeric literal lane *)
             | _ ->
                 Error.number_literal_required ctx.diagnostics
                   ~location:(snd a.info))
          args'
    | None ->
        (* The only non-const free intrinsic is [bitselect], which takes exactly
           three v128 operands; check its arity as the const branch checks
           theirs, so an under/over-application is rejected here rather than
           slipping through to an unrelated stack error during lowering. *)
        if List.length args' <> 3 then
          Error.operand_count_mismatch ctx.diagnostics ~location:func.info
            ~expected:3 ~provided:(List.length args');
        List.iter (fun a -> check_type ctx a (simd_cell TV128)) args');
    return_expression i (Call (callee, args')) (simd_cell TV128))

(* Bidirectional checking mode: type [i] against an [expected] type and report
   its {!reinfer} — what an unannotated binding would re-infer it to, standalone
   — so the binding/construct site can decide whether the annotation is
   load-bearing ([reinfer_needed]). A construction literal can fill an omitted
   type name from [expected] and shed a redundant one; every other expression
   delegates to [instruction] and snapshots its own type. [expected] is the
   [Unknown] sentinel when [check_instruction] is entered from [instruction] with
   no context (synthesis). *)
and check_instruction ctx expected (i : location instr) =
  (* The construction's type name: explicit, or inferred from an exact expected
     type; [missing] reports a [cannot_infer_*] error and yields [None]. *)
  let resolve_name ty ~missing =
    match ty with
    | Some _ -> ty
    | None -> (
        match exact_named_type expected with
        | Some name -> Some name
        | None ->
            missing ();
            None)
  in
  (* The name is redundant precisely when [expected] pins the identical heap
     type, so it can be dropped (and is, on output). *)
  let name_redundant name =
    match exact_named_type expected with
    | Some n -> n.desc = name.Annot.desc
    | None -> false
  in
  (* The type name to emit for a construction whose source name was [original]
     and whose resolved name is [typ]. A name omitted in the source stays
     omitted. A present name is dropped only when converting from Wasm
     ([simplify], so hand-written Wax is never rewritten) and the expected type
     makes it redundant (or the fields alone pin the type). *)
  let emitted_name original typ ~field_unique =
    match original with
    | None -> None
    | Some name ->
        let redundant = name_redundant typ || field_unique in
        if ctx.simplify && redundant then None
        else begin
          if ctx.suggest && redundant then
            Typing_suggest.suggest_drop_type_name ctx name;
          Some typ
        end
  in
  (* The result reference type of a construction of [name]; validates it against
     [expected] when there is one. *)
  let construction_result name =
    (* A concrete allocator ([struct.new] / [array.new*]) yields an *exact*
       reference at the Wasm level. We type it exact only when custom-descriptors
       is enabled (exact reference types are part of that proposal); otherwise it
       is the plain inexact reference, as before the proposal. *)
    let want_exact =
      Wax_utils.Feature.is_enabled ctx.type_context.features
        Wax_utils.Feature.Custom_descriptors
    in
    let result =
      internalize ?inline:(inline_comptype ctx name) ctx
        (Ref
           {
             nullable = false;
             typ = (if want_exact then Exact name else Type name);
           })
    in
    Option.iter
      (fun result ->
        if has_expectation expected then
          check_subtype ctx ~location:i.info result expected)
      result;
    result
  in
  (* A type carrying a [descriptor] clause must be allocated with a descriptor
     ([{descriptor(d) | …}]), not a plain [{T | …}]. *)
  let require_no_descriptor typ =
    match Tbl.find_opt ctx.type_context.types typ with
    | Some (_, def) when Option.is_some def.descriptor ->
        Error.descriptor_allocation_required ctx.diagnostics ~location:i.info
    | _ -> ()
  in
  (* The re-inference of a construction node (array / default struct /
     descriptor construction). It re-infers to its own result standalone when its
     output still names the type — an emitted array/struct-default *name*, or a
     descriptor construction whose descriptor [d] pins the type. A name-less form
     (the name dropped as redundant, or absent, and no descriptor) cannot
     re-infer without the context, so it is [Uninferrable]. A name-carrying array
     or struct-default is [Named] (its written name, which a mere-supertype
     annotation does not pin, is load-bearing for round-trip stability, so the
     annotation drops only on exact equality); a descriptor construction, which
     re-infers structurally through [d] with no written name, is a narrowable
     [Typ]. The [Struct] arm computes its own re-inference inline (field-unique,
     hence structural and narrowable). *)
  let construction_reinfer node =
    let named =
      match node.desc with
      | Array (name, _, _)
      | ArrayDefault (name, _)
      | ArrayFixed (name, _)
      | ArraySegment (name, _, _, _)
      | StructDefault name ->
          Option.is_some name
      | _ -> false
    in
    match standalone_valtype ctx (expression_type ctx node) with
    | Some _ when named -> named_reinfer_of_cell (expression_type ctx node)
    | Some _ -> (
        match node.desc with
        | StructDesc _ | StructDefaultDesc _ ->
            reinfer_of_cell (expression_type ctx node)
        | _ -> Uninferrable)
    | None -> Uninferrable
  in
  match i.desc with
  | Struct (ty, fields) ->
      if ctx.suggest then
        List.iter
          (fun (name, written) ->
            Typing_suggest.suggest_punning ctx name written)
          fields;
      (* The unique struct type these fields name, if any: used to resolve an
         omitted name and to drop a present one that the fields already pin. *)
      let field_match = infer_struct_by_fields ctx fields in
      let* node =
        match
          match ty with
          | Some _ -> ty
          | None -> (
              (* Field inference takes precedence over the expected type: the
                 fields name the exact struct constructed, whereas [expected]
                 may be a supertype. Fall back to [expected] only when the
                 fields are ambiguous. *)
              match field_match with
              | Some name -> Some name
              | None -> (
                  match exact_named_type expected with
                  | Some name -> Some name
                  | None ->
                      Error.cannot_infer_struct_type ctx.diagnostics
                        ~location:i.info;
                      None))
        with
        | None ->
            (* Unresolved: still type the field values for error recovery (and
               so they consume their stack slots / holes), then recover with an
               [Error] result. *)
            let* fields' =
              List.fold_left
                (fun prev ((name : Ast.ident), written) ->
                  let* l = prev in
                  if written = None then record_pun ctx.pun_spans name.info;
                  let* fi' = typed ctx (field_value name written) in
                  return ((name, Option.map (fun _ -> fi') written) :: l))
                (return []) fields
            in
            return_expression i
              (Struct (None, List.rev fields'))
              (Cell.make Error)
        | Some typ ->
            require_no_descriptor typ;
            let*! field_types = lookup_struct_type ctx typ in
            if List.length fields > Array.length field_types then
              Error.field_count_mismatch ctx.diagnostics ~location:i.info
                ~expected:(Array.length field_types)
                ~provided:(List.length fields);
            let* fields' =
              Array.fold_left
                (fun prev field ->
                  let name = field_name field and f = field_type field in
                  match
                    List.find_opt
                      (fun ((idx : Ast.ident), _) -> name.desc = idx.desc)
                      fields
                  with
                  | None ->
                      Error.missing_field ctx.diagnostics ~location:i.info name;
                      prev
                  | Some (name, written) ->
                      let* l = prev in
                      if written = None then record_pun ctx.pun_spans name.info;
                      (* Check the field value against its declared type, so a
                         nested struct/array literal can drop its own name. *)
                      let* checked =
                        let i' = field_value name written in
                        match internalize ctx (unpack_type f) with
                        | Some cell ->
                            let* i', _ = typed_check ctx cell i' in
                            return i'
                        | None -> typed ctx i'
                      in
                      (* Preserve punning: a punned field ([written = None]) stays
                         [None] so the printer re-emits [{x}]; the check above
                         still validates it and gives it its stack effect. *)
                      return ((name, Option.map (fun _ -> checked) written) :: l))
                (return []) field_types
            in
            (* A source field with no counterpart in the declaration (a
               field-count/name mismatch, already reported) is skipped by the
               fold above and left untyped: with per-field hole slices its slot in
               the pending values is simply dropped (no threaded arg list to keep
               balanced, no separate hole-order pass to feed), and the whole
               construction is being rejected anyway. *)
            (* The fields alone pin this type (re-parse re-resolves to it via
               field inference, which takes precedence over the expected type),
               so a present name is redundant. *)
            let field_unique =
              match field_match with
              | Some n -> n.desc = typ.desc
              | None -> false
            in
            let emitted = emitted_name ty typ ~field_unique in
            let*! result = construction_result typ in
            return_expression i (Struct (emitted, List.rev fields')) result
      in
      (* What a bare [{..}] re-infers to: when the fields alone name this exact
         type — [field_match] names [node]'s own result heap type — the bare
         construction re-resolves to it standalone, so it reports [Typ] of its own
         result and the binding site compares that to its annotation ([let x: T =
         {..}] drops the [: T] when [T] is that type). When the fields are
         ambiguous a name-less [{..}] cannot re-infer at all, so it is
         [Uninferrable] and any surrounding annotation is load-bearing. Read the
         result back from [node] rather than the branch-local [typ], so no mutable
         cell need escape the [let*!] arms. *)
      let standalone = standalone_valtype ctx (expression_type ctx node) in
      let fields_pin_result =
        match (field_match, standalone) with
        | Some n, Some { typ = Ref { typ = Type t | Exact t; _ }; _ } ->
            t.desc = n.desc
        | _ -> false
      in
      return
        ( node,
          if fields_pin_result then reinfer_of_cell (expression_type ctx node)
          else Uninferrable )
  | StructDefault ty ->
      let* node =
        match
          resolve_name ty ~missing:(fun () ->
              Error.cannot_infer_struct_type ctx.diagnostics ~location:i.info)
        with
        | None -> return_expression i (StructDefault None) (Cell.make Error)
        | Some typ ->
            let*! fields = lookup_struct_type ctx typ in
            if
              not
                (Array.for_all
                   (fun field -> field_has_default (field_type field))
                   fields)
            then Error.not_defaultable ctx.diagnostics ~location:typ.info;
            require_no_descriptor typ;
            let emitted = emitted_name ty typ ~field_unique:false in
            let*! result = construction_result typ in
            return_expression i (StructDefault emitted) result
      in
      return (node, construction_reinfer node)
  | StructDesc (d, fields) ->
      (* [{ descriptor(d) | fields }] lowers to [struct.new_desc], which pushes
         the field values then the descriptor on top. But the descriptor's type
         [Y] (with [Y describes X]) fixes the struct type [X] the fields are
         checked against, so the descriptor must be typed FIRST — out of emission
         order, which the explicit hole slices make sound for the stack and
         [type_trailing_operand] makes sound for the initialized-local analysis
         (the descriptor, emitted last, may read a local a field [local.tee]s, and
         its own tees must not leak back into the fields). Split the pending
         values: the fields take the front slice, the descriptor the tail; type
         the descriptor against the tail with a fresh hole state, the fields in
         emission order over the front slice, then fold the descriptor into the
         hole-order check and replay its init-locals effects as the last
         operand. *)
      fun st ->
        if ctx.suggest then
          List.iter
            (fun (name, written) ->
              Typing_suggest.suggest_punning ctx name written)
            fields;
        let front_holes =
          List.fold_left
            (fun acc (_, w) -> acc + Option.fold ~none:0 ~some:count_holes w)
            0 fields
        in
        let front_pending, tail_pending = list_split front_holes st.pending in
        let d, replay =
          type_trailing_operand ctx (fun () ->
              let _, d =
                instruction ctx d
                  { pending = tail_pending; value_loc = None; reported = false }
              in
              d)
        in
        let target =
          descriptor_reftype ctx ~location:i.info ~nullable:false d
        in
        let type_body =
          match
            Option.map (fun (t : reftype) -> named_heaptype t.typ) target
          with
          | None | Some None ->
              let* fields' =
                List.fold_left
                  (fun prev ((name : Ast.ident), written) ->
                    let* l = prev in
                    if written = None then record_pun ctx.pun_spans name.info;
                    let* fi' = typed ctx (field_value name written) in
                    return ((name, Option.map (fun _ -> fi') written) :: l))
                  (return []) fields
              in
              return_expression i
                (StructDesc (d, List.rev fields'))
                (Cell.make Error)
          | Some (Some typ) ->
              let*! field_types = lookup_struct_type ctx typ in
              if List.length fields <> Array.length field_types then
                Error.field_count_mismatch ctx.diagnostics ~location:i.info
                  ~expected:(Array.length field_types)
                  ~provided:(List.length fields);
              let* fields' =
                Array.fold_left
                  (fun prev field ->
                    let name = field_name field and f = field_type field in
                    match
                      List.find_opt
                        (fun ((idx : Ast.ident), _) -> name.desc = idx.desc)
                        fields
                    with
                    | None ->
                        Error.missing_field ctx.diagnostics ~location:i.info
                          name;
                        prev
                    | Some (name, written) ->
                        let* l = prev in
                        let* checked =
                          let i' = field_value name written in
                          match internalize ctx (unpack_type f) with
                          | Some cell ->
                              let* i', _ = typed_check ctx cell i' in
                              return i'
                          | None -> typed ctx i'
                        in
                        return
                          ((name, Option.map (fun _ -> checked) written) :: l))
                  (return []) field_types
              in
              (* A source field absent from the declaration is left untyped, as in
                 the [Struct] arm: its hole-slice slot is dropped and the
                 construction is rejected regardless. *)
              let*! result = construction_result typ in
              return_expression i (StructDesc (d, List.rev fields')) result
        in
        let st1, node = type_body { st with pending = front_pending } in
        let st2 = fold_operand ctx d d { st1 with pending = [] } in
        replay ();
        (st2, (node, construction_reinfer node))
  | StructDefaultDesc d ->
      let* d, target =
        descriptor_target ctx ~location:i.info ~nullable:false d
      in
      let* node =
        match Option.map (fun (t : reftype) -> named_heaptype t.typ) target with
        | None | Some None ->
            return_expression i (StructDefaultDesc d) (Cell.make Error)
        | Some (Some typ) ->
            let*! fields = lookup_struct_type ctx typ in
            if
              not
                (Array.for_all
                   (fun field -> field_has_default (field_type field))
                   fields)
            then Error.not_defaultable ctx.diagnostics ~location:i.info;
            let*! result = construction_result typ in
            return_expression i (StructDefaultDesc d) result
      in
      return (node, construction_reinfer node)
  | Array (ty, i1, i2) ->
      let* node =
        match
          resolve_name ty ~missing:(fun () ->
              Error.cannot_infer_array_type ctx.diagnostics ~location:i.info)
        with
        | None ->
            let* i1' = typed ctx i1 in
            let* i2' = typed ctx i2 in
            check_type ctx i2' i32_cell;
            return_expression i (Array (None, i1', i2')) (Cell.make Error)
        | Some typ ->
            (* Resolve the element type (pure) before typing the element value,
               so a struct/array literal or null cast there can be inferred /
               drop its name. The value is still typed first (then the count),
               preserving the emission order and hole slices. *)
            let elt =
              match lookup_array_type ctx typ with
              | Some field' -> internalize ctx (unpack_type field')
              | None -> None
            in
            let* i1' =
              match elt with
              | Some cell ->
                  let* i1', _ = typed_check ctx cell i1 in
                  return i1'
              | None -> typed ctx i1
            in
            let* i2' = typed ctx i2 in
            check_type ctx i2' i32_cell;
            let emitted = emitted_name ty typ ~field_unique:false in
            let*! result = construction_result typ in
            return_expression i (Array (emitted, i1', i2')) result
      in
      return (node, construction_reinfer node)
  | ArrayDefault (ty, n) ->
      let* node =
        match
          resolve_name ty ~missing:(fun () ->
              Error.cannot_infer_array_type ctx.diagnostics ~location:i.info)
        with
        | None ->
            let* n' = instruction ctx n in
            check_type ctx n' i32_cell;
            return_expression i (ArrayDefault (None, n')) (Cell.make Error)
        | Some typ ->
            let* n' = instruction ctx n in
            check_type ctx n' i32_cell;
            (let>@ field = lookup_array_type ctx typ in
             if not (field_has_default field) then
               Error.not_defaultable ctx.diagnostics ~location:typ.info);
            let emitted = emitted_name ty typ ~field_unique:false in
            let*! result = construction_result typ in
            return_expression i (ArrayDefault (emitted, n')) result
      in
      return (node, construction_reinfer node)
  | ArrayFixed (ty, instrs) ->
      let* node =
        match
          resolve_name ty ~missing:(fun () ->
              Error.cannot_infer_array_type ctx.diagnostics ~location:i.info)
        with
        | None ->
            let* instrs' =
              List.fold_left
                (fun prev i' ->
                  let* l = prev in
                  let* i' = typed ctx i' in
                  return (i' :: l))
                (return []) instrs
            in
            return_expression i
              (ArrayFixed (None, List.rev instrs'))
              (Cell.make Error)
        | Some typ ->
            let*! field' = lookup_array_type ctx typ in
            let elt = internalize ctx (unpack_type field') in
            let* instrs' =
              List.fold_left
                (fun prev i' ->
                  let* l = prev in
                  (* Check each element against the element type, so a nested
                     struct/array literal can drop its own name. *)
                  let* i' =
                    match elt with
                    | Some cell ->
                        let* i', _ = typed_check ctx cell i' in
                        return i'
                    | None -> typed ctx i'
                  in
                  return (i' :: l))
                (return []) instrs
            in
            let emitted = emitted_name ty typ ~field_unique:false in
            let*! result = construction_result typ in
            return_expression i (ArrayFixed (emitted, List.rev instrs')) result
      in
      return (node, construction_reinfer node)
  | ArraySegment (ty, seg, off, len) ->
      let* node =
        match
          resolve_name ty ~missing:(fun () ->
              Error.cannot_infer_array_type ctx.diagnostics ~location:i.info)
        with
        | None ->
            let* off' = typed ctx off in
            let* len' = typed ctx len in
            check_type ctx off' i32_cell;
            check_type ctx len' i32_cell;
            return_expression i
              (ArraySegment (None, seg, off', len'))
              (Cell.make Error)
        | Some typ ->
            let* off' = typed ctx off in
            let* len' = typed ctx len in
            check_type ctx off' i32_cell;
            check_type ctx len' i32_cell;
            (* A reference element means [array.new_elem] (the segment is an
               element segment); a numeric/packed element means [array.new_data]
               (a data segment). *)
            (let>@ field = lookup_array_type ctx typ in
             match field.typ with
             | Value (Ref dst) ->
                 let>@ src = Tbl.find ctx.diagnostics ctx.elems seg in
                 check_elem_subtype ctx ~location:i.info ~src ~dst
             | _ ->
                 ignore (Tbl.find ctx.diagnostics ctx.datas seg : unit option));
            let emitted = emitted_name ty typ ~field_unique:false in
            let*! result = construction_result typ in
            return_expression i (ArraySegment (emitted, seg, off', len')) result
      in
      return (node, construction_reinfer node)
  | String (ty, s) ->
      (* A string builds a byte array. Its natural type is the built-in
         [<string>] ([mut i8]); it adopts a different array type only when the
         context demands one — an explicit name, or one inferred from an exact
         expected type — that is not structurally that default (e.g. an immutable
         [chars]). As for the array literals a redundant name is dropped (on
         conversion from Wasm); the annotation is kept only when a bare string
         would not already take the expected type. *)
      let string_typ : Ast.ident = { desc = "<string>"; info = i.info } in
      let string_valtype =
        internalize_valtype ctx
          (Ref { nullable = false; typ = Type string_typ })
      in
      (* The natural type a bare string re-infers to: the default [<string>]
         array, allocated exactly as [construction_result] would (exact only
         when custom-descriptors is enabled). This — not the always-inexact
         [string_valtype], used only for the structural [is_default] check — is
         what decides whether a binding annotation is redundant. *)
      let string_valtype_natural =
        internalize_valtype ctx
          (Ref
             {
               nullable = false;
               typ =
                 (if
                    Wax_utils.Feature.is_enabled ctx.type_context.features
                      Wax_utils.Feature.Custom_descriptors
                  then Exact string_typ
                  else Type string_typ);
             })
      in
      let is_default name =
        match
          ( internalize_valtype ctx (Ref { nullable = false; typ = Type name }),
            string_valtype )
        with
        | Some a, Some b -> valtype_equal ctx a b
        | _ -> false
      in
      let typ =
        match
          match ty with Some _ -> ty | None -> exact_named_type expected
        with
        | Some name when not (is_default name) -> name
        | _ -> string_typ
      in
      (* A bare string builds the canonical [mut i8] array, naming no source type
         at all, so record a use of that canonical index — every definition the
         array deduplicates onto is used by the literal. The mirror of the
         validator's [string_type_reference]; resolved in the unused-field pass.
         A string that adopted a named array type resolved (and so marked) that
         name itself. *)
      if ctx.warn_unused && typ.desc = string_typ.desc then
        Option.iter
          (fun id ->
            let r = (!(ctx.origin), id) in
            if not (List.mem r !(ctx.canonical_type_references)) then
              ctx.canonical_type_references :=
                r :: !(ctx.canonical_type_references))
          (resolve_type_name ctx.diagnostics ctx.type_context string_typ);
      (let>@ field = lookup_array_type ctx typ in
       match field.typ with
       | Packed I8 -> ()
       | Packed I16 ->
           if not (String.is_valid_utf_8 s) then
             Error.string_not_unicode ctx.diagnostics ~location:i.info
       | Value _ ->
           Error.invalid_string_element_type ctx.diagnostics ~location:i.info);
      let emitted =
        if typ.desc = string_typ.desc then None
        else emitted_name ty typ ~field_unique:false
      in
      let* node =
        let*! result = construction_result typ in
        return_expression i (String (emitted, s)) result
      in
      (* A bare string re-infers to its natural [<string>] type (or the emitted
         non-default name resolves the same); it never fails to type, so it
         reports [Typ] of that natural type and the binding site drops a
         redundant annotation exactly as before. *)
      return
        ( node,
          match string_valtype_natural with
          | Some iv -> Typ (valtype_cell iv)
          | None -> Uninferrable )
  | Cast (e, typ) when is_null_initializer e ->
      let* i' = instruction ctx i in
      (* A cast of [null] is redundant when the checking context already
           provides the very type it pins: drop it to bare [null], which
           re-checks to the same type (the context re-supplies it) and lowers to
           the same [ref.null]. Gated on [simplify] so hand-written casts are
           kept; matched exactly so the lowered [ref.null] is unchanged. *)
      let i' =
        if
          ctx.simplify
          &&
          match (typ, Cell.get expected) with
          | Ast.Valtype vt, Valtype b -> (
              match internalize_valtype ctx vt with
              | Some a -> valtype_equal ctx a b
              | None -> false)
          | _ -> false
        then
          match i'.desc with
          (* Only drop down to a *bare* null: it re-checks to [expected], which
             the context re-supplies. A nested cast operand (e.g. [extern.convert_any]
             over a typed [ref.null], decompiled as [(null as &?t) as &?extern])
             pins a different type, so dropping the outer cast would change the
             value's type — keep both casts. *)
          | Cast (({ desc = Null; _ } as inner), _) ->
              { inner with info = (fst i'.info, snd inner.info) }
          | _ -> i'
        else i'
      in
      if has_expectation expected then check_type ctx i' expected;
      (* The elided form is a bare [null], which re-infers the *floating* [&?none]
         (and would lower to [ref.null none]) — not the type the cast pinned — so
         report that: a surrounding annotation stays load-bearing (its join with a
         concrete sibling still rescues it, per [join_reinfer]). A cast kept in the
         output re-infers its own pinned type. This discharges what
         [is_null_initializer] used to special-case at the binding sites. *)
      let reinfer =
        match i'.desc with
        | Null -> Typ (valtype_cell (ref_none_valtype ~nullable:true))
        | _ -> reinfer_of_cell (expression_type ctx i')
      in
      return (i', reinfer)
  | If { label; typ; cond; if_block; else_block } when has_expectation expected
    ->
      (* The checking context supplies a result type. Drop a redundant [=> T]
         (on [simplify]) when the context's [expected] is exactly the annotation
         — then re-parse recovers it from the same source (a function's [-> T],
         a typed binding, a call argument), so nothing is lost or loosened. On
         re-parse the annotation is absent, so fill the result type back in from
         [expected] for [to_wasm]. A [br] to the if's own label delivers a value
         to its exit like the branch tails, but that value is invisible to the
         per-branch re-inference below (a branch ending in such a [br] reads as
         [Diverges]); see [label_delivers] for how the annotation is kept for it. *)
      let* cond' = instruction ctx cond in
      check_type ctx cond' i32_cell;
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      let omitted = typ.results = [||] in
      (* Type the branches against the if's own declared result when annotated,
         else against the context (a re-parsed, dropped annotation). *)
      let result_cell =
        if omitted then expected
        else
          match array_map_opt (internalize ctx) typ.results with
          | Some [| c |] -> c
          | _ -> expected
      in
      let results = [| result_cell |] in
      (* Each branch reports its own fall-through re-inference (see
         [block_with_keep]); the if's is their join. *)
      (* Each arm is anchored at ITS OWN span, not the [if]'s: an output underflow
         is reported at the block's closing token, so two arms sharing the [if]'s
         span rendered their two distinct reports as one [line:col: message] twice
         over (a fuzz DIAG_DUP). *)
      let if_desc, if_reinfer =
        block_with_keep ctx if_block.info label [||] results results
          if_block.desc
      in
      let if_block' = { if_block with desc = if_desc } in
      let else_block', else_reinfer =
        match else_block with
        | Some b ->
            let else_desc, else_reinfer =
              block_with_keep ctx b.info label [||] results results b.desc
            in
            (Some { b with desc = else_desc }, else_reinfer)
        | None ->
            if not (missing_else_ok ctx [||] results) then
              Error.if_without_else ctx.diagnostics ~location:i.info;
            (* No else: the missing branch delivers no value, so it drops out of
               the join and the [then] branch decides (recovery for what is
               already an [if_without_else] error). *)
            (None, Diverges)
      in
      (* The if's result (its annotation, or [expected] when omitted) must fit
         the context — catches e.g. an [=> i64] if where [i32] is expected. *)
      check_subtype ctx ~location:i.info result_cell expected;
      (* An annotated [=> t] equal to what the context pins is redundant: dropped
         on [simplify] (Wasm->Wax), and offered as a quick fix under [ctx.suggest]
         (deleting the [=> t]). Both key on the same test. *)
      let redundant = block_result_redundant ctx typ ~expected ~result_cell in
      if ctx.suggest && redundant then
        Typing_suggest.suggest_if_result ctx cond.info.loc_end
          if_block.info.loc_start;
      let typ =
        if omitted then
          match standalone_valtype ctx expected with
          | Some iv -> { typ with results = [| iv.typ |] }
          | None -> typ
        else if ctx.simplify && redundant then { typ with results = [||] }
        else typ
      in
      (* The caller's binding annotation (e.g. [let x: T = ..]) is redundant iff
         an unannotated [let] would re-infer it — i.e. iff the join of the
         branches' own re-inference already equals it (decided at the binding
         site by [reinfer_needed]). Reading each branch's re-inference upward,
         rather than its result cell (which the annotation flowed into), is what
         makes a context-typed tail — a flexible literal, a nested [if], a bare
         [null] rescued by a sibling — no longer look spuriously redundant.

         A value delivered by a [br] to the if's own label also reaches the exit
         but is invisible to the fall-through join above ([from_wasm] does emit
         this — a [br 0] inside an [if (result T)] round-trips to [br 'l ..]).
         Its re-inference is not tracked, and reading its resolved cell would miss
         an un-named construction whose name was dropped because the label pinned
         the type (it would recompile only under the annotation). So keep the
         annotation whenever the if's label was branched to: [ctx.used_labels]
         records the label's definition site when [branch_target] resolved a [br]
         to it, and the label is unique and in scope only within these branches.
         Conservative (it keeps even for an inferrable delivery), but a [br] to an
         [if]'s own label is rare in decompiled code, and this never wrongly
         drops. *)
      let label_delivers =
        match label with
        | Some l -> IntSet.mem l.info.loc_start.pos_cnum !(ctx.used_labels)
        | None -> false
      in
      let reinfer =
        if label_delivers then Uninferrable
        else join_reinfer ctx if_reinfer else_reinfer
      in
      let* node =
        return_statement i
          (If
             {
               label;
               typ;
               cond = cond';
               if_block = if_block';
               else_block = else_block';
             })
          results
      in
      return (node, reinfer)
  (* A [do]/[loop]/[try]/[try_table] block in a checking context need not
     annotate its own result: thread [expected] in as the result type so a
     redundant annotation drops (on [simplify]) and re-parse recovers it from the
     same context ([context_result_cell] / [context_block_typ]). Branches to the
     block's own label, and (for [try]) the catch handlers, are checked against
     [expected] like the fall-through value. The block's re-inference (for a
     surrounding binding annotation) is the join of every value reaching its exit
     — the fall-through plus branched/caught values, all collected by
     [block_keep_bool] — or, when its own result annotation survives in the
     output, that annotation (the block pins its type itself); see
     [block_keep_reinfer]. *)
  | Block { label; typ; block = { desc = instrs; _ } as blkloc }
    when has_expectation expected ->
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      let result_cell = context_result_cell ctx typ ~expected in
      let instrs', r =
        block_keep_bool ctx i.info label ~result:result_cell
          ~br_params:[| result_cell |] instrs
      in
      let kept_annotation =
        typ.results <> [||]
        && not
             (ctx.simplify
             && block_result_redundant ctx typ ~expected ~result_cell)
      in
      let reinfer =
        block_keep_reinfer ctx ~loc:i.info ~result:result_cell ~kept_annotation
          r
      in
      check_subtype ctx ~location:i.info result_cell expected;
      let typ =
        context_block_typ ctx ~keyword:"do" i.info.loc_start
          blkloc.info.loc_start typ ~expected ~result_cell
      in
      let* node =
        return_statement i
          (Block { label; typ; block = { blkloc with desc = instrs' } })
          [| result_cell |]
      in
      return (node, reinfer)
  | Loop { label; typ; block = { desc = instrs; _ } as blkloc }
    when has_expectation expected ->
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      let result_cell = context_result_cell ctx typ ~expected in
      (* A [br] to a loop re-enters at its top with the loop's parameters, so it
         carries no result; the loop's value is its fall-through. Hence the
         branch-target type is the (empty) parameters, not the result, and a
         branch to the loop's label does not deliver the value. *)
      let instrs', r =
        block_keep_bool ctx i.info label ~result:result_cell ~br_params:[||]
          instrs
      in
      let kept_annotation =
        typ.results <> [||]
        && not
             (ctx.simplify
             && block_result_redundant ctx typ ~expected ~result_cell)
      in
      let reinfer =
        block_keep_reinfer ctx ~loc:i.info ~result:result_cell ~kept_annotation
          r
      in
      check_subtype ctx ~location:i.info result_cell expected;
      let typ =
        context_block_typ ctx ~keyword:"loop" i.info.loc_start
          blkloc.info.loc_start typ ~expected ~result_cell
      in
      let* node =
        return_statement i
          (Loop { label; typ; block = { blkloc with desc = instrs' } })
          [| result_cell |]
      in
      return (node, reinfer)
  | TryTable { label; typ; block = { desc = body; _ } as blkloc; catches }
    when has_expectation expected ->
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      let result_cell = context_result_cell ctx typ ~expected in
      (* A [try_table]'s catches branch to other targets, not its own label, so
         its value is the body's (the fall-through, or a [br] to its label). *)
      let body', r =
        block_keep_bool ctx i.info label ~result:result_cell
          ~br_params:[| result_cell |] body
      in
      check_trytable_catches ctx catches;
      let kept_annotation =
        typ.results <> [||]
        && not
             (ctx.simplify
             && block_result_redundant ctx typ ~expected ~result_cell)
      in
      let reinfer =
        block_keep_reinfer ctx ~loc:i.info ~result:result_cell ~kept_annotation
          r
      in
      check_subtype ctx ~location:i.info result_cell expected;
      let typ =
        context_block_typ ctx ~keyword:"try" i.info.loc_start
          blkloc.info.loc_start typ ~expected ~result_cell
      in
      let* node =
        return_statement i
          (TryTable
             { label; typ; block = { blkloc with desc = body' }; catches })
          [| result_cell |]
      in
      return (node, reinfer)
  | Try { label; typ; block = { desc = body; _ } as blkloc; catches; catch_all }
    when has_expectation expected ->
      assert (typ.params = [||]);
      let result_cell = context_result_cell ctx typ ~expected in
      (* A catch handler also produces the try's value. Type the handlers against
         the same inferring cell [r] as the body, so their values are collected too
         (a [try] whose body diverges takes its value entirely from the handlers);
         the keep-bool then sees every exit. *)
      let body', r =
        block_keep_bool ctx i.info label ~result:result_cell
          ~br_params:[| result_cell |] body
      in
      let catches, catch_all =
        type_try_catches ctx label ~results:[| r |] catches catch_all
      in
      let kept_annotation =
        typ.results <> [||]
        && not
             (ctx.simplify
             && block_result_redundant ctx typ ~expected ~result_cell)
      in
      let reinfer =
        block_keep_reinfer ctx ~loc:i.info ~result:result_cell ~kept_annotation
          r
      in
      check_subtype ctx ~location:i.info result_cell expected;
      let typ =
        context_block_typ ctx ~keyword:"try" i.info.loc_start
          blkloc.info.loc_start typ ~expected ~result_cell
      in
      let* node =
        return_statement i
          (Try
             {
               label;
               typ;
               block = { blkloc with desc = body' };
               catches;
               catch_all;
             })
          [| result_cell |]
      in
      return (node, reinfer)
  | Select (i1, i2, i3) when has_expectation expected ->
      (* The expression form of an annotated [if]: push the context's [expected]
         type into both value branches, so a construction there can drop its
         type name (re-parse re-pushes it through this same arm); the condition
         [i1] is an [i32]. The branches are evaluated before the condition, as in
         synthesis. Like an [if], the [?:]'s re-inference is the join of its two
         value branches' (via [join_reinfer]) — so a bare [null] alongside a typed
         sibling gains the same precision the [if] arm has (the join rescues it),
         rather than the coarser disjunction of per-branch keep-bools. *)
      let* i2', reinf2 = typed_check ctx expected i2 in
      let* i3', reinf3 = typed_check ctx expected i3 in
      let* i1' = typed ctx i1 in
      check_type ctx i1' i32_cell;
      (* The result is the branches' join, not [expected]: each branch is already
         [<: expected], so this keeps the select's precise type (e.g. [&bytes]
         rather than the [&eq] the context happened to ask for). *)
      let ty =
        match
          join_value_types ctx (expression_type ctx i2')
            (expression_type ctx i3')
        with
        | Some ty -> ty
        | None -> expected
      in
      let* node = return_expression i (Select (i1', i2', i3')) ty in
      return (node, join_reinfer ctx reinf2 reinf3)
  | _ ->
      let* i' = instruction ctx i in
      (* Snapshot the value's own type BEFORE [check_type] mutates the cell: this
         is what an unannotated binding would re-infer it to. Held flexible so a
         join with a concrete sibling absorbs it (see [reinfer_of_cell]). *)
      let reinfer = reinfer_of_cell (expression_type ctx i') in
      if has_expectation expected then check_type ctx i' expected;
      return (i', reinfer)

(* Run [check_instruction] in statement (empty-stack) position, mirroring the expression
   bridge in [toplevel_instruction]'s default arm: pop the hole operands off the
   stack into the parameter list, run [check_instruction] on them, and surface its
   re-inference. Used for an annotated global initializer (a constant expression). *)
and check_toplevel ctx expected i =
  with_holes ctx i (fun () -> check_instruction ctx expected i)

(* Type call arguments. When the callee's parameter types are known and the
   arity matches, check each argument against its parameter (so a struct/array
   literal argument can be inferred and have its name dropped); otherwise
   synthesize them. Either way arguments are processed left-to-right, so hole
   consumption matches [instructions]. *)
and typed_call_args ctx l param_types =
  match param_types with
  | Some params when Array.length params = List.length l ->
      let rec go k = function
        | [] -> return []
        | a :: r ->
            let* a', _ = typed_check ctx params.(k) a in
            let* r' = go (k + 1) r in
            return (a' :: r')
      in
      go 0 l
  | _ -> instructions ctx l

(* Type a value carried to a known result/branch type (a [return], [br], …).
   When exactly one value is expected, check the operand against it so a
   struct/array literal can be inferred and drop its name; otherwise synthesize
   and check the whole tuple, as before. *)
and check_against ctx expected i =
  match expected with
  | [| ty |] when is_inferring ty ->
      (* The block's result type is being inferred: synthesize the branched
         value and record it (a plain [check_instruction] would discard it, as
         [has_expectation] is false for a [Collecting] cell). When the cell
         carries a declared result (an annotation under test, or the type the
         surrounding context pins), [subtype] validates the value against it
         per-delivery, so [check_subtype] reports a [br]/catch carrying the wrong
         type precisely at its site; a fully-inferred cell ([declared = None])
         records without constraint, so this never fires spuriously. *)
      let* i' = instruction ctx i in
      check_subtype ctx ~location:(snd i'.info) (expression_type ctx i') ty;
      return i'
  | [| ty |] ->
      let* i', _ = check_instruction ctx ty i in
      return i'
  | _ ->
      let* i' = instruction ctx i in
      check_subtypes ctx ~location:(snd i'.info) (fst i'.info) expected;
      return i'

and type_indirect_call ctx i i' l =
 (* Arguments are pushed first, then the callee reference, then [call_ref]. The
     callee's function type gives the parameter types the arguments are checked
     against (so a struct/array literal argument can be inferred and drop its
     name), so the callee is typed FIRST — out of emission order, made sound for
     the stack by the explicit hole slices (front for the arguments, tail for the
     callee) and for the initialized-local analysis by [type_trailing_operand]
     (the callee, emitted last, may read a local an argument [local.tee]s, and its
     own tees must not leak back into the arguments). Then the arguments are typed
     in emission order over the front slice and the callee is folded in and its
     init-locals effects replayed as the last operand, matching [to_wasm]. The
     error arms still synthesize the arguments for recovery. *)
 fun st ->
  let front_holes = List.fold_left (fun acc a -> acc + count_holes a) 0 l in
  let front_pending, tail_pending = list_split front_holes st.pending in
  let i', replay =
    type_trailing_operand ctx (fun () ->
        let _, i' =
          instruction ctx i'
            { pending = tail_pending; value_loc = None; reported = false }
        in
        i')
  in
  (* Query the callee's expression type once: [expression_type] reports a
     zero/multi-value callee ("an expression is expected here"), so asking
     twice — here and in [type_body] below — would report it twice. *)
  let callee_type = expression_type ctx i' in
  let functype =
    match Cell.get callee_type with
    | Valtype { typ = Ref { typ = Type ty | Exact ty; _ }; _ } ->
        lookup_func_type ctx ty
    | _ -> None
  in
  let param_types =
    Option.bind functype (fun typ ->
        array_map_opt
          (fun (p : (_, location) Ast.annotated) ->
            internalize ctx (snd p.desc))
          typ.params)
  in
  let type_body =
    let* l' = typed_call_args ctx l param_types in
    match Cell.get callee_type with
    | Valtype { typ = Ref { typ = Type _ | Exact _; _ }; _ } -> (
        match functype with
        | None ->
            (* [lookup_func_type] already reported "expected function type" (the
               named type is not a function); recover with the [Unreachable]/
               [Error] node the [let*!] on that lookup used to yield, so a
               wrapping [become] treats it as a failed call rather than forming a
               tail call with an [Error] result. *)
            return
              {
                desc = Ast.Unreachable;
                info = ([| Cell.make Error |], (Ast.no_loc ()).info);
                hints = Wax_wasm.Hints.none;
                expected = Unset;
              }
        | Some typ ->
            (match param_types with
            | Some param_types when Array.length param_types <> List.length l'
              ->
                Error.operand_count_mismatch ctx.diagnostics
                  ~location:(snd i'.info) ~expected:(Array.length param_types)
                  ~provided:(List.length l')
            | _ -> ());
            let*! returned_types =
              array_map_opt (internalize ctx) typ.results
            in
            return_statement i (Call (i', l')) returned_types)
    | Error ->
        (* The callee already failed to type (e.g. an unbound name); recover
             silently rather than adding a spurious "expected function type". *)
        return_statement i (Call (i', l')) [| Cell.make Error |]
    | Unknown | UnknownRef ->
        (* The callee's type is unknown (unreachable / branch code) or only a
             reference (its function type cannot be resolved), so the call cannot
             be compiled. *)
        Error.unknown_operand_type ctx.diagnostics ~location:(snd i'.info);
        return_statement i (Call (i', l')) [| Cell.make Error |]
    | _ ->
        Error.expected_func ctx.diagnostics ~location:(snd i'.info);
        return_statement i (Call (i', l')) [| Cell.make Error |]
  in
  let st1, node = type_body { st with pending = front_pending } in
  let st2 = fold_operand ctx i' i' { st1 with pending = [] } in
  replay ();
  (st2, node)

(* Compilation-hints proposal: what a [#[targets(f: 0.73, …)]] hint on this call
   needs beyond the parser's check that it prefixes a call at all. The mirror of
   [Validation.check_hints]' [call_targets] arm, which the Wax typer owes because
   [wax check] never converts, so a problem only the lowering would hit would
   otherwise pass. Each target is resolved but NOT marked used: naming a function
   in advisory metadata is not a use, so it must not keep an otherwise-dead
   function out of the unused-field lint. *)
and check_call_targets_hint ctx (i : location instr) =
  match i.hints.Wax_wasm.Hints.targets with
  | None -> ()
  | Some h ->
      (match i.desc with
      (* Direct-call test, mirroring [To_wasm]: a bare name that denotes a module
         function and is not shadowed by a local lowers to [call], whose target is
         already known, so a target list says nothing. *)
      | (Call ({ desc = Get name; _ }, _) | TailCall ({ desc = Get name; _ }, _))
        when (not (StringMap.mem name.Annot.desc ctx.locals))
             && Tbl.find_no_mark ctx.functions name <> None ->
          Error.call_targets_direct_call ctx.diagnostics
            ~location:h.Wax_wasm.Hints.loc
      | _ -> ());
      List.iter
        (fun ((f : Ast.ident), _) ->
          if
            StringMap.mem f.Annot.desc ctx.locals
            || Tbl.find_no_mark ctx.functions f = None
          then
            Error.unbound_name ctx.diagnostics ~location:f.Annot.info "function"
              f)
        h.Wax_wasm.Hints.value;
      let total =
        List.fold_left (fun acc (_, pct) -> acc + pct) 0 h.Wax_wasm.Hints.value
      in
      if total > 100 then
        Error.call_targets_over_100 ctx.diagnostics
          ~location:h.Wax_wasm.Hints.loc ~total

and call_instruction ctx i =
  (* Dispatches a [Call]: first the intrinsic method/free-function
     forms (memory, table, segment, array, numeric, and SIMD
     operations written as [recv.meth(..)] or [name(..)]), then an
     ordinary call through a function reference. *)
  check_call_targets_hint ctx i;
  match i.desc with
  | Call
      ( ({ desc = StructGet (({ desc = Get memname; _ } as recv), meth); _ } as
         func),
        args )
    when Wax_wasm.Atomics.of_method_name meth.desc <> None
         && memory_receiver ctx memname ->
      let family = Option.get (Wax_wasm.Atomics.of_method_name meth.desc) in
      type_atomic_method_call ctx i func recv memname meth family args
  | Call
      ( ({ desc = StructGet (({ desc = Get memname; _ } as recv), meth); _ } as
         func),
        args )
    when is_mem_method meth.desc && memory_receiver ctx memname ->
      type_mem_method_call ctx i func recv memname meth args
  (* SIMD memory accesses: mem.loadv128(addr), mem.storev128(addr, v),
     mem.load8_lane(addr, v, lane), etc. Stack operands first, then the
     constant lane immediate (if any), then the usual align/offset literals. *)
  | Call
      ( ({ desc = StructGet (({ desc = Get memname; _ } as recv), meth); _ } as
         func),
        args )
    when Simd.is_mem_method meth.desc && memory_receiver ctx memname ->
      type_simd_mem_method_call ctx i func recv memname meth args
  (* Memory management: mem.size/grow/fill/copy/init, on a memory name. *)
  | Call
      ( ({ desc = StructGet (({ desc = Get name; _ } as recv), meth); _ } as func),
        args )
    when is_mgmt_method meth.desc && memory_receiver ctx name ->
      type_mem_mgmt_call ctx i func recv name meth args
  (* Table management: tab.size/grow/fill/copy/init, on a table name. *)
  | Call
      ( ({ desc = StructGet (({ desc = Get name; _ } as recv), meth); _ } as func),
        args )
    when is_mgmt_method meth.desc && table_receiver ctx name ->
      type_table_mgmt_call ctx i func recv name meth args
  (* data.drop / elem.drop, on a segment name. *)
  | Call
      ( ({
           desc =
             StructGet
               (({ desc = Get name; _ } as recv), ({ desc = "drop"; _ } as meth));
           _;
         } as func),
        [] )
    when segment_receiver ctx name ->
      let recv' =
        {
          desc = Get name;
          info = ([||], recv.info);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }
      in
      return_statement i
        (Call
           ( {
               desc = StructGet (recv', meth);
               info = ([||], func.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             [] ))
        [||]
  (* Stack-switching methods on a continuation receiver: [c.resume(x)],
     [c.resume_throw(exc(p))], [c.resume_throw_ref(e)], [c.switch(x, tag: t)];
     an [on] handler clause arrives as a wrapping [On] node (see
     [type_on_clause]). These were keywords before, so no struct field can be
     shadowed by claiming the names. *)
  | Call
      ( {
          desc =
            StructGet
              ( recv,
                ({
                   desc =
                     "resume" | "resume_throw" | "resume_throw_ref" | "switch";
                   _;
                 } as meth) );
          _;
        },
        args ) ->
      type_cont_method_call ctx i ~handlers:[] recv meth args
  | Call
      ( ({ desc = StructGet (a, ({ desc = "fill"; _ } as meth)); _ } as func),
        [ j; v; n ] ) ->
      type_array_fill_call ctx i func a meth j v n
  | Call
      ( ({ desc = StructGet (a1, ({ desc = "copy"; _ } as meth)); _ } as func),
        [ i1; a2; i2; n ] ) ->
      type_array_copy_call ctx i func a1 meth i1 a2 i2 n
  (* array.init_data / array.init_elem: arr.init(seg, dest, src, len). The
     element type selects data vs elem (as for array.new). *)
  | Call
      ( ({ desc = StructGet (a, ({ desc = "init"; _ } as meth)); _ } as func),
        arg1 :: ([ _; _; _ ] as rest) ) ->
      type_array_init_call ctx i func a meth arg1 rest
  (* An array bulk method with the wrong argument count (the exact forms are
     above) — the empty [a.fill()] a call being typed leaves. Gated on an array
     receiver so a struct field of the same name stays an indirect call. *)
  | Call
      ( ({
           desc =
             StructGet (recv, ({ desc = "fill" | "copy" | "init"; _ } as meth));
           _;
         } as func),
        args )
    when receiver_is_array_ref ctx recv ->
      type_array_method_recovery ctx i func recv meth args
  (* A scalar binary intrinsic method, [x.min(y)] — reached only when the
     receiver is numeric, not a reference: [s.min(a, b)] on a struct with a
     function-pointer field [min] is an indirect call (below), disambiguated by
     the receiver's type, not the argument count. Any argument count is accepted
     so the empty form an auto-closed call leaves ([x.min()]) still yields the
     method node (with an arity error) for recovery and editor features. *)
  | Call
      ( ({
           desc =
             StructGet
               ( i1,
                 ({
                    desc = ("rotl" | "rotr" | "copysign" | "min" | "max") as op;
                    _;
                  } as meth) );
           _;
         } as func),
        args )
    when not (receiver_is_ref ctx i1) ->
      type_binary_intrinsic_call ctx i func i1 meth op args
  (* No-argument instruction methods on a value: [x.sqrt()], [x.clz()],
     [x.to_bits()], [arr.length()]. Kept in call form so they print back with
     their parentheses; the result type is read from the receiver. *)
  | Call (({ desc = StructGet (recv, meth); _ } as func), [])
    when is_unary_method meth.desc ->
      type_unary_intrinsic_call ctx i func recv meth
  (* SIMD vector op written as a method intrinsic, [recv.add_i32x4(b)]. The lane
     shape is read from the method name (the receiver is always v128, or a scalar
     for splat); arguments are the lane immediates (if any) followed by the
     remaining stack operands. *)
  | Call (({ desc = StructGet (recv, meth); _ } as func), args)
    when Simd.classify meth.desc <> None ->
      type_simd_vector_op_call ctx i func recv meth args
  (* Built-in intrinsics written as a qualified path, [i64::add128(...)] or
     [v128::bitselect(...)]. *)
  | Call (({ desc = Path (ns, name); _ } as func), args) ->
      type_path_intrinsic_call ctx i func ns name args
  | Call (i', l) -> type_indirect_call ctx i i' l
  | _ -> assert false (* only invoked on [Call] *)

(* A qualified-path intrinsic call [ns::name(args)]. The [v128] namespace holds
   the SIMD free-function intrinsics ([const_<shape>], [bitselect]); the [i64]
   namespace holds the wide-arithmetic instructions. *)
and type_path_intrinsic_call ctx i func ns name args =
  match ns.desc with
  | "v128" -> type_simd_free_intrinsic_call ctx i func ns name args
  | "i64" -> type_wide_arith_call ctx i func ns name args
  | "atomic" when name.desc = "fence" ->
      let* args' = instructions ctx args in
      if args' <> [] then
        Error.operand_count_mismatch ctx.diagnostics ~location:func.info
          ~expected:0 ~provided:(List.length args');
      return_statement i
        (Call
           ( {
               desc = Path (ns, name);
               info = ([||], func.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             args' ))
        [||]
  (* A declared continuation type is a namespace holding its constructors,
     [k::new] / [k::bind] (the [T::] namespace constructs a [&T]). *)
  | _
    when match Tbl.find_opt ctx.type_context.types ns with
         | Some (_, { typ = Cont _; _ }) -> true
         | _ -> false ->
      type_cont_construct_call ctx i func ns name args
  | _ ->
      let* args' = instructions ctx args in
      Error.unknown_intrinsic ctx.diagnostics ~location:func.info ns.desc
        name.desc;
      return_expression i
        (Call
           ( {
               desc = Path (ns, name);
               info = ([||], func.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             args' ))
        (Cell.make Error)

(* The [i64::] wide-arithmetic intrinsics: [add128]/[sub128] take four i64
   operands (each of the two 128-bit inputs as low/high) and
   [mul_wide_s]/[mul_wide_u] take two, all returning two i64 results
   (low, high). *)
and type_wide_arith_call ctx i func ns name args =
  let* args' = instructions ctx args in
  let arity =
    match name.desc with
    | "add128" | "sub128" -> Some 4
    | "mul_wide_s" | "mul_wide_u" -> Some 2
    | _ -> None
  in
  match arity with
  | None ->
      Error.unknown_intrinsic ctx.diagnostics ~location:func.info ns.desc
        name.desc;
      (* Recover with two [Error] results (the arity every wide-arithmetic
         intrinsic has), so a typo does not cascade into a value-count error. *)
      return_statement i
        (Call
           ( {
               desc = Path (ns, name);
               info = ([||], func.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             args' ))
        [| Cell.make Error; Cell.make Error |]
  | Some n ->
      if List.length args' <> n then
        Error.operand_count_mismatch ctx.diagnostics ~location:func.info
          ~expected:n ~provided:(List.length args');
      List.iter (fun a -> check_type ctx a i64_cell) args';
      return_statement i
        (Call
           ( {
               desc = Path (ns, name);
               info = ([||], func.info);
               hints = Wax_wasm.Hints.none;
               expected = Unset;
             },
             args' ))
        [| valtype_cell i64_valtype; valtype_cell i64_valtype |]

and instructions ctx l : _ -> _ * _ list =
  (* A run of operands emitted left-to-right (call/constructor arguments, a
     [throw] payload, a resume/switch operand list, …): each takes its own
     hole-slice in this same (emission) order, so [typed] also folds in the
     hole-order check across them. *)
  match l with
  | [] -> return []
  | i :: r ->
      let* i' = typed ctx i in
      let* r' = instructions ctx r in
      return (i' :: r')

(* Like [instructions] but for static immediate operands (SIMD lane indices) that
   are not pushed on the stack: type them plainly, so they take no hole slice and
   do not count as values in the hole-order check. They are constant integers and
   never carry a hole. *)
and plain_instructions ctx l =
  match l with
  | [] -> return []
  | i :: r ->
      let* i' = instruction ctx i in
      let* r' = plain_instructions ctx r in
      return (i' :: r')

(* Type a memory-access call's argument list: a [Labelled] immediate has its
   payload typed and is re-wrapped — preserving the label for [check_memarg],
   printing and lowering — while the other arguments are typed as ordinary
   expressions. Only the memory-access typers accept labels; everywhere else
   [instructions] sends a [Labelled] node to the catch-all error. *)
and mem_call_arguments ctx l : _ -> _ * _ list =
  match l with
  | [] -> return []
  | i :: r -> (
      match i.desc with
      | Ast.Labelled (lbl, e) ->
          (* A labelled memarg ([offset: N]) is a static immediate, not a stack
             operand: type it plainly (it never carries a hole, and must not count
             as a value in the hole-order check — see [typed]). *)
          let* e' = instruction ctx e in
          let* r' = mem_call_arguments ctx r in
          return
            ({
               desc = Labelled (lbl, e');
               info = (fst e'.info, i.info);
               hints = Wax_wasm.Hints.none;
               (* Carry the producer's marker through the re-wrap (as the
                  general path does): [From_wasm] marks the label [Contextual]. *)
               expected = i.expected;
             }
            :: r')
      | _ ->
          let* i' = typed ctx i in
          let* r' = mem_call_arguments ctx r in
          return (i' :: r'))

(* Recover a [match]'s typed scrutinee. [rebuild_match] returns it when there is
   at least one arm (the scrutinee is threaded into the lowering and typed
   there). With no arms the lowering is the default alone and the scrutinee is
   discarded, so type it in isolation, giving each hole an [Error] cell so a bare
   hole scrutinee does not crash [pop_parameter]. *)
and match_recover_scrutinee ctx scrutinee = function
  | Some scrut' -> scrut'
  | None ->
      let pending =
        List.init (count_holes scrutinee) (fun _ -> Cell.make Error)
      in
      snd
        (instruction ctx scrutinee
           { pending; value_loc = None; reported = false })

and toplevel_instruction ctx i : stack -> stack * 'b =
  if debug then Wax_utils.Printer.run_err (fun p -> Printer_output.instr p i);
  match i.desc with
  | Block { label; typ; block = { desc = instrs; _ } as blkloc } ->
      let*! params =
        array_map_opt
          (fun (p : (_, location) Ast.annotated) ->
            internalize ctx (snd p.desc))
          typ.params
      in
      let*! results = array_map_opt (internalize ctx) typ.results in
      let* () = pop_args ctx `Input ~location:i.info params in
      let instrs' = block ctx i.info label params results results instrs in
      return_statement i
        (Block { label; typ; block = { blkloc with desc = instrs' } })
        results
  | Loop { label; typ; block = { desc = instrs; _ } as blkloc } ->
      let*! params =
        array_map_opt
          (fun (p : (_, location) Ast.annotated) ->
            internalize ctx (snd p.desc))
          typ.params
      in
      let*! results = array_map_opt (internalize ctx) typ.results in
      let* () = pop_args ctx `Input ~location:i.info params in
      let instrs' = block ctx i.info label params results params instrs in
      return_statement i
        (Loop { label; typ; block = { blkloc with desc = instrs' } })
        results
  | If { label; typ; cond; if_block; else_block } ->
      (* A statement-position [if] is void (a value-producing one is consumed by
         its context, so it is typed in expression position). Like a
         statement-position [block]/[loop] it is not inferred — only its
         expression-position form is ([if_inference], from [type_block_construct]).
         This also keeps a void [if] reached by a [br] to its own label working:
         the label's branch-target is then the void result, not an inferred
         single value. *)
      let* cond = toplevel_instruction ctx cond in
      check_type ctx cond i32_cell;
      let*! params =
        array_map_opt
          (fun (p : (_, location) Ast.annotated) ->
            internalize ctx (snd p.desc))
          typ.params
      in
      let*! results = array_map_opt (internalize ctx) typ.results in
      let* () = pop_args ctx `Input ~location:i.info params in
      let if_block =
        {
          if_block with
          desc = block ctx i.info label params results results if_block.desc;
        }
      in
      let else_block =
        match else_block with
        | Some b ->
            Some
              {
                b with
                desc = block ctx i.info label params results results b.desc;
              }
        | None ->
            if not (missing_else_ok ctx params results) then
              Error.if_without_else ctx.diagnostics ~location:i.info;
            None
      in
      return_statement i (If { label; typ; cond; if_block; else_block }) results
  | TryTable { label; typ; block = { desc = body; _ } as blkloc; catches } ->
      let*! params =
        array_map_opt
          (fun (p : (_, location) Ast.annotated) ->
            internalize ctx (snd p.desc))
          typ.params
      in
      let*! results = array_map_opt (internalize ctx) typ.results in
      let* () = pop_args ctx `Input ~location:i.info params in
      let body' = block ctx i.info label params results results body in
      check_trytable_catches ctx catches;
      return_statement i
        (TryTable { label; typ; block = { blkloc with desc = body' }; catches })
        results
  | Try { label; typ; block = { desc = body; _ } as blkloc; catches; catch_all }
    ->
      let*! params =
        array_map_opt
          (fun (p : (_, location) Ast.annotated) ->
            internalize ctx (snd p.desc))
          typ.params
      in
      let*! results = array_map_opt (internalize ctx) typ.results in
      let* () = pop_args ctx `Input ~location:i.info params in
      let body' = block ctx i.info label params results results body in
      let catches, catch_all =
        type_try_catches ctx label ~results catches catch_all
      in
      return_statement i
        (Try
           {
             label;
             typ;
             block = { blkloc with desc = body' };
             catches;
             catch_all;
           })
        results
  | TryCatch { label; typ; block = { desc = body; _ } as blkloc; arms } ->
      (* A statement-position structured [try]; unlike the raw [TryTable] (a
         from-Wasm shape) it takes no parameters. *)
      if Array.length typ.params > 0 then
        Error.parameterized_block_expression ctx.diagnostics ~location:i.info;
      let*! results = array_map_opt (internalize ctx) typ.results in
      let body' = block ctx i.info label [||] results results body in
      let arms' = type_trycatch_arms ctx label ~results arms in
      return_statement i
        (TryCatch
           { label; typ; block = { blkloc with desc = body' }; arms = arms' })
        results
  | Nop -> return_statement i Nop [||]
  | Unreachable -> return_statement i Unreachable [||] |> unreachable
  | Dispatch { index; cases; default; arms } ->
      (* As a statement, type-check the lowering (see [Ast_utils.lower_dispatch])
         as a sequence in the current stack — so a divergence in the trailing
         case body (e.g. every case ends in [return]) propagates, as it would for
         the equivalent blocks. *)
      let rec check_dups seen = function
        | [] -> ()
        | ((l : Ast.ident), _) :: r ->
            (match List.assoc_opt l.desc seen with
            | Some prev_loc ->
                Error.dispatch_duplicate_arm ctx.diagnostics ~location:l.info
                  ~prev_loc l
            | None -> ());
            check_dups ((l.desc, l.info) :: seen) r
      in
      check_dups [] arms;
      let index, _ =
        reject_control_holes ctx ~construct:"dispatch" ~role:"index"
          ~recovery:(Ast.Int "0") index
      in
      let lowered =
        Ast_utils.lower_dispatch ~block_info:i.info ~index ~cases ~default ~arms
      in
      let* typed, _ = block_contents ctx [||] lowered in
      let index', arms' = rebuild_dispatch typed arms in
      return_statement i
        (Dispatch { index = index'; cases; default; arms = arms' })
        [||]
  | Match { scrutinee; arms; default } ->
      (* As a statement, type-check the lowering (see [Ast_utils.lower_match]) in
         the current stack, so the void escape block's fall-through (the no-match
         path through the default) propagates. The scrutinee is threaded into the
         lowering and typed there; it is then recovered from the typed form
         rather than typed a second time (which reported every scrutinee error
         twice and crashed on a bare hole scrutinee). *)
      let scrutinee, scrut_had_holes =
        reject_control_holes ctx ~construct:"match" ~role:"scrutinee"
          ~recovery:Ast.Null scrutinee
      in
      let labels = match_labels i.info arms in
      let lowered =
        Ast_utils.lower_match ~block_info:i.info ~labels ~scrutinee ~arms
          ~default
      in
      let* typed, _ = block_contents ctx [||] lowered in
      let arms', default', scrut_opt =
        (* On an erroneous scrutinee the typed lowering may not peel apart into
           the expected block nesting; recover with empty arm/default bodies (the
           module is already being rejected — the rebuilt node only feeds the
           formatter/editor) and type the scrutinee on its own, rather than
           crashing. *)
        try rebuild_match typed arms
        with Match_shape ->
          ( List.map
              (fun (pat, (orig : (_ instr list, location) Ast.annotated)) ->
                (pat, { orig with desc = [] }))
              arms,
            [],
            None )
      in
      let scrut' = match_recover_scrutinee ctx scrutinee scrut_opt in
      (if not scrut_had_holes then
         match match_scrut_reftype ctx scrut' with
         | Some _ -> ()
         | None ->
             Error.expected_ref ctx.diagnostics ~location:(snd scrut'.info));
      return_statement i
        (Match
           {
             scrutinee = scrut';
             arms = arms';
             default = { default with desc = default' };
           })
        [||]
  | TailCall _ | Br _ | Br_table _ | Throw _ | ThrowRef _ | Return _ ->
      let* res = with_holes ctx i (fun () -> instruction ctx i) in
      return res |> unreachable
  | _ ->
      let* res = with_holes ctx i (fun () -> instruction ctx i) in
      return res

(* Check that each [try_table] catch clause forwards the right value types to its
   branch target. The handler is a separate block (the target label), so unlike
   [try] the catch contributes nothing to the [try_table]'s own result. Reported
   at the target label, framed as a handler/target mismatch. Shared by the
   expression-, statement-, and checking-position [TryTable] cases. *)
and check_trytable_catches ctx catches =
  let check_catch types label =
    let params = branch_target ctx label in
    if Array.length types <> Array.length params then
      Error.value_count_mismatch ctx.diagnostics ~location:label.info
        ~expected:(Array.length params) ~provided:(Array.length types)
    else
      Array.iter2
        (fun provided expected ->
          if not (subtype ctx provided expected) then
            Error.catch_target_mismatch ctx.diagnostics ~location:label.info
              provided expected)
        types params
  in
  List.iter
    (fun catch ->
      match catch with
      | Catch (tag, label) ->
          let>@ { params; results = r } =
            Tbl.find ctx.diagnostics ctx.tags tag
          in
          if r <> [||] then
            Error.tag_with_results ctx.diagnostics ~location:tag.info;
          let>@ params =
            array_map_opt
              (fun (p : (_, location) Ast.annotated) ->
                internalize ctx (snd p.desc))
              params
          in
          check_catch params label
      | CatchRef (tag, label) ->
          let>@ { params; results = r } =
            Tbl.find ctx.diagnostics ctx.tags tag
          in
          if r <> [||] then
            Error.tag_with_results ctx.diagnostics ~location:tag.info;
          let>@ params =
            array_map_opt
              (fun (p : (_, location) Ast.annotated) ->
                internalize ctx (snd p.desc))
              params
          in
          let>@ ref_exn =
            internalize ctx (Ref { nullable = false; typ = Exn })
          in
          check_catch (Array.append params [| ref_exn |]) label
      | CatchAll label -> check_catch [||] label
      | CatchAllRef label ->
          let>@ ref_exn =
            internalize ctx (Ref { nullable = false; typ = Exn })
          in
          check_catch [| ref_exn |] label)
    catches

(* Type a structured [try]'s arms with the fall-through rule: arm [k] is a
   block entered on its tag's payload (plus the [&exn] for a [&] arm) whose
   completion must be arm [k+1]'s entry stack — the last arm's the try's
   [results]. The try's [label] (the join) is in scope in every arm with the
   result as its branch type, so [br 'l] exits carrying the try's value.
   Diverging arms are exempt as any block body is. Each arm's entry types are
   recorded in the node ([arm_types]) for [To_wasm]'s re-lowering. *)
and type_trycatch_arms ctx label ~results arms =
  (* The arm's entry stack, as source types: the tag's payload, plus the
     non-null [&exn] for a [&] arm ([[]] for the catch-all). Mirrors
     [check_trytable_catches]' tag validation (a caught tag must have no
     results). *)
  let entry arm =
    let payload =
      match arm.arm_tag with
      | Some tag -> (
          match Tbl.find ctx.diagnostics ctx.tags tag with
          | Some { params; results = r } ->
              if r <> [||] then
                Error.tag_with_results ctx.diagnostics ~location:tag.info;
              Array.map (fun p -> param_type p) params
          | None -> [||])
      | None -> [||]
    in
    if arm.arm_ref then
      Array.append payload [| Ast.Ref { nullable = false; typ = Exn } |]
    else payload
  in
  let entries = List.map entry arms in
  let internalized e = array_map_opt (internalize ctx) e in
  let rec go arms entries =
    match (arms, entries) with
    | [], [] -> []
    | arm :: arms', e :: entries' ->
        let exit_types =
          match entries' with e' :: _ -> internalized e' | [] -> Some results
        in
        let arm' =
          match (internalized e, exit_types) with
          | Some params, Some exits ->
              (* The ARM's own span, not the try's: an arm is a block of its own,
                 and anchoring its reports at the enclosing try makes them collide
                 with the try body's — an arm that completes with nothing (an
                 empty [t => {}]) reported the missing value at the try's closing
                 token, exactly where the body's own report already sat, so the
                 same line printed twice (a duplicated diagnostic the mutation
                 fuzzer caught). Same fix as [type_try_catches] for a legacy
                 [try]'s handlers. *)
              let body' =
                block ctx arm.arm_body.Annot.info label params exits results
                  arm.arm_body.desc
              in
              {
                arm with
                arm_types = e;
                arm_body = { arm.arm_body with desc = body' };
              }
          | _ ->
              (* A type in the chain failed to resolve (already reported);
                 recover by typing the body as a plain result-producing block
                 rather than cascading. *)
              let body' =
                block ctx arm.arm_body.Annot.info label [||] results results
                  arm.arm_body.desc
              in
              {
                arm with
                arm_types = e;
                arm_body = { arm.arm_body with desc = body' };
              }
        in
        arm' :: go arms' entries'
    | _ -> assert false
  in
  go arms entries

and trycatch_inference ctx i label typ ~body ~arms =
  infer_synthesized ctx i typ ~type_body:(fun ~cs:_ ~r ->
      let results = [| r |] in
      let body' = block ctx i.info label [||] results results body.desc in
      let arms' = type_trycatch_arms ctx label ~results arms in
      fun typ ->
        TryCatch
          { label; typ; block = { body with desc = body' }; arms = arms' })

(* Type a [try_legacy]'s catch handlers (and catch-all) against [results] — each
   handler is a block that produces the try's result, like the body. Shared by
   the expression-, statement-, and checking-position [Try] cases; the body is
   typed by the caller. *)
and type_try_catches ctx label ~results catches catch_all =
  let catches =
    List.filter_map
      (fun (tag, body) ->
        let*@ { params; results = r } = Tbl.find ctx.diagnostics ctx.tags tag in
        if r <> [||] then
          Error.tag_with_results ctx.diagnostics ~location:tag.info;
        let+@ params =
          array_map_opt
            (fun (p : (_, location) Ast.annotated) ->
              internalize ctx (snd p.desc))
            params
        in
        (* The HANDLER's own span, not the [try]'s: a handler is a block of its
           own, and its parameters — the tag's payload, which the handler entry
           pushes — are pushed at that span. Anchored at the [try] instead, a
           payload the handler never consumes was reported as a value remaining
           on the stack *at the try's opening*, which is both misleading and
           indistinguishable from the enclosing construct's own leftover report
           (a duplicated diagnostic the mutation fuzzer caught). *)
        let body' =
          block ctx body.Annot.info label params results results body.Annot.desc
        in
        (tag, { body with desc = body' }))
      catches
  in
  let catch_all =
    Option.map
      (fun body ->
        {
          body with
          Annot.desc =
            block ctx body.Annot.info label [||] results results body.Annot.desc;
        })
      catch_all
  in
  (catches, catch_all)

and block_contents ctx results l =
  (* Alongside the typed body, report the trailing value's re-inference for a
     caller that keeps it ([block_with_keep] / [block_keep_bool]): [Some r] when
     this function itself produced the fall-through value by routing the trailing
     instruction through [check_instruction] (the [Empty] case below, where the
     pushed cell is the coerced result and so hides the natural type); [None]
     otherwise, leaving the caller to snapshot the fall-through off the stack (the
     value came from an earlier instruction, or was synthesized and pushed at its
     own natural type). *)
  match l with
  | [] -> return ([], None)
  (* A trailing instruction that produces the block's single value is routed
     through [check_instruction] (against the result type) rather than synthesized,
     so the result type flows into it: a nested block's own result annotation then
     drops, a construction drops its name, and a [?:] propagates the type into
     both its branches. [classify_trailing] decides which forms qualify (a
     parameterized block does not — it stays on the statement path, which pops its
     parameters off the stack, as expression position has no stack to take them
     from). *)
  | [ i ]
    when Array.length results = 1
         &&
         match classify_trailing ctx i.desc with
         | false, false -> false
         | _ -> true ->
      fun st ->
        (match st with
        | Empty when is_inferring results.(0) ->
            (* The block's own result type is being inferred (synthesis), so the
               result cell is a [Collecting] one: checking this trailing value
               against it would discard it ([has_expectation] is false). Instead
               synthesize the value — a nested block runs its own inference — and
               push its type, to be collected by the enclosing block. The pushed
               cell is the value's own natural type, so the caller can snapshot it
               ([None]). *)
            let* i' = with_holes ctx i (fun () -> instruction ctx i) in
            let* () = push_results ~loc:i.info (fst i'.info) in
            return ([ i' ], None)
        | Empty ->
            (* The stack is empty, so this trailing instruction must produce the
                block's value: a construction literal (incl. a string) or null
                cast, or a nested [if]/[do] block. Check it against the single
                result type so it can be inferred / drop its name, redundant
                cast, or its own result annotation, just like a [return].
                [check_instruction] has already validated the value against [results.(0)]
                (reporting any mismatch once), so push the result type itself
                rather than the value's own type — that keeps the block's
                [pop_args] from reporting the same mismatch a second time. The
                pushed cell is that coerced result, so surface the value's own
                re-inference ([Some]) for the caller instead. *)
            let* i', reinfer = check_toplevel ctx results.(0) i in
            let* () = push_results ~loc:i.info results in
            return ([ i' ], Some reinfer)
        | Cons _ | Unreachable | Poisoned ->
            (* The block's value is already on the stack, produced by an earlier
                instruction (or the code is unreachable / the stack poisoned);
                this trailing one is a statement, not the result-producer, so
                type it as such rather than routing it through
                [check_instruction]. *)
            let* i' = toplevel_instruction ctx i in
            let* () = push_results ~loc:i.info (fst i'.info) in
            return ([ i' ], None))
          st
  | i :: r ->
      fun st ->
        let st_after, i' = toplevel_instruction ctx i st in
        (* Dead code: the stack was reachable before [i], typing [i] left it
           polymorphic ([Unreachable] — [i] is a [br]/[return]/[unreachable] or
           the like), and a statement still follows. Report the first such
           statement, pointing back at the divergence. The following statements
           are then typed on the [Unreachable] stack, so this fires once, at the
           point control is lost. *)
        (match (st, st_after, r) with
        | (Empty | Cons _), Unreachable, dead :: _ when ctx.warn_unused ->
            Error.dead_code ctx.diagnostics ~location:dead.info
              ~related:
                [
                  {
                    Wax_utils.Diagnostic.location = i.info;
                    message =
                      Wax_utils.Message.text "Control never returns from here.";
                  };
                ]
        | _ -> ());
        let st_after, () = push_results ~loc:i.info (fst i'.info) st_after in
        (* The fall-through is the tail's; propagate its re-inference. *)
        let st_after, (r', reinfer) = block_contents ctx results r st_after in
        (st_after, (merge_let_tuple ctx i' r', reinfer))

(* Like [block] but also report the fall-through value's re-inference — what an
   unannotated [let x = <block>] would re-infer it to, standalone — for the [if]
   arm's per-branch join. Two sources feed it: the routed trailing instruction's
   own re-inference ([block_contents] returns [Some]), else a snapshot of the
   top-of-stack cell before [pop_args] coerces it to the result (the fall-through
   came from an earlier instruction). A branch that delivers no value ([Empty] /
   [Unreachable] / [Poisoned] at the exit) [Diverges], dropping out of the join.
   A value branched to the block's own label is not seen here (it is not on the
   exit stack) — [block_keep_bool] collects those for the block forms; the [if]
   arm reads only fall-throughs, sound because [from_wasm] never emits a [br] to
   an [if]'s own label carrying an uninferrable value (see IF-KEEP-BOOL.md). *)
and block_with_keep ctx loc label params results br_params body =
  with_empty_stack ctx ~location:loc ~kind:Block
    (let* () = push_results ~loc params in
     let* body', reinf_opt =
       block_contents
         { ctx with control_types = (label, br_params) :: ctx.control_types }
         results body
     in
     fun st ->
       let keep =
         match reinf_opt with
         | Some r -> r
         | None -> (
             match st with
             | Cons (_, tv, _) -> reinfer_of_cell tv
             | Empty | Unreachable | Poisoned -> Diverges)
       in
       let st, () = pop_args ctx `Output ~location:loc results st in
       (st, (body', keep)))

and block ctx loc label params results br_params body =
  fst (block_with_keep ctx loc label params results br_params body)

(* Like [block] for a paramless block checked against a single [result] type, but
   collect every value reaching its exit — the fall-through plus values branched
   to its label — at their natural types into a [Collecting] cell, so
   [block_keep_reinfer] can later read the block's own re-inference (the join of
   those, when the block's result annotation is not itself kept). The trailing
   instruction needs care: one that resolves its own type joins like any other
   exit value (route it through the inferring cell — it synthesizes), but one that
   needs the context to pin its type must be routed through the concrete [result],
   which hides its natural type, so the annotation stays load-bearing for it. A
   nested block always resolves itself; a struct does iff its fields name a unique
   type ([infer_struct_by_fields]) — then it synthesizes the same with or without
   the context, so route it through the cell; a field-ambiguous struct needs the
   context to pin its type (a named one still relies on it to drop its redundant
   name), so keep the annotation. (Only structs are field-checked here; other
   constructions stay conservative.) Returns the typed body and the [Collecting]
   cell for [block_keep_reinfer]. *)
and block_keep_bool ctx loc label ~result ~br_params body =
  (* The re-inference is decided from every value reaching the exit: the fall-through
     plus values branched to the label, collected at their natural types into [cs]
     (the branch-target [r] is a [Collecting] cell), then joined. The trailing
     instruction needs care: one that resolves its own type joins like any other
     exit value (route it through [r] — it synthesizes), but one that needs the
     context to pin its type must be routed through the concrete [result], which
     hides its natural type, so keep the annotation for it. A nested block always
     resolves itself; a struct does iff its fields name a unique type
     ([infer_struct_by_fields]) — then it synthesizes the same with or without the
     context, so route it through [r]; a field-ambiguous struct needs the context
     to pin its type (a named one still relies on it to drop its redundant name),
     so keep the annotation. (Only structs are field-checked here; other
     constructions stay conservative.) *)
  let trailing_construction, trailing_nested_block =
    match List.rev body with
    | last :: _ -> classify_trailing ctx last.desc
    | [] -> (false, false)
  in
  (* A trailing construction is routed through [result], hiding its natural type,
     so its annotation is load-bearing — mark the cell needed up front. *)
  let cs, r = fresh_collecting ~needed:trailing_construction (Some result) in
  (* Branches deliver the result for every kind but [loop] (where they re-enter):
     mirror the caller's [br_params] arity with the [Collecting] cell so their
     values are recorded. *)
  let br = if Array.length br_params > 0 then [| r |] else [||] in
  (* Route a trailing nested block through the inferring cell so it synthesizes;
     a construction or leaf is checked against the concrete result. *)
  let result_routing = if trailing_nested_block then r else result in
  with_empty_stack ctx ~location:loc ~kind:Block
    (let* block', _ =
       block_contents
         { ctx with control_types = (label, br) :: ctx.control_types }
         [| result_routing |] body
     in
     fun st ->
       (* Snapshot the fall-through's natural type before [pop_args] resolves it
          to [result], so it joins with the branched values at its own type. *)
       (match st with
       | Cons (loc', tv, _) ->
           cs.collected <- (loc', Cell.make (Cell.get tv)) :: cs.collected
       | Empty | Unreachable | Poisoned -> ());
       let st, () = pop_args ctx `Output ~location:loc [| result |] st in
       (* Return the cell: the caller may deliver more values to it (a [try]'s catch
          handlers) before [block_keep_reinfer] reads the join. Every value reaching
          the exit is already validated against [result] — the fall-through by
          [pop_args], the branched/caught values per-delivery as they were
          collected — so the join only decides the re-inference. *)
       (st, (block', r)))

(* The re-inference of a checked block typed by [block_keep_bool] — what an
   unannotated [let x = <block>] would re-infer it to. When the block's own result
   annotation survives in the output ([kept_annotation]) it pins its type itself,
   so the block re-infers to [result] regardless of its contents. Otherwise the
   annotation is dropped/omitted and the block re-infers from its contents: the
   join of every value reaching the exit (the fall-through plus branched/caught
   values collected into [cs]). A delivery that relied on the context ([cs.needed]
   — a trailing construction, or a [resume] handler that read the cell) cannot be
   re-derived, so it is [Uninferrable]; a body that delivers nothing [Diverges].
   Read after any extra deliveries (a [try]'s catch handlers) have been collected. *)
and block_keep_reinfer ctx ~loc ~result ~kept_annotation r =
  (* The re-inference from the block's contents: the join of every value reaching
     its exit. Always computed — [join_collected] reports a genuine exit-type
     mismatch (values with no common supertype) as a side effect, which must fire
     regardless of the keep decision — but discarded below when the block's own
     annotation is kept (it then pins the type itself). *)
  let contents_reinfer =
    match Cell.get r with
    | Collecting cs -> (
        if cs.needed then Uninferrable
        else
          match join_collected ctx ~location:loc cs.collected with
          | Some j -> reinfer_of_cell j
          | None -> Diverges)
    | _ -> Uninferrable
  in
  (* A kept [=> T] is a *written* result annotation the surrounding context does
     not pin, so — like a [Named] construction — the block re-infers to it only by
     exact equality, never by narrowing: narrowing an immutable outer binding down
     to a kept block result would flip the decompilation between "outer
     annotation, no block result" and "block result, no outer annotation" on the
     next cycle. *)
  if kept_annotation then named_reinfer_of_cell result else contents_reinfer

(* From the [inferred] result of an inferring block (already joined across an
   [if]'s branches) and the source [typ], produce the result-type cells for the
   stack effect and the [typ] to store on the node. For an omitted annotation
   ([typ.results = [||]]) the inferred type fills it in; for an explicit single
   result the annotation is dropped (cleared) when [simplify] and the inferred
   type is a subtype of it, else kept. (When it is a strict subtype the block
   re-infers to that subtype — a more precise but still valid result type that
   the surrounding context, which accepted the declared supertype, still
   accepts; the round-trip is then more precise than the source rather than
   byte-identical, as elsewhere.) *)
(* The concrete width an exact ([br_if]) exit value re-defaults to on re-parse
   ([resolve_omitted_valtype]: a flexible int/number/int8/int16 -> i32, large-int
   -> i64, float -> f64, a concrete value -> itself). A polymorphic ([Unknown])
   exact is a [br_if] value on the polymorphic stack of dead code, snapshotted here
   before its own downstream context (an arithmetic op, a cast) could type it; with
   the annotation dropped that context re-defaults it to i32 (the dead-code
   default), so treat it as i32 rather than "no constraint" — otherwise a block
   whose result is wider (an i64 fall-through alongside such a [br_if]) would drop
   the load-bearing annotation and no longer re-infer. [None] only for [Error]
   (recovery) and a bottom reference, which impose no width constraint. Used for the
   drop decision: an annotation dropped here must be re-derivable. *)
and exact_reparse_internal ctx ty =
  match Cell.get ty with
  | Int8 | Int16 | Unknown -> Some i32_valtype.internal
  | _ -> Option.map (fun v -> v.internal) (standalone_valtype ctx ty)

(* Whether an exact exit's re-parse type equals a candidate result [internal]. *)
and exact_reparse_matches ctx ~result ty =
  match exact_reparse_internal ctx ty with None -> true | Some e -> e = result

(* The width a flexible numeric literal re-defaults to on re-parse (int/number ->
   i32, large-int -> i64, float -> f64); [None] for anything already concrete or
   non-numeric. *)
and flexible_default_internal = function
  | Int | Number | Int8 | Int16 -> Some i32_valtype.internal
  | LargeInt -> Some i64_valtype.internal
  | Float -> Some f64_valtype.internal
  | _ -> None

(* Whether keeping the result annotation is load-bearing because dropping it would
   change the width on re-parse. [natural] are the exit types snapshotted before
   [join_collected] pinned them. When the join settled to a concrete type only
   because the declared annotation pinned a flexible exit to it (e.g. a bare float
   literal reaching an [f32] block, which the annotation pins to f32 but which
   re-defaults to f64 without it), dropping the annotation lets that exit re-infer
   the block to a different width — so keep it. Gated on [inferred] being concrete:
   when the join stayed flexible (an [if] over a [LargeInt] and an [Int] branch
   joins to a [LargeInt]) it self-resolves the same way on re-parse and the
   annotation is redundant. *)
and natural_width_forces_annotation ~natural ~inferred =
  match Option.map (fun c -> Cell.get c) inferred with
  | Some (Valtype rv) ->
      List.exists
        (fun ty ->
          match flexible_default_internal ty with
          | Some def -> def <> rv.internal
          | None -> false)
        natural
  | _ -> false

(* Snapshot the natural types of a block's collected exit values before
   [join_collected] pins them (for [natural_width_forces_annotation]). *)
and collected_natural collected =
  List.map (fun (_, ty) -> Cell.get ty) collected

(* A [br_if] value stays on the stack typed as the block's result; when the result
   is fixed (a present annotation, a context type, or the inferred join, all of
   which pin a flexible exact), only a *concrete* exact of a different type is a
   genuine mismatch — a flexible one is coerced to the result. Report each such
   exact against [result] (a concrete width). *)
and report_exact_mismatches ctx ~location ~result exacts =
  match standalone_valtype ctx result with
  | None -> ()
  | Some t ->
      List.iter
        (fun (loc, ty) ->
          match Cell.get ty with
          | Valtype v when v.internal <> t.internal ->
              Error.br_if_result_mismatch ctx.diagnostics ~location
                ~loc:(Option.value loc ~default:location)
                ~result ty
          | _ -> ())
        exacts

and finalize_inferred ?(needed = false) ?(exacts = []) ?(natural = []) ?location
    ctx typ ~inferred =
  if typ.results = [||] then
    match Option.bind inferred (resolve_omitted_valtype ctx) with
    | Some iv ->
        (* The inferred result pins a flexible exact, so only a concrete exact of a
           different type is unsound; without an annotation there is nothing to make
           it match, so report it. *)
        (match location with
        | Some location ->
            report_exact_mismatches ctx ~location ~result:(valtype_cell iv)
              exacts
        | None -> ());
        ([| valtype_cell iv |], { typ with results = [| iv.typ |] })
    | None -> ([||], typ)
  else
    let result_cells =
      match array_map_opt (internalize ctx) typ.results with
      | Some a -> a
      | None -> [||]
    in
    let drop =
      ctx.simplify && (not needed)
      && Array.length result_cells = 1
      (* Keep the annotation if any exit (a fall-through / [br_table] value, …)
         would re-default to a different width on re-parse. *)
      && (not (natural_width_forces_annotation ~natural ~inferred))
      (* Only drop the annotation when every exact ([br_if]) exit re-defaults to
         exactly the result; otherwise re-parse would re-infer a different result
         and the pass-through value would no longer match it. *)
      && (match standalone_valtype ctx result_cells.(0) with
        | Some t ->
            List.for_all
              (fun (_, ty) -> exact_reparse_matches ctx ~result:t.internal ty)
              exacts
        | None -> exacts = [])
      &&
      match
        ( Option.bind inferred (standalone_valtype ctx),
          standalone_valtype ctx result_cells.(0) )
      with
      | Some v, Some t ->
          Wax_wasm.Types.val_subtype (subtyping_info ctx) v.internal t.internal
      | _ -> false
    in
    (result_cells, if drop then { typ with results = [||] } else typ)

(* Shared scaffold for the five expression-position synthesis inferers
   ([if]/[block]/[loop]/[try_table]/[try]). They are identical apart from the
   guard, how the body is typed, and the node they rebuild: each types its body
   against a fresh [Collecting] result cell, then joins the collected exits and
   (on [simplify]) drops a redundant annotation the same way. [applies] is an
   extra guard on top of [infer_block_applies] ([if] also requires an [else]);
   [type_body ~cs ~r] types the body against the shared cell and returns whatever
   [rebuild ~typ] needs to reconstruct the node. *)
and infer_synthesized ?(applies = true) ctx i typ ~type_body =
  if not (infer_block_applies ctx typ && applies) then None
  else
    let cs, r = fresh_collecting (declared_result ctx typ) in
    (* [type_body] types the body against the shared cell (its side effects on
       [cs] are what the join below reads) and returns a [rebuild] closure that
       reconstructs the node from the finalized result type. *)
    let rebuild = type_body ~cs ~r in
    (* Every exit that delivered nothing is an error once another delivered a
       value (see [collect_into]); in source order, the list being built by
       consing. *)
    if cs.collected <> [] then
      List.iter
        (fun location ->
          Error.short_stack ctx.diagnostics `Output ~location ~actual:0
            ~expected:1)
        (List.rev cs.empty_exits);
    let natural = collected_natural cs.collected in
    let inferred = join_collected ctx ~location:i.info cs.collected in
    let results, typ =
      finalize_inferred ~needed:cs.needed ~exacts:cs.exacts ~natural
        ~location:i.info ctx typ ~inferred
    in
    Some (rebuild typ, results)

(* Try to infer (and, on [simplify], drop) an [if]'s result type from the values
   reaching its exit, returning the typed node when it applies and [None] to fall
   back to the annotated path. Called from the expression-position [If] case
   ([type_block_construct]); a statement-position [if] is void and not inferred,
   like a statement [block]/[loop]. [cond] is the already-typed condition.
   Applies with an [else] and under the same conditions as the other block forms
   ([infer_block_applies]). Like them, both branches are typed against one shared
   [Collecting] cell (via [collect_into]), so every value reaching the exit —
   each branch's fall-through and any value branched to the [if]'s own label — is
   recorded and then joined. A trailing construction still synthesizes its own
   type (its natural type is what is collected), so [finalize_inferred] only
   drops [=> T] when that synthesized type is a subtype of it (a tail that cannot
   synthesize on its own, e.g. a bare [null], keeps it). *)
and if_inference ctx i label typ ~cond ~if_block ~else_block =
  infer_synthesized ~applies:(Option.is_some else_block) ctx i typ
    ~type_body:(fun ~cs ~r ->
      (* Each arm anchored at its own span, as on the annotated path: the exits
         they record are reported at the block's closing token, and the [if]'s own
         span would render two arms' reports as the same line twice. *)
      let else_b = Option.get else_block in
      let if_block' =
        collect_into ctx if_block.info label ~cs ~r if_block.desc
      in
      let else_block' = collect_into ctx else_b.info label ~cs ~r else_b.desc in
      fun typ ->
        If
          {
            label;
            typ;
            cond;
            if_block = { if_block with desc = if_block' };
            else_block = Some { else_b with desc = else_block' };
          })

(* The block's declared single result internalized to a cell, or [None] when the
   result is omitted. *)
and declared_result ctx typ =
  match typ.results with [| t |] -> internalize ctx t | _ -> None

(* A fresh [Collecting] result cell and its backing record: [declared] is the
   annotation under test (or [None]), [needed] preset when it is already known to
   be load-bearing. *)
and fresh_collecting ?(needed = false) declared =
  let cs =
    { collected = []; exacts = []; declared; needed; empty_exits = [] }
  in
  (cs, Cell.make (Collecting cs))

(* Type one block body against the shared [Collecting] result cell [r] (backed
   by [cs]), in synthesis, recording every value reaching its exit — the
   fall-through plus each value branched to [label] — into [cs.collected] (via
   [subtype]) rather than unifying. The label is bound to [r] so [br]/[br_on_*]
   record their value; [r] is also passed as the body's result so a trailing
   nested block is routed and synthesized (its value collected) rather than typed
   as a void statement and lost — the fall-through is still read off the stack
   below. Returns the typed body. Every inferring block routes through this; [if]
   calls it once per branch with a shared cell so both branches' exits join. *)
and collect_into ctx loc label ~cs ~r instrs =
  with_empty_stack ctx ~location:loc ~kind:Block
    (let* body', _ =
       block_contents
         { ctx with control_types = (label, [| r |]) :: ctx.control_types }
         [| r |] instrs
     in
     fun st ->
       (* The fall-through value (if any) reaches the exit alongside the
          branched ones. A single leftover is consumed; anything else is left
          for [with_empty_stack] to report. A value sitting on an [Unreachable]
          base is a dead fall-through (e.g. after a [br]): consume it just as
          [pop_args] would in check position, leaving the unreachable base. *)
       match st with
       | Cons (loc, tv, Empty) ->
           cs.collected <- (loc, tv) :: cs.collected;
           (Empty, body')
       | Cons (loc, tv, (Unreachable | Poisoned)) ->
           cs.collected <- (loc, tv) :: cs.collected;
           (Unreachable, body')
       (* A REACHABLE fall-through delivering nothing, while some exit delivered a
          value, leaves the block yielding a result its own exit does not produce
          — the lowering would emit a block whose declared result the body never
          leaves. The annotated paths ([block_with_keep], [block_keep_bool]) catch
          this through their [pop_args ~`Output]; an inferred result must be
          delivered by every exit just as a declared one is. Only RECORD it here,
          anchored at the block's closing token as [pop] anchors every other
          [`Output] underflow: whether it is an error depends on the exits still
          to come, and an [if] types one arm before the other, so deciding it here
          reported the empty arm only when it came SECOND ([cs.collected] was
          still empty for an empty THEN arm, and nothing revisited it once the
          else arm delivered a value — the typer then accepted a module the
          lowering's validation rejected). [infer_synthesized] reports once the
          whole body is typed. An [Unreachable] fall-through (the case above)
          needs no value: nothing reaches the exit that way. *)
       | Empty ->
           cs.empty_exits <- loc_last_char loc :: cs.empty_exits;
           (Empty, body')
       | (Unreachable | Poisoned) as st -> (st, body')
       | Cons _ -> (st, body'))

(* Join the values reaching a block's exit into its inferred result, or [None]
   when none do (a void or fully divergent body). Incompatible exit types are
   reported with a caret at each offending value (falling back to [location], the
   block, when a value carries none); this is unreachable for well-typed input,
   where every exit is a subtype of the declared result. One type is kept so a
   single result is still produced. *)
and join_collected ctx ~location collected =
  (* [collected] is built in reverse (cons as each exit is met); fold in source
     order so a mismatch points at the values that way and recovers with the
     first. *)
  match List.rev collected with
  | [] -> None
  | (loc0, first) :: rest ->
      Some
        (snd
           (List.fold_left
              (fun (loc_acc, acc) (loc, ty) ->
                match join_value_types ctx acc ty with
                | Some r -> (loc_acc, r)
                | None ->
                    Error.block_exit_type_mismatch ctx.diagnostics ~location
                      ~loc1:(Option.value loc_acc ~default:location)
                      ~loc2:(Option.value loc ~default:location)
                      acc ty;
                    (loc_acc, acc))
              (loc0, first) rest))

(* Whether to infer a block's result in expression (synthesis) position: only
   for the single-result, parameterless forms, and only when the annotation is
   omitted (a re-parse of a dropped one, which must be re-inferred) or [simplify]
   is converting from Wasm (so a redundant annotation can be dropped). *)
and infer_block_applies ctx typ =
  Array.length typ.params = 0
  && (typ.results = [||] || (ctx.simplify && Array.length typ.results = 1))

(* Infer (and, on [simplify], drop) the result type of a [do]/labelled block
   from the values reaching its exit. The single-branch counterpart of
   [if_inference]: same [fresh_collecting] / [collect_into] / [join_collected]
   shape, with one body. *)
and block_inference ctx i label typ ~instrs =
  infer_synthesized ctx i typ ~type_body:(fun ~cs ~r ->
      let body' = collect_into ctx i.info label ~cs ~r instrs.desc in
      fun typ -> Block { label; typ; block = { instrs with desc = body' } })

(* Expression-position synthesis inference for [loop]/[try]/[try_table], the
   analogue of [block_inference] for [do]. Type the body (and, for [try], the
   handlers) against a fresh [Collecting] result cell so every value reaching the
   exit — the fall-through, and values branched to the block's label — is
   recorded, then join them and (on [simplify]) drop a redundant annotation. A
   [br] to a loop re-enters at its top (branch-target = the empty params), so a
   loop's value is only its fall-through; the others deliver to their label. *)
and loop_inference ctx i label typ ~instrs =
  infer_synthesized ctx i typ ~type_body:(fun ~cs:_ ~r ->
      let instrs' = block ctx i.info label [||] [| r |] [||] instrs.desc in
      fun typ -> Loop { label; typ; block = { instrs with desc = instrs' } })

and trytable_inference ctx i label typ ~body ~catches =
  infer_synthesized ctx i typ ~type_body:(fun ~cs:_ ~r ->
      let results = [| r |] in
      let body' = block ctx i.info label [||] results results body.desc in
      check_trytable_catches ctx catches;
      fun typ ->
        TryTable { label; typ; block = { body with desc = body' }; catches })

and try_inference ctx i label typ ~body ~catches ~catch_all =
  infer_synthesized ctx i typ ~type_body:(fun ~cs:_ ~r ->
      let results = [| r |] in
      let body' = block ctx i.info label [||] results results body.desc in
      let catches, catch_all =
        type_try_catches ctx label ~results catches catch_all
      in
      fun typ ->
        Try
          { label; typ; block = { body with desc = body' }; catches; catch_all })

(*** Module type and constant checking ***)

let check_type_definitions ctx =
  Tbl.iter ctx.types (fun _ (i, (st : subtype)) ->
      let ty = Wax_wasm.Types.get_subtype (subtyping_info ctx) (def_id i) in
      (* A continuation type must wrap a function type. Point at the wrapped
         type as the source wrote it. *)
      (match (ty.typ, st.typ) with
      | Cont ft, Cont src_ref -> (
          match (Wax_wasm.Types.get_subtype (subtyping_info ctx) ft).typ with
          | Func _ -> ()
          | Struct _ | Array _ | Cont _ ->
              Error.expected_func_type ctx.diagnostics ~location:src_ref.info)
      | _ -> ());
      (* Every check below is about the type's relationship to its declared
         supertype, so the supertype reference [sup] is the place to point. *)
      match (ty.supertype, st.supertype) with
      | None, _ | _, None -> ()
      | Some j, Some sup ->
          let location = sup.info in
          let ty' = Wax_wasm.Types.get_subtype (subtyping_info ctx) j in
          if ty'.final then Error.final_supertype ctx.diagnostics ~location sup
          else
            let valid_subtype =
              match (ty.typ, ty'.typ) with
              | ( Func { params; results },
                  Func { params = params'; results = results' } ) ->
                  Array.length params = Array.length params'
                  && Array.length results = Array.length results'
                  && Array.for_all2
                       (fun p p' ->
                         Wax_wasm.Types.val_subtype (subtyping_info ctx) p' p)
                       params params'
                  && Array.for_all2
                       (fun r r' ->
                         Wax_wasm.Types.val_subtype (subtyping_info ctx) r r')
                       results results'
              | Struct fields, Struct fields' ->
                  Array.length fields' <= Array.length fields
                  &&
                  let rec loop k =
                    k >= Array.length fields'
                    || (field_subtype ctx fields.(k) fields'.(k) && loop (k + 1))
                  in
                  loop 0
              | Array field, Array field' -> field_subtype ctx field field'
              | Cont ft, Cont ft' ->
                  Wax_wasm.Types.heap_subtype (subtyping_info ctx) (Type ft)
                    (Type ft')
              | Func _, (Struct _ | Array _ | Cont _)
              | Struct _, (Func _ | Array _ | Cont _)
              | Array _, (Func _ | Struct _ | Cont _)
              | Cont _, (Func _ | Struct _ | Array _) ->
                  false
            in
            let descriptor_ok =
              (* A subtype has a descriptor iff its supertype does, and the
                 subtype's descriptor must be a subtype of the supertype's. *)
              match (ty.descriptor, ty'.descriptor) with
              | None, None -> true
              | Some ds, Some dp ->
                  Wax_wasm.Types.heap_subtype (subtyping_info ctx) (Type ds)
                    (Type dp)
              | Some _, None | None, Some _ -> false
            in
            let describes_ok =
              (* A subtype has a described type iff its supertype does, and the
                 subtype's described type must be a subtype of the supertype's. *)
              match (ty.describes, ty'.describes) with
              | None, None -> true
              | Some os, Some op ->
                  Wax_wasm.Types.heap_subtype (subtyping_info ctx) (Type os)
                    (Type op)
              | Some _, None | None, Some _ -> false
            in
            if not (valid_subtype && descriptor_ok && describes_ok) then
              Error.invalid_subtype ctx.diagnostics ~location sup)

(* Check that [i] is a constant expression. The recursion returns whether the
   SUBTREE already reported a violation: an enclosing construct whose own shape
   test fails only because a nested offender was already reported (a
   non-constant leaf poisons every level of a nested [BinOp] chain) must not
   re-report — one root cause, one diagnostic, at the innermost offender. *)
let rec check_constant_instruction ctx i =
  ignore (constant_instruction ctx i : bool)

and constant_instruction ctx i =
  let location = snd i.info in
  let required () =
    Error.constant_expression_required ctx.diagnostics ~location;
    true
  in
  match i.desc with
  | Get idx -> (
      match Tbl.find_opt ctx.globals idx with
      | Some (mut, _) ->
          if mut then (
            Error.constant_global_required ctx.diagnostics ~location;
            true)
          else false
      | None -> (* ref.func *) false)
  | Null | StructDefault _ | Int _ | Float _ | Char _ | String _ -> false
  (* [array.new_default] fills with the field default, but its length is an
     arbitrary expression that must itself be constant (like the sibling [Array]
     / [ArrayFixed] / [ContNew] constructors). *)
  | ArrayDefault (_, len) -> constant_instruction ctx len
  (* A punned field ([None], written [{x}]) is a [Get] of the like-named global,
     so it must satisfy the same constant-global rule; check that implicit [Get].
     The [storagetype] array of the fabricated node is unused by the [Get] arm. *)
  | Struct (_, l) ->
      List.fold_left (fun r f -> constant_field ctx f || r) false l
  | StructDesc (d, l) ->
      let r = constant_instruction ctx d in
      List.fold_left (fun r f -> constant_field ctx f || r) r l
  | StructDefaultDesc d -> constant_instruction ctx d
  | ArrayFixed (_, l) ->
      List.fold_left (fun r i -> constant_instruction ctx i || r) false l
  | Array (_, i1, i2) ->
      let r1 = constant_instruction ctx i1 in
      constant_instruction ctx i2 || r1
  (* [cont.new] allocates a fresh continuation from a (constant) function
     reference, so it is itself constant; its operand must be constant too. This
     tracks the open stack-switching spec PR (the spec does not list it yet). *)
  | ContNew (_, f) -> constant_instruction ctx f
  | BinOp ({ desc = Add | Sub | Mul; _ }, i1, i2) -> (
      let r1 = constant_instruction ctx i1 in
      let r2 = constant_instruction ctx i2 in
      if r1 || r2 then true
      else
        match Cell.get (expression_type ctx i) with
        (* [Error] is the poison of an already-reported operand (e.g. a hole);
           a second report here would duplicate it. *)
        | Int | Valtype { internal = I32 | I64; _ } | Error -> r1 || r2
        | _ -> required ())
  | Cast ({ desc = Null; _ }, Valtype (Ref { nullable = true; _ })) ->
      (* ref.null *)
      false
  | Cast (i', Valtype (Ref { typ = I31; _ })) -> (
      if
        (* ref.i31 *)
        constant_instruction ctx i'
      then true
      else
        match Cell.get (expression_type ctx i') with
        (* [Error]: already reported (see the [BinOp] arm). *)
        | Valtype { internal = I32; _ } | Error -> false
        | _ -> required ())
  | Cast (i', Valtype (Ref { typ = Extern; nullable })) ->
      (* extern.convert_any. An [i32] operand is first wrapped in [ref.i31]
         ([i32 -> i31 -> any -> extern], as the non-constant typer lowers
         [x as &extern]), which is itself constant — so accept it like the
         [ref.i31] arm above rather than demanding the operand already be an
         [any] reference. *)
      if constant_instruction ctx i' then true
      else if
        match (Cell.get (expression_type ctx i') : inferred_type) with
        | Valtype { internal = I32; _ } -> false
        | Valtype { internal; _ } ->
            not
              (Wax_wasm.Types.val_subtype (subtyping_info ctx) internal
                 (Ref { nullable; typ = Any }))
        (* [Error]: already reported (see the [BinOp] arm). *)
        | Error -> false
        | _ -> true
      then required ()
      else false
  | Cast (i', Valtype (Ref { typ = Any; nullable })) ->
      (* any.convert_extern *)
      if constant_instruction ctx i' then true
      else if
        match (Cell.get (expression_type ctx i') : inferred_type) with
        | Valtype { internal; _ } ->
            not
              (Wax_wasm.Types.val_subtype (subtyping_info ctx) internal
                 (Ref { nullable; typ = Extern }))
        (* [Error]: already reported (see the [BinOp] arm). *)
        | Error -> false
        | _ -> true
      then required ()
      else false
  | UnOp ({ desc = Pos; _ }, i') -> constant_instruction ctx i'
  | UnOp ({ desc = Neg; _ }, { desc = Float _ | Int _; _ }) -> false
  (* [v128::<shape>(..)] is a constant expression; its lanes are literals.
     Other SIMD ops are not constant. The lanes are NOT re-walked here: the
     intrinsic's own typing already rejects any non-literal lane (with this
     same "constant expression required" report, at the lane's span), so
     re-checking each argument would report every bad lane twice. *)
  | Call ({ desc = Path (ns, name); _ }, _)
    when ns.desc = Simd.free_namespace
         && Simd.const_shape_of_name (Simd.free_full name.desc) <> None ->
      false
  | UnOp ({ desc = Neg | Not; _ }, _)
  | BinOp
      ( {
          desc =
            ( Div _ | Rem _ | And | Or | Xor | Shl | Shr _ | Eq | Ne | Lt _
            | Gt _ | Le _ | Ge _ );
          _;
        },
        _,
        _ )
  | Block _ | Loop _ | While _ | If _ | TryTable _ | Try _ | TryCatch _
  | Dispatch _ | Match _ | Unreachable | Nop | Hole | Path _ | Set _ | Tee _
  | Call _ | TailCall _ | Cast _ | CastDesc _ | Test _ | NonNull _ | StructGet _
  | GetDescriptor _ | StructSet _ | ArraySegment _ | ArrayGet _ | ArraySet _
  | Let _ | Br _ | Br_if _ | Br_table _ | Br_on_null _ | Br_on_non_null _
  | Br_on_cast _ | Br_on_cast_fail _ | Br_on_cast_desc_eq _
  | Br_on_cast_desc_eq_fail _ | Throw _ | ThrowRef _ | ContBind _ | Suspend _
  | Resume _ | ResumeThrow _ | ResumeThrowRef _ | Switch _ | On _ | Return _
  | Sequence _ | Select _ | If_annotation _ | Labelled _ ->
      required ()

(* A struct-literal field in a constant expression. An explicit value is checked
   directly; a punned field ([None]) is the implicit [Get] of the like-named
   global, which must also be an immutable global. *)
and constant_field ctx (name, i) =
  match i with
  | Some i -> constant_instruction ctx i
  | None ->
      constant_instruction ctx
        {
          desc = Get name;
          info = ([||], name.info);
          hints = Wax_wasm.Hints.none;
          expected = Unset;
        }

(*** Globals, functions, and declarations ***)

type ('before, 'after) phased =
  | Before of 'before
  | After of 'after
  | PhasedConditional of {
      before : 'before;
      then_ : ('before, 'after) phased list;
      else_ : ('before, 'after) phased list option;
    }

(* Type a data-segment offset as a constant expression of the memory address type. *)
let type_data_offset ctx address_type off =
  let off' =
    with_empty_stack ctx ~location:off.info ~kind:Expression
      (toplevel_instruction ctx off)
  in
  check_type ctx off' (address_cell address_type);
  check_constant_instruction ctx off';
  off'

(*** Data segment contents (WAT numeric-values proposal) ***)

let storagetype_name : storagetype -> string = function
  | Packed I8 -> "i8"
  | Packed I16 -> "i16"
  | Value I32 -> "i32"
  | Value I64 -> "i64"
  | Value F32 -> "f32"
  | Value F64 -> "f64"
  | Value (V128 | Ref _) -> "?"

(* Whether a raw literal string is a valid value of the run's element type. Reuse
   the same predicates the WAT numlist form validates with, so the two agree. *)
let data_run_element_valid (st : storagetype) s =
  match st with
  | Packed I8 -> Wax_wasm.Misc.is_int8 s
  | Packed I16 -> Wax_wasm.Misc.is_int16 s
  | Value I32 -> Wax_wasm.Misc.is_int32 s
  | Value I64 -> Wax_wasm.Misc.is_int64 s
  | Value F32 -> Wax_wasm.Misc.is_float32 s
  | Value F64 -> Wax_wasm.Misc.is_float64 s
  | Value (V128 | Ref _) -> false

(* The lane count and per-lane validity of a [v128] run element's shape. *)
let vec_lane_count : Wax_utils.V128.shape -> int = function
  | I8x16 -> 16
  | I16x8 -> 8
  | I32x4 | F32x4 -> 4
  | I64x2 | F64x2 -> 2

let vec_lane_name : Wax_utils.V128.shape -> string = function
  | I8x16 -> "i8"
  | I16x8 -> "i16"
  | I32x4 -> "i32"
  | I64x2 -> "i64"
  | F32x4 -> "f32"
  | F64x2 -> "f64"

let vec_lane_valid (shape : Wax_utils.V128.shape) s =
  match shape with
  | I8x16 -> Wax_wasm.Misc.is_int8 s
  | I16x8 -> Wax_wasm.Misc.is_int16 s
  | I32x4 -> Wax_wasm.Misc.is_int32 s
  | I64x2 -> Wax_wasm.Misc.is_int64 s
  | F32x4 -> Wax_wasm.Misc.is_float32 s
  | F64x2 -> Wax_wasm.Misc.is_float64 s

(* Validate one data-segment element: string (nothing to check), scalar run (each
   value in range for the element type), or [v128] run (each lane group has its
   shape's lane count, and every lane is in range). Values are raw literal
   strings — nothing is typed as an expression. *)
let type_data_element ctx (e : Ast.data_elem) =
  match e with
  | Data_string _ -> ()
  | Data_run (st, values) ->
      List.iter
        (fun (v : (string, location) Ast.annotated) ->
          if not (data_run_element_valid st v.desc) then
            Error.data_run_bad_element ctx.diagnostics ~location:v.info
              (storagetype_name st))
        values
  | Data_v128 vs ->
      List.iter
        (fun (v : (Wax_utils.V128.t, location) Ast.annotated) ->
          let { Wax_utils.V128.shape; components } = v.desc in
          if List.length components <> vec_lane_count shape then
            Error.data_v128_arity ctx.diagnostics ~location:v.info
              (vec_lane_count shape);
          List.iter
            (fun c ->
              if not (vec_lane_valid shape c) then
                Error.data_run_bad_element ctx.diagnostics ~location:v.info
                  (vec_lane_name shape))
            components)
        vs

let type_data_init ctx init = List.iter (type_data_element ctx) init

let rec globals ctx fields =
  List.map
    (fun (field : (_ modulefield, location) Ast.annotated) ->
      match field.desc with
      | Memory ({ address_type; data; _ } as m) ->
          check_limits ctx ~location:field.info "memory" ~shared:m.shared
            address_type m.page_size_log2 m.limits max_memory_size;
          let data =
            List.map
              (fun (d : _ Ast.memdata) ->
                type_data_init ctx d.init;
                { d with offset = type_data_offset ctx address_type d.offset })
              data
          in
          After { field with desc = Memory { m with data } }
      | Data ({ mode; _ } as d) ->
          let mode =
            match mode with
            | Passive -> Passive
            | Active (mem, off) ->
                let address_type =
                  match Tbl.find_opt ctx.memories mem with
                  | Some (_, at) -> at
                  | None ->
                      let suggestions =
                        Wax_utils.Spell_check.f
                          (fun f -> Tbl.iter ctx.memories (fun k _ -> f k))
                          mem.desc
                      in
                      Error.unbound_name ctx.diagnostics ~location:mem.info
                        ~suggestions "memory" mem;
                      `I32
                in
                Active (mem, type_data_offset ctx address_type off)
          in
          type_data_init ctx d.init;
          After { field with desc = Data { d with mode } }
      | Elem ({ reftype = rt; mode; init; _ } as e) ->
          let mode =
            match mode with
            | EPassive -> EPassive
            | EActive (tab, off) ->
                (* The offset indexes [tab], whose address type may be i64. *)
                let address_type =
                  match Tbl.find_opt ctx.tables tab with
                  | Some (at, _) -> at
                  | None ->
                      let suggestions =
                        Wax_utils.Spell_check.f
                          (fun f -> Tbl.iter ctx.tables (fun k _ -> f k))
                          tab.desc
                      in
                      Error.unbound_name ctx.diagnostics ~location:tab.info
                        ~suggestions "table" tab;
                      `I32
                in
                EActive (tab, type_data_offset ctx address_type off)
          in
          let elem_typ = internalize ctx (Ref rt) in
          let init =
            List.map
              (fun i ->
                let i' =
                  with_empty_stack ctx ~location:i.info ~kind:Expression
                    (toplevel_instruction ctx i)
                in
                (let>@ typ = elem_typ in
                 check_type ctx i' typ);
                check_constant_instruction ctx i';
                i')
              init
          in
          After { field with desc = Elem { e with mode; init } }
      | Table ({ reftype = rt; init; _ } as t) ->
          check_limits ctx ~location:field.info "table" ~shared:false
            t.address_type None t.limits max_table_size;
          (* Without an initializer the table is filled with the element type's
             default value, which a non-nullable reference does not have. *)
          if Option.is_none init && not rt.nullable then
            Error.non_nullable_table ctx.diagnostics ~location:field.info;
          (* A table initializer may reference only imported globals. *)
          let init_ctx = { ctx with globals = ctx.import_globals } in
          let init =
            Option.map
              (fun e ->
                let e' =
                  with_empty_stack init_ctx ~location:e.info ~kind:Expression
                    (toplevel_instruction init_ctx e)
                in
                (let>@ typ = internalize ctx (Ref rt) in
                 check_type ctx e' typ);
                check_constant_instruction init_ctx e';
                e')
              init
          in
          After { field with desc = Table { t with init } }
      | Global ({ name; mut; typ; def; _ } as g) ->
          let typ, def' =
            match typ with
            | Some annot -> (
                (* Type the initializer in checking mode against the annotation,
                   mirroring a [let] binding: an omitted struct/array name is
                   inferred from it, and its re-inference ([reinfer_needed])
                   decides whether the annotation is redundant (dropped only when
                   converting from Wasm). An immutable ([const]) global
                   additionally drops an annotation that is a mere supertype of
                   the initializer's type ([drop_supertype]), narrowing the global
                   to that subtype — sound since nothing reassigns it (see
                   [annotation_needed]). *)
                match internalize_valtype ctx annot with
                | None ->
                    let def' =
                      with_empty_stack ctx ~location:def.info ~kind:Expression
                        (toplevel_instruction ctx def)
                    in
                    (Some annot, def')
                | Some ity ->
                    (* Type the initializer before registering the global, so a
                       self-reference (an initializer mentioning this global) is
                       still reported as an unknown name. *)
                    let def', reinfer =
                      with_empty_stack ctx ~location:def.info ~kind:Expression
                        (check_toplevel ctx (valtype_cell ity) def)
                    in
                    Tbl.add ctx.diagnostics ctx.globals name (mut, Some ity);
                    (* A [null] initializer no longer needs a special case: the
                       [Cast]/leaf arms report its floating [&?none] re-inference,
                       so [reinfer_needed] keeps the annotation on its own. *)
                    let needed =
                      reinfer_needed ~drop_supertype:(not mut) ctx reinfer
                        (valtype_cell ity)
                    in
                    let redundant = not needed in
                    (* Offer dropping the redundant annotation as a quick fix for
                       hand-written Wax, exactly as a [let] binding does; the
                       [simplify] drop below is the Wasm->Wax mirror. *)
                    if ctx.suggest && redundant then
                      Typing_suggest.suggest_redundant_annotation ctx
                        ~name_end:name.info.loc_end ~boundary:def.info.loc_start;
                    let drop = ctx.simplify && redundant in
                    ((if drop then None else Some annot), def'))
            | None ->
                (* No annotation: the global takes the initializer's type, the
                   way a [let] binding without an annotation does. An
                   [Unknown]/[Error] initializer makes the global poison
                   ([None]) rather than defaulting to [i32], so its uses do not
                   cascade; an [Unknown] one is additionally reported (see
                   [bound_value_type]). *)
                let def' =
                  with_empty_stack ctx ~location:def.info ~kind:Expression
                    (toplevel_instruction ctx def)
                in
                let ity =
                  bound_value_type ctx ~location:def.info
                    (expression_type ctx def')
                in
                Tbl.add ctx.diagnostics ctx.globals name (mut, ity);
                (None, def')
          in
          check_constant_instruction ctx def';
          After { field with desc = Global { g with typ; def = def' } }
      | Conditional { cond; then_fields; else_fields } ->
          PhasedConditional
            {
              before = field;
              then_ =
                with_cond ctx ~location:field.info cond true (fun () ->
                    globals ctx then_fields.desc);
              else_ =
                Option.map
                  (fun e ->
                    with_cond ctx ~location:field.info cond false (fun () ->
                        globals ctx e.Annot.desc))
                  else_fields;
            }
      | _ -> Before field)
    fields

let rec functions ctx fields =
  List.filter_map
    (fun field ->
      match field with
      | Before
          ({
             Annot.desc =
               Func { name; sign; body = label, body; typ; attributes };
             info = location;
           } as f) ->
          (* Attribute everything this definition resolves — its declared type as
             much as its body — to the function itself, so nothing a dead function
             names looks externally referenced. Reset after the body below. *)
          ctx.origin := From_function name.desc;
          let func_typ =
            let*@ ty =
              (* Resolve the function's own declared type without marking the
                 function name used — its definition site is not a reference, so
                 the unused-field lint can still flag it if nothing calls it.
                 A poison entry ([Some None] — the signature failed, reported at
                 registration) yields [None] here; the body is still checked
                 below, with the failed types as Error poison. *)
              let*@ entry = Tbl.find_no_mark ctx.functions name in
              let*@ _, tname, _ = entry in
              Tbl.find ctx.diagnostics ctx.types { name with desc = tname }
            in
            match ty with
            | _, { typ = Func typ; _ } -> Some typ
            | _ ->
                Error.expected_func_type ctx.diagnostics ~location:name.info;
                None
          in
          (* For a poisoned signature, the source [sign] is re-resolved with
             MUTED diagnostics — its failure was already reported at
             registration — and whatever fails again becomes Error poison (a
             poison local / an Error result cell), so the body's own errors
             still surface without cascades. *)
          let mctx =
            match func_typ with
            | Some _ -> ctx
            | None ->
                {
                  ctx with
                  diagnostics =
                    Wax_utils.Diagnostic.collector ~parent:ctx.diagnostics ();
                }
          in
          (* A [#[start]] function must have no parameters and no results. *)
          (match func_typ with
          | Some func_typ ->
              if
                List.exists (fun a -> a.Ast.attr_name = "start") attributes
                && not
                     (Array.length func_typ.params = 0
                     && Array.length func_typ.results = 0)
              then
                Error.start_function_signature ctx.diagnostics
                  ~location:name.info
          | None -> ());
          let return_types =
            match func_typ with
            | Some func_typ -> (
                match
                  array_map_opt
                    (fun typ -> internalize ctx typ)
                    func_typ.results
                with
                | Some r -> r
                | None -> [||] (* a resolved type's results resolve *))
            | None -> (
                match sign with
                | Some { results; _ } ->
                    Array.map
                      (fun typ ->
                        match internalize mctx typ with
                        | Some c -> c
                        | None -> Cell.make Error)
                      results
                | None -> [||])
          in
          let locals = ref StringMap.empty in
          (match sign with
          | Some { params; _ } ->
              Array.iter
                (fun p ->
                  let id = param_name p and typ = param_type p in
                  match id with
                  | Some id ->
                      (* A parameter type that does not resolve still binds the
                         name, as a poison local (read as [Error]), so the
                         body's uses of it do not cascade. *)
                      let typ = internalize_valtype mctx typ in
                      locals :=
                        StringMap.add id.Annot.desc (typ, id.info) !locals
                  | None -> ())
                params
          | _ -> ());
          if debug then Printf.eprintf "=== %s\n%!" name.desc;
          let ctx =
            {
              ctx with
              locals = !locals;
              (* Parameters are always initialized. *)
              initialized_locals =
                StringMap.fold
                  (fun k _ s -> StringSet.add k s)
                  !locals StringSet.empty;
              (* Fresh per-function tracking of declared and read locals. *)
              missing_holes = ref [];
              unresolved_label = ref false;
              read_locals = ref IntSet.empty;
              local_decls = ref [];
              (* Fresh per-function tracking of branched-to labels, and the
                 labels declared in the body (collected once, up front). *)
              used_labels = ref IntSet.empty;
              label_decls = List.fold_left Typing_lint.collect_labels [] body;
              (* Locals a later assignment writes, collected up front so a
                 fused [let]'s drop can spot a write-once binding (linear: one
                 traversal per function, not per binding). *)
              assigned_locals =
                List.fold_left Typing_lint.collect_assigned_locals
                  StringSet.empty body;
              control_types = [ (label, return_types) ];
              return_types;
            }
          in
          (* The syntactic lints (constant conditions, dropped pure values) read
             the source body, before typing shadows [body] with the typed one. *)
          if ctx.warn_unused then List.iter (Typing_lint.lint_source ctx) body;
          let body =
            with_empty_stack ctx ~location ~kind:Function
              (let* body, _ = block_contents ctx return_types body in
               let* () = pop_args ctx `Output ~location return_types in
               return body)
          in
          ctx.origin := Root;
          (* The body is fully typed, so the deferred lints (shift-count widths)
             can now read their pinned cells; run them here, in this function, so
             they stay in source order among the other diagnostics. *)
          Typing_lint.flush_deferred_lints ctx;
          (* A local or label whose name starts with [_] is intentionally
             unused. *)
          if ctx.warn_unused then begin
            List.iter
              (fun (name : Ast.ident) ->
                let n = name.desc in
                if
                  (not
                     (IntSet.mem name.info.loc_start.pos_cnum !(ctx.read_locals)))
                  && not (String.length n > 0 && n.[0] = '_')
                then Error.unused_local ctx.diagnostics ~location:name.info name)
              (List.rev !(ctx.local_decls));
            List.iter
              (fun (name : Ast.ident) ->
                let n = name.desc in
                if
                  (not
                     (IntSet.mem name.info.loc_start.pos_cnum !(ctx.used_labels)))
                  && not (String.length n > 0 && n.[0] = '_')
                then Error.unused_label ctx.diagnostics ~location:name.info name)
              (List.rev ctx.label_decls)
          end;
          Some
            {
              f with
              desc = Func { name; sign; body = (label, body); typ; attributes };
            }
      | PhasedConditional
          {
            before =
              {
                desc = Conditional { cond; then_fields = tf; else_fields = ef };
                info;
              };
            then_;
            else_;
          } ->
          Some
            {
              info;
              desc =
                Conditional
                  {
                    cond;
                    then_fields =
                      {
                        tf with
                        desc =
                          with_cond ctx ~location:info cond true (fun () ->
                              functions ctx then_);
                      };
                    else_fields =
                      (match (ef, else_) with
                      | Some ef, Some e ->
                          Some
                            {
                              ef with
                              desc =
                                with_cond ctx ~location:info cond false
                                  (fun () -> functions ctx e);
                            }
                      | None, None -> None
                      | _ -> assert false);
                  };
            }
      | PhasedConditional _
      | Before
          {
            desc =
              Global _ | Conditional _ | Memory _ | Data _ | Elem _ | Table _;
            _;
          } ->
          assert false
      | After f -> Some f
      | Before
          ({
             desc =
               Type _ | Module_annotation _ | Import _ | Import_group _ | Tag _;
             _;
           } as f) ->
          Some f)
    fields

let funsig ctx sign =
  check_unique_param_names ctx.diagnostics sign.params;
  sign

(* A function or tag may give both a type reference and an inline signature
   (e.g. [fn f: T (i32) -> i32]); the inline signature must then match the
   referenced function type [referenced]. The two are compared in canonical
   [Internal] form. Mirrors [Validation.check_inline_type]. *)
let check_inline_type ctx ~location referenced sign =
  match sign with
  | None -> ()
  | Some sign -> (
      match (internal_functype ctx referenced, internal_functype ctx sign) with
      | Some f, Some f' ->
          if f <> f' then
            Error.inline_function_type_mismatch ctx.diagnostics ~location
      | _ -> ())

(* Resolve a function declaration's type (a named reference or an inline
   signature). Reports resolution failures; returns [None] then. *)
let fundecl_typ ctx name typ sign =
  match typ with
  | Some typ -> (
      let*@ info = Tbl.find ctx.diagnostics ctx.types typ in
      (* The referenced type must be a function type (as for tags below); if
           an inline signature is also given, it must match. *)
      match snd info with
      | { typ = Func ft; _ } ->
          check_inline_type ctx ~location:typ.info ft sign;
          Some (def_id (fst info), typ.desc)
      | _ ->
          Error.expected_func_type ctx.diagnostics ~location:typ.info;
          None)
  | None -> (
      match sign with
      | Some sign ->
          let name =
            { (name : Ast.ident) with desc = "<func:" ^ name.desc ^ ">" }
          in
          let+@ i =
            (* [add_type] runs the [functype] converter, which already checks
                 parameter-name uniqueness, so [sign] needs no separate
                 [funsig] pass here (that would report duplicates twice). *)
            add_type ctx.diagnostics ctx.type_context
              [|
                Ast.no_loc
                  ( name,
                    {
                      supertype = None;
                      typ = Func sign;
                      final = true;
                      descriptor = None;
                      describes = None;
                    } );
              |]
          in
          (i, name.desc)
      | None -> assert false)

(* Register a function (defined or imported) under [name]. A signature that
   fails to resolve still CLAIMS the name, as a poison entry ([None]): its
   uses resolve quietly to [Error] instead of cascading into unbound-name
   reports, and its body is still checked (see [functions]) — the Wax mirror
   of the validator's poisoned index entries. A duplicate name registers
   nothing (the first entry stands; [Tbl.exists] reports the clash). *)
let register_function ctx d name typ sign ~exact ~import =
  if not (Tbl.exists d ctx.functions name) then begin
    (* A defined function's signature is a reference *it* makes, so attribute the
       types it names to the function rather than letting a dead function's type
       look externally referenced. An IMPORT has no body: its signature is a
       module-level reference, hence a root — as in the validator, and as for an
       imported global's or tag's type here. *)
    let outer = !(ctx.origin) in
    if (not import) && outer <> Ignored then
      ctx.origin := From_function name.desc;
    let entry =
      Option.map (fun (i, n) -> (i, n, exact)) (fundecl_typ ctx name typ sign)
    in
    ctx.origin := outer;
    Tbl.add d ctx.functions name entry
  end

let field_attributes (field : _ modulefield) =
  match field with
  | Func { attributes; _ }
  | Global { attributes; _ }
  | Tag { attributes; _ }
  | Memory { attributes; _ }
  | Data { attributes; _ }
  | Table { attributes; _ }
  | Elem { attributes; _ }
  | Module_annotation attributes ->
      attributes
  (* An import's attributes hang off each [import_decl]; they are validated
     while walking the import, not through [field_attributes]. *)
  | Type _ | Conditional _ | Import _ | Import_group _ -> []

(* Reject unknown attributes and validate the value shape of the ones that are
   allowed on the entity carrying them. [import_ok] is set for the declarations
   inside an [import "module" { ... }] block, where a name-only
   [#[import = "name"]] overrides the imported name. *)
let check_attribute_list diagnostics ~export_ok ~start_ok ~module_ok ~import_ok
    ?(priority_ok = false) (attributes : Ast.attributes) =
  List.iter
    (fun ({
            attr_name = name;
            attr_value = value;
            attr_guard = guard;
            attr_span;
          } :
           Ast.attribute) ->
      (* The whole [#[...]]. A valueless attribute ([#[start]], [#[run_once]]) has
         no value span to fall back on, and the field's span would underline the
         entire definition. A synthesized attribute carries the entity's span. *)
      let location = attr_span in
      (* A per-attribute [if <cond>] guard is only meaningful on [export] and
         [start]; blame its own [if] keyword. *)
      (match guard with
      | Some g when name <> "export" && name <> "start" ->
          Error.guard_not_allowed diagnostics ~location:g.info name
      | _ -> ());
      match name with
      | "export" ->
          (* A bare [#[export]] (no value) reuses the entity's Wax name as the
             export name; an explicit name must be a string. *)
          (match value with
          | None | Some { desc = String _; _ } -> ()
          | _ ->
              Error.annotation_value_mismatch diagnostics ~location "export"
                "a string");
          if not export_ok then
            Error.annotation_not_allowed diagnostics ~location "export"
      | "start" ->
          (match value with
          | None -> ()
          | Some _ ->
              Error.annotation_value_mismatch diagnostics ~location "start"
                "no value");
          if not start_ok then
            Error.annotation_not_allowed diagnostics ~location "start"
      | "module" ->
          (match value with
          | Some { desc = String _; _ } -> ()
          | _ ->
              Error.annotation_value_mismatch diagnostics ~location "module"
                "a string");
          if not module_ok then
            Error.annotation_not_allowed diagnostics ~location "module"
      | "feature" ->
          (match value with
          | Some { desc = String _; _ } -> ()
          | _ ->
              Error.annotation_value_mismatch diagnostics ~location "feature"
                "a string");
          (* Allowed exactly where [module] is: as an inner attribute. *)
          if not module_ok then
            Error.annotation_not_allowed diagnostics ~location "feature"
      | "import" ->
          (match value with
          | Some { desc = String _; _ } -> ()
          | _ ->
              Error.annotation_value_mismatch diagnostics ~location "import"
                "a string");
          if not import_ok then
            Error.annotation_not_allowed diagnostics ~location "import"
      (* Compilation-hints proposal: the function-level compilation priority. It
         needs a body to attach to, so it is allowed on a defined function only —
         an imported one has no code-section entry to key an offset-0 hint in. *)
      | "priority" | "optimization" ->
          (* In range as well as an integer: the section stores the priority as a
             ULEB, and an over-long literal would otherwise reach [to_wasm]'s
             [int_of_string] and crash it (as for the SIMD lane index above; the
             WAT grammar range-checks the same payload with [priority_of_nat]). *)
          (match value with
          | Some ({ desc = Int _; _ } as v)
            when Option.fold ~none:false
                   ~some:(fun l ->
                     Wax_utils.Uint64.compare l
                       (Wax_utils.Uint64.of_string "0x1_0000_0000")
                     < 0)
                   (int_literal v) ->
              ()
          | _ ->
              Error.annotation_value_mismatch diagnostics ~location name
                "an integer in the u32 range");
          if not priority_ok then
            Error.annotation_not_allowed diagnostics ~location name
      | "run_once" ->
          (match value with
          | None -> ()
          | Some _ ->
              Error.annotation_value_mismatch diagnostics ~location "run_once"
                "no value");
          if not priority_ok then
            Error.annotation_not_allowed diagnostics ~location "run_once"
      | _ -> Error.unknown_annotation diagnostics ~location name)
    attributes;
  (* The section states an optimization priority only alongside a compilation
     one, and [run_once] is just a spelling of a particular optimization value, so
     either without [#[priority]] would have nowhere to go. Reject rather than
     invent a compilation priority the author did not choose. *)
  if priority_ok then begin
    let find k =
      List.find_opt (fun (a : Ast.attribute) -> a.attr_name = k) attributes
    in
    let locate (a : Ast.attribute) = a.attr_span in
    if find "priority" = None then
      List.iter
        (fun k ->
          Option.iter
            (fun a ->
              Error.priority_required diagnostics ~location:(locate a) k)
            (find k))
        [ "optimization"; "run_once" ];
    match (find "optimization", find "run_once") with
    | Some a, Some b ->
        Error.conflicting_optimization diagnostics ~location:(locate a)
          ~prev_loc:(locate b)
    | _ -> ()
  end

(* Validate the annotations on a module field: reject unknown ones, check the
   value shape of [export] / [start] / [module], and allow each only where it is
   meaningful. *)
let check_attributes diagnostics
    (field : (_ modulefield, location) Ast.annotated) =
  let export_ok, start_ok, module_ok =
    match field.desc with
    | Func _ -> (true, true, false)
    | Global _ | Memory _ | Table _ | Tag _ -> (true, false, false)
    | Module_annotation _ -> (false, false, true)
    | Data _ | Elem _ | Type _ | Import _ | Import_group _ | Conditional _ ->
        (false, false, false)
  in
  let priority_ok = match field.desc with Func _ -> true | _ -> false in
  check_attribute_list diagnostics ~export_ok ~start_ok ~module_ok
    ~import_ok:false ~priority_ok
    (field_attributes field.desc)

(*** Type-checking a configuration ***)

let type_configuration ?(warn_unused = false) ?(build = true) ?(suggest = false)
    ?(resolve_links = None) ?(pun_spans = None) ?(member_completions = None)
    ?(faithful = false) ?(features = Wax_utils.Feature.default ()) ~simplify
    diagnostics fields =
  (* [simplify] (the Wasm->Wax rewrite that drops redundant annotations) and
     [suggest] (offering those same drops as editor quick fixes on hand-written
     Wax) are mutually exclusive: [simplify] removes the very nodes [suggest]
     would flag. The [suggest_*] helpers rely on this. *)
  if simplify && suggest then
    invalid_arg "Typing: simplify and suggest are exclusive";
  let cond = ref Cond.true_ in
  let cond_env = Cond.create () in
  let links = resolve_links in
  (* Shared by every table below, so a name resolution is attributed to the
     function whose body made it (see [Tbl.current]). *)
  let current = ref Root in
  let type_context =
    {
      internal_types = Wax_wasm.Types.create ();
      types =
        Tbl.make ~hover:hover_of_type ~current
          (Namespace.make ~links cond)
          "type";
      features;
      subtyping_info_cache = None;
    }
  in
  (* Walk module fields, recursing into groups and threading the branch
     assumption through conditionals so each [Type]/declaration is registered
     under the assumption of the branch it appears in. *)
  let rec walk_fields f fields =
    List.iter
      (fun (field : (_ modulefield, _) annotated) ->
        match field.desc with
        | Conditional { cond = c; then_fields; else_fields } ->
            with_cond_ref cond cond_env diagnostics ~location:field.info c true
              (fun () -> walk_fields f then_fields.desc);
            Option.iter
              (fun e ->
                with_cond_ref cond cond_env diagnostics ~location:field.info c
                  false (fun () -> walk_fields f e.Annot.desc))
              else_fields
        | _ -> f field)
      fields
  in
  walk_fields
    (fun (field : (_ modulefield, _) annotated) ->
      match field.desc with
      | Type rectype ->
          let _ : Wax_wasm.Types.Id.t option =
            add_type diagnostics type_context rectype
          in
          ()
      | _ -> ())
    fields;
  (* Index the struct types by their field set, so a literal whose name is
     omitted can be resolved from its fields. All types are registered above, so
     this is complete; a later distinct name for the same key marks it ambiguous
     ([None]), while a conditional variant of the same name does not. *)
  let structs_by_fields = Hashtbl.create 16 in
  Tbl.iter type_context.types (fun name (_, (st : subtype)) ->
      match st.typ with
      | Struct sfields -> (
          let key =
            field_set_key
              (Array.to_list (Array.map (fun f -> (field_name f).desc) sfields))
          in
          match Hashtbl.find_opt structs_by_fields key with
          | None ->
              Hashtbl.replace structs_by_fields key (Some (Ast.no_loc name))
          | Some (Some n) when n.desc = name -> ()
          | Some _ -> Hashtbl.replace structs_by_fields key None)
      | Func _ | Array _ | Cont _ -> ());
  let ctx =
    let namespace = Namespace.make ~links cond in
    {
      diagnostics;
      type_context;
      types = type_context.types;
      structs_by_fields;
      not_expression_reported = Hashtbl.create 16;
      functions = Tbl.make ~current namespace "function";
      globals = Tbl.make ~hover:hover_of_global ~current namespace "global";
      import_globals =
        Tbl.make ~hover:hover_of_global ~current namespace "global";
      assigned_globals = Hashtbl.create 16;
      cast_traps_reported = Hashtbl.create 16;
      canonical_type_references = ref [];
      origin = current;
      memories = Tbl.make ~current namespace "memory";
      datas = Tbl.make ~current (Namespace.make ~links cond) "data segment";
      tables = Tbl.make ~current namespace "table";
      elems = Tbl.make ~current (Namespace.make ~links cond) "element segment";
      tags = Tbl.make ~current (Namespace.make ~links cond) "tag";
      locals = StringMap.empty;
      warn_unused;
      missing_holes = ref [];
      unresolved_label = ref false;
      read_locals = ref IntSet.empty;
      local_decls = ref [];
      used_labels = ref IntSet.empty;
      deferred_lints = ref [];
      label_decls = [];
      assigned_locals = StringSet.empty;
      initialized_locals = StringSet.empty;
      deferred_uninit = [];
      control_types = [];
      return_types = [||];
      cond;
      cond_env;
      resolve_links = links;
      pun_spans;
      member_completions;
      simplify;
      suggest;
      faithful;
    }
  in
  check_type_definitions ctx;
  let memory_index = ref 0 in
  (* Register a tag's type from its [typ]/[sign], shared by imported and defined
     tags. *)
  let register_tag name typ sign =
    let>@ typ =
      match (typ, sign) with
      | Some typ, _ -> (
          let*@ info = Tbl.find ctx.diagnostics ctx.types typ in
          match snd info with
          | { typ = Func ft; _ } ->
              check_inline_type ctx ~location:typ.info ft sign;
              Some ft
          | _ ->
              Error.expected_func_type ctx.diagnostics ~location:typ.info;
              None)
      | None, Some sign -> Some (funsig ctx sign)
      | None, None -> assert false
    in
    Tbl.add diagnostics ctx.tags name typ
  in
  (* A table's element type is stored as written, so resolve it here for its two
     side effects: an unbound type name is reported by the typer itself (rather
     than only later, by the lowering, which is what the whole type-checking pass
     exists to pre-empt), and a type named only as a table's element type counts
     as used — as it does in the validator. *)
  let resolve_table_reftype rt = ignore (internalize_valtype ctx (Ref rt)) in
  (* Register an imported entity under its Wax name. *)
  let register_import (decl : Ast.import_decl) =
    match decl.kind with
    | Import_func { typ; sign; exact } ->
        register_function ctx diagnostics decl.id typ sign ~exact ~import:true
    | Import_global { mut; typ } ->
        let>@ typ = internalize_valtype ctx typ in
        Tbl.add diagnostics ctx.globals decl.id (mut, Some typ)
    | Import_tag { typ; sign } -> register_tag decl.id typ sign
    | Import_memory { address_type; _ } ->
        let i = !memory_index in
        incr memory_index;
        Tbl.add diagnostics ctx.memories decl.id (i, address_type)
    | Import_table { address_type; reftype = rt; _ } ->
        resolve_table_reftype rt;
        Tbl.add diagnostics ctx.tables decl.id (address_type, rt)
  in
  walk_fields
    (fun field ->
      match field.desc with
      | Memory { name; address_type; data; _ } ->
          let i = !memory_index in
          incr memory_index;
          Tbl.add diagnostics ctx.memories name (i, address_type);
          List.iter
            (fun (d : _ Ast.memdata) ->
              Option.iter
                (fun n -> Tbl.add diagnostics ctx.datas n ())
                d.data_name)
            data
      | Import { decl; _ } -> register_import decl.desc
      | Import_group { decls; _ } ->
          List.iter
            (fun (d : (Ast.import_decl, location) Ast.annotated) ->
              register_import d.desc)
            decls
      | Func { name; typ; sign; _ } ->
          (* A module-defined function has exactly its declared type, so a
             reference to it is exact — but exact reference types are part of
             custom-descriptors; without it, type it as the plain inexact
             reference, as before the proposal. *)
          let exact =
            Wax_utils.Feature.is_enabled ctx.type_context.features
              Wax_utils.Feature.Custom_descriptors
          in
          register_function ctx diagnostics name typ sign ~exact ~import:false
      | Tag { name; typ; sign; _ } -> register_tag name typ sign
      | Data { name; _ } ->
          Option.iter (fun n -> Tbl.add diagnostics ctx.datas n ()) name
      | Table { name; address_type; reftype = rt; _ } ->
          resolve_table_reftype rt;
          Tbl.add diagnostics ctx.tables name (address_type, rt)
      | Elem { name; reftype = rt; _ } -> Tbl.add diagnostics ctx.elems name rt
      | Conditional _ | Type _ | Global _ | Module_annotation _ -> ())
    fields;
  (* A module may not export the same name twice. Each [#[export = "..."]]
     attribute is one export; [walk_fields] descends into groups and resolves
     conditionals per branch, so exports in mutually exclusive branches do not
     clash. *)
  let exports = Hashtbl.create 16 in
  (* The conditions under which a [#[start]] has been seen; like [exports], a
     second start clashes only when its condition can hold at the same time. *)
  let starts = ref [] in
  let module_seen = ref None in
  (* The Wax name a bare [#[export]] reuses as its export name. *)
  let field_name (field : (_ modulefield, location) Ast.annotated) =
    match field.desc with
    | Func { name; _ }
    | Global { name; _ }
    | Memory { name; _ }
    | Table { name; _ }
    | Tag { name; _ } ->
        Some name
    | Data _ | Elem _ | Import _ | Import_group _ | Conditional _ | Type _
    | Module_annotation _ ->
        None
  in
  (* Process the [export]/[start]/[module] attributes carried by an entity whose
     Wax name is [default_name] (used as the export name of a bare [#[export]]).
     [location] blames the entity when an attribute carries no value. *)
  let process_attrs ~default_name ~location attributes =
    List.iter
      (fun ({ attr_name = key; attr_value = v; attr_guard = guard; _ } :
             Ast.attribute) ->
        (* The condition under which this attribute is actually present: the
           field's own branch assumption ([!cond]) narrowed by an optional
           per-attribute [if <cond>] guard (only [export]/[start] carry one). *)
        let cond =
          match guard with
          | None -> !cond
          | Some g ->
              Cond.and_ !cond
                (Cond.of_cond cond_env diagnostics ~location:g.info g.desc)
        in
        match (key, Option.map (fun (v : _ instr) -> v.desc) v) with
        | "export", ((Some (String _) | None) as value) ->
            (* The export name and the location to blame: the explicit string
               for [#[export = "nm"]], the entity's own name for a bare
               [#[export]]. *)
            let entry =
              match value with
              | Some (String (_, name)) -> Some (name, (Option.get v).info)
              | _ -> (
                  match default_name with
                  | Some (id : ident) -> Some (id.desc, id.info)
                  | None -> None)
            in
            Option.iter
              (fun (name, location) ->
                (* Two exports of the same name clash only when the conditions
                   guarding them can hold at once; the same name in mutually
                   exclusive branches is fine. Each remembered guard is the
                   condition under which an export was seen. *)
                let guards =
                  Option.value ~default:[] (Hashtbl.find_opt exports name)
                in
                (match
                   List.find_opt
                     (fun (g, _) -> Cond.is_satisfiable (Cond.and_ g cond))
                     guards
                 with
                | Some (_, prev_loc) ->
                    Error.duplicated_export diagnostics ~location ~prev_loc name
                | None -> ());
                Hashtbl.replace exports name ((cond, location) :: guards))
              entry
        | "start", _ ->
            (* A module may name at most one start function per configuration;
               starts in mutually exclusive branches are fine. *)
            (match
               List.find_opt
                 (fun (g, _) -> Cond.is_satisfiable (Cond.and_ g cond))
                 !starts
             with
            | Some (_, prev_loc) ->
                Error.multiple_start diagnostics ~location ~prev_loc
            | None -> ());
            starts := (cond, location) :: !starts
        | "module", _ -> (
            (* A module may carry at most one name annotation. *)
            match !module_seen with
            | Some prev_loc ->
                Error.multiple_module diagnostics ~location ~prev_loc
            | None -> module_seen := Some location)
        | _ -> ())
      attributes
  in
  (* Validate and process the attributes on one imported declaration: a
     name-only [#[import = "name"]] override and [#[export]] (a re-export) are
     meaningful there. *)
  let check_import_decl (decl : (Ast.import_decl, location) annotated) =
    (* An imported function may be the module's start function; other imported
       kinds cannot. *)
    let start_ok =
      match decl.desc.kind with Import_func _ -> true | _ -> false
    in
    check_attribute_list diagnostics ~export_ok:true ~start_ok ~module_ok:false
      ~import_ok:true decl.desc.attributes;
    (* A [#[start]] import, like a defined start function, must have no
       parameters and no results (the import was registered above, so its type
       is resolvable). *)
    if
      start_ok
      && List.exists (fun a -> a.Ast.attr_name = "start") decl.desc.attributes
    then begin
      let name = decl.desc.id in
      let func_typ =
        let*@ entry = Tbl.find ctx.diagnostics ctx.functions name in
        (* A poison entry: the signature failure was already reported. *)
        let*@ _, tname, _ = entry in
        let*@ _, ty =
          Tbl.find ctx.diagnostics ctx.types { name with desc = tname }
        in
        match ty.typ with Func typ -> Some typ | _ -> None
      in
      match func_typ with
      | Some ft when Array.length ft.params = 0 && Array.length ft.results = 0
        ->
          ()
      | Some _ ->
          Error.start_function_signature ctx.diagnostics ~location:name.info
      | None -> ()
    end;
    (match
       List.filter (fun a -> a.Ast.attr_name = "import") decl.desc.attributes
     with
    | first :: (a : Ast.attribute) :: _ ->
        Error.multiple_import diagnostics ~location:a.attr_span
          ~prev_loc:first.attr_span
    | _ -> ());
    (* An imported memory/table still has size limits to validate, the same as
       a defined one. *)
    (match decl.desc.kind with
    | Import_memory { address_type; limits; page_size_log2; shared } ->
        check_limits ctx ~location:decl.info "memory" ~shared address_type
          page_size_log2 limits max_memory_size
    | Import_table { address_type; limits; _ } ->
        check_limits ctx ~location:decl.info "table" ~shared:false address_type
          None limits max_table_size
    | Import_func _ | Import_global _ | Import_tag _ -> ());
    process_attrs ~default_name:(Some decl.desc.id) ~location:decl.info
      decl.desc.attributes
  in
  walk_fields
    (fun field ->
      check_attributes diagnostics field;
      match field.desc with
      | Import { decl; _ } -> check_import_decl decl
      | Import_group { decls; _ } -> List.iter check_import_decl decls
      | _ ->
          process_attrs ~default_name:(field_name field) ~location:field.info
            (field_attributes field.desc))
    fields;
  let _ : _ option =
    let name = Ast.no_loc "<string>" in
    add_type ctx.diagnostics ctx.type_context
      [|
        Ast.no_loc
          ( name,
            {
              supertype = None;
              typ = Array { mut = true; typ = Packed I8 };
              final = true;
              descriptor = None;
              describes = None;
            } );
      |]
  in
  let ctx =
    {
      ctx with
      (* Only imports are registered at this point; snapshot them as the global
         scope visible to table initializers. *)
      import_globals = { ctx.globals with tbl = Hashtbl.copy ctx.globals.tbl };
    }
  in
  let phased_fields = globals ctx fields in
  (* Global initializers are fully typed now; run their deferred lints (see
     [ctx.deferred_lints]) before the function bodies, keeping every diagnostic
     in source order. *)
  Typing_lint.flush_deferred_lints ctx;
  let typed_fields = functions ctx phased_fields in
  (* Report module fields that are defined but never referenced (the module-level
     analog of an unused local). A field is exempt if its name starts with [_], if
     it is exported or is the start function (both externally reachable), or if it
     is an import (an external contract, not a definition; those are
     [Fundecl]/[GlobalDecl] and never reach the arms below). Uses are collected by
     [Tbl.resolve] as names are looked up while typing the globals and function
     bodies above.

     Then report the mutable ([let]) globals never assigned, which could be
     [const] instead. *)
  if warn_unused then begin
    (* Resolve the by-canonical type references (a string literal's [mut i8]
       array) against the definitions that deduplicated onto them, once, before
       any of the reference graphs below are read. *)
    (match !(ctx.canonical_type_references) with
    | [] -> ()
    | refs ->
        Tbl.iter_entries ctx.types (fun name (r, _) ->
            match (r : Wax_wasm.Types.ref_index) with
            | Def id ->
                List.iter
                  (fun (origin, id') ->
                    if Wax_wasm.Types.Id.equal id id' then
                      Tbl.mark_reference ctx.types name origin)
                  refs
            | Rec _ -> ()));
    let exempt field =
      List.exists
        (fun (a : Ast.attribute) ->
          a.attr_name = "export" || a.attr_name = "start")
        (field_attributes field)
    in
    (* A leading [_] marks a declaration as deliberately unused (and, for a
       global, deliberately as written), exempting it from these lints. *)
    let intentional (name : ident) =
      String.length name.desc > 0 && name.desc.[0] = '_'
    in
    (* Close a name-keyed reference graph: [live] is everything reachable from
       [seeds] through the edges [edges_of] yields for each node. *)
    let closure ~edges_of seeds =
      let live = Hashtbl.create 16 in
      let rec visit n =
        if not (Hashtbl.mem live n) then begin
          Hashtbl.replace live n ();
          List.iter visit (edges_of n)
        end
      in
      List.iter visit seeds;
      live
    in
    (* The functions that can actually run: those reachable from outside
       (exported, or the start function) or referenced from a module-level context
       (a global or table initializer, a segment — recorded as [Root]), plus
       everything those transitively call or take a [&f] of.

       Reachability, not the mere presence of a reference, is what lets the lint
       see a dead *cycle*: two functions that only call each other reference one
       another, so a presence check finds both used, yet neither can ever run —
       and the same goes for anything only such a cycle reaches. Taking a
       function reference counts as calling it, since where the reference ends up
       is not tracked, so the analysis never reports a function that might run. *)
    let live_functions =
      let calls = Hashtbl.create 16 in
      let seeds = ref [] in
      Tbl.iter_references ctx.functions (fun referrer callee ->
          match referrer with
          | From_function caller -> Hashtbl.add calls caller callee
          | Root -> seeds := callee :: !seeds
          (* Only types reference types, so a type definition never names a
             function; treat it as a root rather than losing the reference. *)
          | From_type _ -> seeds := callee :: !seeds
          | Ignored -> ());
      walk_fields
        (fun field ->
          match field.desc with
          | Func { name; _ } when exempt field.desc ->
              seeds := name.desc :: !seeds
          | _ -> ())
        fields;
      closure ~edges_of:(Hashtbl.find_all calls) !seeds
    in
    (* Referenced by a module-level context, or by something that can run. A
       reference from dead code keeps nothing alive. *)
    let live_origin = function
      | Root -> true
      | From_function f -> Hashtbl.mem live_functions f
      | From_type _ | Ignored -> false
    in
    let used tbl (name : ident) =
      List.exists live_origin (Tbl.referrers tbl name.desc)
    in
    (* The types anything reachable names, closed over the references a type
       definition makes through its own components (its supertype, field and
       element types, a descriptor clause) — so a rec group nothing outside it
       names is dead as a whole, its mutual references notwithstanding. *)
    let live_types =
      let components = Hashtbl.create 16 in
      let seeds = ref [] in
      Tbl.iter_references ctx.types (fun referrer target ->
          match referrer with
          | From_type src -> Hashtbl.add components src target
          | Root | From_function _ ->
              if live_origin referrer then seeds := target :: !seeds
          | Ignored -> ());
      closure ~edges_of:(Hashtbl.find_all components) !seeds
    in
    let unused tbl (name : ident) =
      (not (intentional name)) && not (used tbl name)
    in
    (* A defined field of any kind: report it at its name unless exempt. *)
    let check_unused field tbl kind (name : ident) =
      if (not (exempt field)) && unused tbl name then
        Error.unused_field ctx.diagnostics ~location:name.info kind name
    in
    (* An import that is never referenced (and not re-exported) is reported, the
       same way an unused definition is. *)
    let check_unused_import (decl : (Ast.import_decl, location) annotated) =
      let exempt =
        List.exists
          (fun (a : Ast.attribute) ->
            a.attr_name = "export" || a.attr_name = "start")
          decl.desc.attributes
      in
      let report tbl kind =
        if unused tbl decl.desc.id then
          Error.unused_import ctx.diagnostics ~location:decl.desc.id.info kind
            decl.desc.id
      in
      if not exempt then
        match decl.desc.kind with
        | Import_func _ -> report ctx.functions "function"
        | Import_global _ -> report ctx.globals "global"
        | Import_memory _ -> report ctx.memories "memory"
        | Import_table _ -> report ctx.tables "table"
        | Import_tag _ -> report ctx.tags "tag"
    in
    walk_fields
      (fun field ->
        match field.desc with
        | Func { name; _ } ->
            check_unused field.desc ctx.functions "function" name
        | Global { name; mut; _ } ->
            check_unused field.desc ctx.globals "global" name;
            (* A global not used at all is already reported just above, so do not
               pile a second diagnostic on the same declaration; an exported one
               may be assigned by the host. *)
            if
              mut
              && (not (intentional name))
              && (not (exempt field.desc))
              && used ctx.globals name
              && not (Hashtbl.mem ctx.assigned_globals name.desc)
            then Error.unnecessary_mut ctx.diagnostics ~location:name.info name
        | Memory { name; _ } ->
            check_unused field.desc ctx.memories "memory" name
        | Table { name; _ } -> check_unused field.desc ctx.tables "table" name
        | Tag { name; _ } -> check_unused field.desc ctx.tags "tag" name
        (* An active segment runs at instantiation, so only a passive one can be
           unused: it is reachable solely through [mem.init]/[tab.init] and
           [seg.drop]. *)
        | Data { name = Some name; mode = Passive; _ } ->
            check_unused field.desc ctx.datas "data segment" name
        | Elem { name; mode = EPassive; _ } ->
            check_unused field.desc ctx.elems "element segment" name
        | Import { decl; _ } -> check_unused_import decl
        | Import_group { decls; _ } -> List.iter check_unused_import decls
        (* Each member of a rec group is reported on its own; the group as a whole
           is dead only when nothing outside it names any member. *)
        | Type rectype ->
            Array.iter
              (fun elt ->
                let name = member_name elt in
                if
                  (not (intentional name))
                  && not (Hashtbl.mem live_types name.desc)
                then
                  Error.unused_field ctx.diagnostics ~location:name.info "type"
                    name)
              rectype
        | Data _ | Elem _ | Module_annotation _ | Conditional _ -> ())
      fields
  end;
  ( ctx.type_context.types,
    (* The cell-annotated tree ([inferred_module_annotation]); [f] resolves it to
       storage types for the deferred Wasm/WAT conversion, while the editor reads
       the cells directly. A validation-only pass ([~build:false]) runs the
       checking above for its diagnostics and discards it. *)
    if not build then [] else typed_fields )

(* The concrete storage type an inference cell finally takes — the resolution
   behind {!project_annotation}, factored out so the width pass below settles a
   cell exactly as the projection does (the two disagreeing would make the width
   comparison read a type the tree never takes). [Unknown]/[Error]/[Collecting]
   have no concrete type ([None]); a flexible numeric literal takes its default
   width. *)
let resolved_storagetype (ty : inferred_type) =
  match ty with
  | Unknown | Error | Collecting _ -> None
  | Null -> Some (Value (Ref { nullable = true; typ = None_ }))
  | UnknownRef -> Some (Value (Ref { nullable = false; typ = None_ }))
  | Number -> Some (Value I32)
  | Int8 -> Some (Packed I8)
  | Int16 -> Some (Packed I16)
  | Int -> Some (Value I32)
  | LargeInt -> Some (Value I64)
  | Float -> Some (Value F64)
  | Valtype { typ; _ } -> Some (Value typ)

(* Resolve the inference cells at each node to concrete storage types — the
   projection [f] applies before handing the typed tree to the Wasm conversion. *)
let project_annotation (types, loc) =
  (Array.map (fun ty -> resolved_storagetype (Cell.get ty)) types, loc)

let project_module (m : inferred_module_annotation Ast.module_) :
    typed_module_annotation Ast.module_ =
  List.map
    (fun f ->
      {
        f with
        Annot.desc = Ast_utils.map_modulefield project_annotation f.Annot.desc;
      })
    m

(* The numeric width a type states, [None] for a reference or vector (the width
   pass covers the scalars only). A packed narrow read ([i8]/[i16] — a [load8], an
   [i8] field) is an i32 value the typer tracks narrow, so it counts as [i32]:
   the pass is about the value's numeric width, and a narrow read has none of its
   own. *)
let numeric_width (ty : Ast.valtype) =
  match ty with I32 | I64 | F32 | F64 -> Some ty | Ref _ | V128 -> None

let inferred_width (ty : Ast.storagetype) =
  match ty with
  | Value ty -> numeric_width ty
  | Packed (I8 | I16) -> Some Ast.I32

(* Whether an inferred type is a FLEXIBLE numeric literal — one with no type of
   its own, which a context narrows and, with none, {!resolved_storagetype}
   defaults. Only such a value can be repaired by a pin: an identity cast grounds
   it AT the pinned width, exactly as [From_wasm]'s [Stack.pin_width] does. Every
   other numeric type is ANCHORED — resolved from a local, a call result, a merged
   context — and there the same cast would be a numeric CONVERSION changing the
   value, not a pin, so a disagreement is reported instead of repaired. The packed
   narrow reads ([Int8]/[Int16]) are anchored in exactly that sense: their value
   comes from a [load8]/[load16], and a cast on one fuses into the load rather than
   grounding a literal. *)
let flexible_literal (ty : inferred_type) =
  match ty with
  | Number | Int | LargeInt | Float -> true
  | Unknown | Error | UnknownRef | Null | Int8 | Int16 | Valtype _
  | Collecting _ ->
      false

(* Which family a numeric type belongs to. A pin only ever settles a value's WIDTH:
   taking it across this divide is a CONVERSION (in Wax it even needs a signage,
   [as f32_s]), so no repair may cross it. *)
let numeric_family (t : Ast.valtype) =
  match t with I32 | I64 -> `Int | F32 | F64 | Ref _ | V128 -> `Float

(* The family a numeric CAST accepts for its operand, which is what bounds a pin
   inserted there ([None] for a cast that is not numeric): an identity/width cast
   ([as i64], [as f32] — a wrap, extend, promote or demote) takes its own family; a
   signed conversion takes the OTHER one ([as i64_s] is a truncation, so its operand
   is a float; [as f32_s] a convert, so its operand is an integer). *)
let cast_operand_family (t : Ast.casttype) =
  match t with
  | Valtype ((I32 | I64 | F32 | F64) as t) -> Some (numeric_family t)
  | Signedtype { typ = `I32 | `I64; _ } -> Some `Float
  | Signedtype { typ = `F32 | `F64; _ } -> Some `Int
  | Valtype (Ref _ | V128) | Functype _ -> None

(* Whether a pin to [required] keeps the value in the family its own inferred type
   commits it to. A literal still free of a family ([Number], or the float-capable
   [LargeInt]) narrows either way; one an operator committed ([Int], [Float]) does
   not; and a value whose cell a cast already folded keeps the family it folded to.
   (Under a cast the bound comes from {!cast_operand_family} instead, which is
   sharper: it is the consumer, not the fold, that constrains the operand there.) *)
let pin_stays_in_family (inferred : inferred_type) ~resolved ~required =
  let integral t = numeric_family t = `Int in
  match inferred with
  | Number | LargeInt -> true
  | Int -> integral required
  | Float -> not (integral required)
  | _ -> integral resolved = integral required

(* The inference lattice's entry for a numeric base type. [None] for the types the
   width pass does not handle, which {!numeric_width} has already excluded. *)
let numeric_valtype (ty : Ast.valtype) =
  match ty with
  | I32 -> Some i32_valtype
  | I64 -> Some i64_valtype
  | F32 -> Some f32_valtype
  | F64 -> Some f64_valtype
  | Ref _ | V128 -> None

(* The offending expression, elided past a line's worth: a disagreement is
   reported against a whole operand tree, which can be large. *)
let width_expr (i : _ instr) =
  let expr = Infer.Output.instr_string i in
  if String.length expr <= 40 then expr else String.sub expr 0 40 ^ "..."

(* Reconcile the type each node's producer recorded on it (see [Ast.instr]'s
   [expected] — only {!Wax_conversion.From_wasm} records any) with the type this
   run resolves for it.

   Compares against the RESOLVED type, the one the node finally takes: a flexible
   numeric literal is only pinned to a width by {!resolved_storagetype}'s
   defaulting (int/number -> i32, large number -> i64, float -> f64), which is
   exactly the width a re-parse of the printed form would settle on. Reading the
   cell as-is would take a flexible literal for "no type yet" and miss every
   drift.

   Two outcomes, by whether a pin CAN fix the disagreement (see
   {!flexible_literal}):

   - a flexible tree resolving to the wrong width is REPAIRED under
     [`Repair] — the node is wrapped in an identity cast to the recorded type, the
     grounding pin [From_wasm] should have placed, so the printed Wax re-infers the
     width the Wasm states. The cell is grounded with it ([Cell.set]), which is
     what makes one pass converge: the cells of a flexible tree are UNIFIED, so
     grounding the outermost node's cell settles every node beneath it and their
     own (identical) expectations are then met — no second pin inside the tree the
     first one already grounds. Under [`Report] it is reported instead, which is
     what keeps the fuzz harness able to see a missing [From_wasm] pin
     ([--debug width-check], oracle 5c) rather than a silently healed one.
   - an ANCHORED type that disagrees is reported in BOTH modes: no cast can fix it
     (one would convert the value), so it is either an invalid input — a binary is
     trusted, never validated, so its operands need not be what its opcodes name —
     or a conversion bug that must be fixed at the source.

   Runs after the whole module is typed and after [simplify]'s rewrites, which is
   also why an inserted pin cannot oscillate with [simplify]'s redundant-cast
   pruning: pruning has already happened, in the typing pass proper, and nothing
   re-enters it. A repair is by construction NOT redundant — the cast is what
   changes the tree's resolved type — so a later re-type of the printed Wax keeps
   it (and if it ever did become redundant, the [simplify] of a fresh decompile
   would drop it and this pass would put it back only if it were still needed).

   A node with no resolved type ([Unknown]/[Error] — a hole in unreachable code
   the typer left polymorphic) is left alone: nothing was resolved to disagree
   with, and pinning it would invent a type where the Wasm side is polymorphic
   too. So is a node that leaves no value or several. *)
(* The type a cast ASCRIBES to its operand in the printed form: only an
   identity/width cast states its operand's type ([_ as i64] makes the operand an
   i64), and that is what a re-parse reads. A signed conversion states its RESULT's
   ([_ as i64_s] is a truncation of a float), so it ascribes nothing to the operand
   and a value under it still needs its own record honoured. *)
let ascribed_type (t : Ast.casttype) =
  match t with Valtype ((I32 | I64 | F32 | F64) as t) -> Some t | _ -> None

let rec reconcile_widths mode diagnostics ~under_cast ~ascribed (i : _ instr) :
    _ instr =
  (* The recording-gap census ([--debug width-record]). A numeric-valued node
     whose expectation is [Unset] — as opposed to a deliberate [Contextual] —
     was never seen by any of [From_wasm]'s recording choke points: the one
     class of width bug that is INVISIBLE to the reconciliation below by
     construction (nothing recorded, nothing to disagree with), so it can only
     drift silently. This census makes the class enumerable: run a decompile
     under the flag and every line is either an emission path that must record
     what its opcode states, or a node synthesized after the conversion (whose
     width the synthesizing pass itself guarantees) to be marked [Contextual]
     at its construction site. Reports [v128] too: a record there is what tells
     {!Wax_conversion.From_wasm}'s [Stack.effective_backing] the value is not a
     reference, so an unrecorded one is a gap even though no width check ever
     fires on it. *)
  (if Wax_utils.Debug.is_enabled Width_record then
     match (i.expected, i.info) with
     | Unset, ([| cell |], location) -> (
         match resolved_storagetype (Cell.get cell) with
         | Some (Value ((I32 | I64 | F32 | F64 | V128) as t)) ->
             let p = location.loc_start in
             Printf.eprintf "width-record: %s: unrecorded %s value: %s\n%!"
               (if p.Lexing.pos_lnum = 0 then "<no loc>"
                else
                  Printf.sprintf "%s:%d:%d" p.Lexing.pos_fname p.Lexing.pos_lnum
                    (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1))
               (Infer.Output.valtype_string t)
               (width_expr i)
         | Some (Value (Ref _)) | Some (Packed _) | None -> ())
     | _ -> ());
  (* This node first: a repair here grounds the cell its whole flexible subtree
     shares, so the recursion below sees the settled type. *)
  let pin =
    match (i.expected, i.info) with
    | Recorded required, ([| cell |], location) -> (
        let inferred = Cell.get cell in
        match (numeric_width required, resolved_storagetype inferred) with
        | Some required, Some resolved -> (
            match (inferred_width resolved, numeric_valtype required) with
            | Some inferred_w, Some required_v when inferred_w <> required ->
                (* Can a pin correct this disagreement? Two ways in:
                   - the node is the OPERAND of a numeric cast and is a literal
                     tree ({!defaulting_tree}). The cast folded that tree to its
                     own target, so nothing but the cast ever fixed its width, and
                     re-grounding it there is inert to the consumer — the cast
                     becomes the conversion the Wasm had. Its one constraint is the
                     family it accepts ({!cast_operand_family}): a truncation takes
                     a float operand, a wrap an integer one, and a pin that crossed
                     that would not even type-check.
                   - otherwise the node's own type must be unfixed: a
                     still-flexible literal, or a tree of HOLES alone — a value the
                     Wasm side left polymorphic, so whatever type the typer settled
                     on came from its own defaulting rather than from the module.
                     (That is the dead-code case, and the type is often CONCRETE —
                     an operator pins an [Unknown] operand outright — so the cell
                     alone cannot recognise it.) A hole holds no value to convert,
                     so it is exempt from the family bound, unless it sits under a
                     cast whose own family bound applies. *)
                let hole_only = defaulting_tree ~holes_only:true i in
                let pinnable =
                  (* Under a cast the family it accepts bounds EVERY pin placed
                     there, whatever made the value pinnable. *)
                  (match under_cast with
                    | Some accepted -> accepted = numeric_family required
                    | None -> true)
                  && ((under_cast <> None && defaulting_tree i)
                     || (flexible_literal inferred || hole_only)
                        && ((hole_only && under_cast = None)
                           || pin_stays_in_family inferred ~resolved:inferred_w
                                ~required))
                in
                if pinnable && mode = `Repair then begin
                  Cell.set cell (Valtype required_v);
                  Some (required, required_v)
                end
                else begin
                  Error.width_invariant_violated diagnostics ~location
                    ~inferred:(Some inferred_w) ~required ~pinnable
                    (width_expr i);
                  None
                end
            | _ -> None)
        (* The cell is UNRESOLVED: nothing in the module fixed this value's type.
           Only the genuinely polymorphic [Unknown] is repairable here (see below
           for the other two), and only when the printed form does not already
           state the recorded type — a hole under [_ as i64] needs nothing, the
           cast IS the pin. Where nothing states it, the value's type is decided by
           the LOWERING's default for its position, and the one family of positions
           that reads an operand's type to pick an opcode — a narrow store or
           atomic RMW, whose method name carries only the access width — defaults
           to i32 ([To_wasm.atomic_op], the [StoreS] arm), so an [i64] record there
           silently narrows the store. The pin is what states it.

           Only a tree of HOLES is pinned: it holds no value, so grounding it
           invents no conversion (the same argument as in the resolved case above),
           and it is the only shape that reaches here — a live operand is typed by
           its consumer, and a dead one is a hole. Anything else falls through
           unrepaired, as before.

           [Error] is skipped: this node's own typing already failed and was
           reported, so a pin would only decorate a rejected module. [Collecting]
           is skipped too: it is not a value's cell but a block's
           result-under-inference, and [From_wasm]'s [forget_expected] clears the
           expectations of the values feeding one, so an expectation reaching it
           would mean that clearing has a hole — worth leaving visible as an
           unrepaired case rather than papering over with a pin. (Measured over
           300+ corpus modules: no expectation reaches either.) *)
        | Some required, None -> (
            match (inferred, numeric_valtype required) with
            | Unknown, Some required_v
              when ascribed <> Some required
                   && (match under_cast with
                     | Some accepted -> accepted = numeric_family required
                     | None -> true)
                   && defaulting_tree ~holes_only:true i ->
                if mode = `Repair then begin
                  Cell.set cell (Valtype required_v);
                  Some (required, required_v)
                end
                else begin
                  Error.width_invariant_violated diagnostics ~location
                    ~inferred:None ~required ~pinnable:true (width_expr i);
                  None
                end
            | _ -> None)
        | _ -> None)
    | _ -> None
  in
  let sub = reconcile_widths mode diagnostics in
  let i =
    {
      i with
      desc =
        (match i.desc with
        (* A numeric cast constrains its operand only by FAMILY, so a pin inside
           it stays type-correct — unlike an operand a call or method signature
           fixes, where a pin would make the call ill-typed. That is the one
           position where a folded literal tree is still repairable, and the family
           it accepts travels with the recursion. *)
        | Cast (e, t) when cast_operand_family t <> None ->
            Cast
              ( sub ~under_cast:(cast_operand_family t)
                  ~ascribed:(ascribed_type t) e,
                t )
        | desc ->
            Ast_utils.map_desc
              ~instr:(sub ~under_cast:None ~ascribed:None)
              ~block:(Ast_utils.smart_map (sub ~under_cast:None ~ascribed:None))
              desc);
    }
  in
  match pin with
  | None -> i
  | Some (required, required_v) ->
      (* The pin takes the node's span (as [From_wasm]'s own pins do, so the source
         trivia still lands on it) and the recorded type as its own; the
         instruction's own hints stay on the instruction. It carries no claim
         of its own — the one it was inserted for is now met — and is
         [Contextual], not [Unset]: this pass guarantees its width itself, so
         the recording-gap census must not report it. *)
      {
        desc = Cast (i, Valtype required);
        info = ([| valtype_cell required_v |], snd i.info);
        hints = Wax_wasm.Hints.none;
        expected = Contextual;
      }

let reconcile_module_widths mode diagnostics
    (m : inferred_module_annotation Ast.module_) =
  if mode = `Off then m
  else
    List.map
      (fun (f : (_ modulefield, location) Ast.annotated) ->
        {
          f with
          Annot.desc =
            Ast_utils.map_modulefield_instr
              (reconcile_widths mode diagnostics ~under_cast:None ~ascribed:None)
              f.Annot.desc;
        })
      m

(* Conditional annotations denote mutually-exclusive branches, so they are
   type-checked by exploring every reachable configuration (as the WAT validator
   does), rather than checking both branches as if they coexisted. *)

(*** Conditional compilation and entry points ***)

let rec instr_has_conditional (i : _ instr) =
  match i.desc with
  | If_annotation _ -> true
  | Block { block; _ } | Loop { block; _ } | TryTable { block; _ } ->
      ihc_list block.desc
  | While { cond; step; block; _ } ->
      instr_has_conditional cond
      || Option.fold ~none:false ~some:instr_has_conditional step
      || ihc_list block.desc
  | If { cond; if_block; else_block; _ } ->
      instr_has_conditional cond || ihc_list if_block.desc
      || Option.fold ~none:false
           ~some:(fun b -> ihc_list b.Annot.desc)
           else_block
  | Try { block; catches; catch_all; _ } ->
      ihc_list block.desc
      || List.exists (fun (_, l) -> ihc_list l.Annot.desc) catches
      || Option.fold ~none:false
           ~some:(fun b -> ihc_list b.Annot.desc)
           catch_all
  | TryCatch { block; arms; _ } ->
      ihc_list block.desc
      || List.exists (fun a -> ihc_list a.arm_body.desc) arms
  | Sequence l -> ihc_list l
  | ArrayFixed (_, l) -> ihc_list l
  | Dispatch { index; arms; _ } ->
      instr_has_conditional index
      || List.exists (fun (_, body) -> ihc_list body.Annot.desc) arms
  | Match { scrutinee; arms; default } ->
      instr_has_conditional scrutinee
      || List.exists (fun (_, body) -> ihc_list body.Annot.desc) arms
      || ihc_list default.desc
  | ContBind (_, _, l)
  | Suspend (_, l)
  | Resume (_, _, l)
  | ResumeThrow (_, _, _, l)
  | ResumeThrowRef (_, _, l)
  | Switch (_, _, l)
  | Throw (_, l) ->
      ihc_list l
  | Call (a, l) | TailCall (a, l) -> instr_has_conditional a || ihc_list l
  (* A punned field ([None]) is a [Get] and carries no conditional. *)
  | Struct (_, l) ->
      List.exists
        (fun (_, i) -> Option.fold ~none:false ~some:instr_has_conditional i)
        l
  | StructDesc (d, l) ->
      instr_has_conditional d
      || List.exists
           (fun (_, i) -> Option.fold ~none:false ~some:instr_has_conditional i)
           l
  | CastDesc (a, _, b)
  | Br_on_cast_desc_eq (_, _, a, b)
  | Br_on_cast_desc_eq_fail (_, _, a, b)
  | BinOp (_, a, b)
  | Array (_, a, b)
  | ArraySegment (_, _, a, b)
  | ArrayGet (a, b)
  | StructSet (a, _, b) ->
      instr_has_conditional a || instr_has_conditional b
  | ArraySet (a, b, c) | Select (a, b, c) ->
      instr_has_conditional a || instr_has_conditional b
      || instr_has_conditional c
  | Set (_, _, i)
  | Tee (_, i)
  | Labelled (_, i)
  | Cast (i, _)
  | Test (i, _)
  | NonNull i
  | UnOp (_, i)
  | StructGet (i, _)
  | GetDescriptor i
  | StructDefaultDesc i
  | ArrayDefault (_, i)
  | Br_if (_, i)
  | On (i, _)
  | Br_table (_, i)
  | Br_on_null (_, i)
  | Br_on_non_null (_, i)
  | Br_on_cast (_, _, i)
  | Br_on_cast_fail (_, _, i)
  | ThrowRef i
  | ContNew (_, i) ->
      instr_has_conditional i
  | Let (_, i) | Br (_, i) | Return i -> ihc_opt i
  | Unreachable | Nop | Hole | Null | Get _ | Path _ | Char _ | String _ | Int _
  | Float _ | StructDefault _ ->
      false

and ihc_list l = List.exists instr_has_conditional l
and ihc_opt o = Option.fold ~none:false ~some:instr_has_conditional o

let field_has_conditional (f : (_ modulefield, _) annotated) =
  match f.desc with
  | Conditional _ -> true
  | Func { body = _, instrs; _ } -> List.exists instr_has_conditional instrs
  | Global { def; _ } -> instr_has_conditional def
  | _ -> false

(* Resolve every conditional against the assumption [asm], inlining the selected
   branch to produce a conditional-free module (groups are kept and recursed
   into). For an undetermined conditional, select [then], [enqueue] the [else]
   configuration, and [record] the chosen literal. *)
let specialize_fields env diagnostics ~enqueue ~record asm0 fields =
  let module S = Wax_wasm.Cond_solver in
  (* Resolve one conditional and return both the specialized branch and the
     assumption that holds afterwards. Each branch is taken only if it is
     reachable under [asm] (its conjunction with the branch condition is
     satisfiable); an unreachable branch is pruned, so we never explore an
     infeasible configuration. The surviving assumption is threaded into the
     following siblings, so e.g. once [cond1] forces [$wasi], a sibling
     [#[if(not wasi)]] has its [@then] pruned. *)
  let choose asm cond ~location ~then_branch ~else_branch =
    let c = S.of_cond env diagnostics ~location cond in
    let then_asm = S.and_ asm c and else_asm = S.and_ asm (S.not_ c) in
    if not (S.is_satisfiable then_asm) then (
      record (S.not_ c);
      (else_branch else_asm, else_asm))
    else if not (S.is_satisfiable else_asm) then (
      record c;
      (then_branch then_asm, then_asm))
    else (
      enqueue else_asm;
      record c;
      (then_branch then_asm, then_asm))
  in
  (* Instruction-level specializer: resolve each [If_annotation] by splicing the
     selected branch into the enclosing list; recurse into every sub-instruction
     and nested block body. [sone] is for single-instruction positions, where an
     [If_annotation] cannot appear (it is statement-only). *)
  let rec sinstrs asm l =
    match l with
    | [] -> []
    | i :: rest ->
        let instrs, asm = sinstr asm i in
        instrs @ sinstrs asm rest
  and sinstr asm (i : _ instr) =
    match i.desc with
    | If_annotation { cond; then_body; else_body } ->
        choose asm cond ~location:i.info
          ~then_branch:(fun asm' -> sinstrs asm' then_body.desc)
          ~else_branch:(fun asm' ->
            match else_body with Some e -> sinstrs asm' e.desc | None -> [])
    | desc -> ([ { i with desc = sdesc asm desc } ], asm)
  and sone asm i = match sinstr asm i with [ x ], _ -> x | _ -> assert false
  and sdesc asm (desc : _ instr_desc) : _ instr_desc =
    match desc with
    | Block { label; typ; block } ->
        Block
          { label; typ; block = { block with desc = sinstrs asm block.desc } }
    | Loop { label; typ; block } ->
        Loop
          { label; typ; block = { block with desc = sinstrs asm block.desc } }
    | While { label; cond; step; block } ->
        While
          {
            label;
            cond = sone asm cond;
            step = Option.map (sone asm) step;
            block = { block with desc = sinstrs asm block.desc };
          }
    | If { label; typ; cond; if_block; else_block } ->
        If
          {
            label;
            typ;
            cond = sone asm cond;
            if_block = { if_block with desc = sinstrs asm if_block.desc };
            else_block =
              Option.map
                (fun (b : (_ instr list, location) Ast.annotated) ->
                  { b with desc = sinstrs asm b.desc })
                else_block;
          }
    | TryTable { label; typ; catches; block } ->
        TryTable
          {
            label;
            typ;
            catches;
            block = { block with desc = sinstrs asm block.desc };
          }
    | Try { label; typ; block; catches; catch_all } ->
        Try
          {
            label;
            typ;
            block = { block with desc = sinstrs asm block.desc };
            catches =
              List.map
                (fun (t, l) ->
                  (t, { l with Annot.desc = sinstrs asm l.Annot.desc }))
                catches;
            catch_all =
              Option.map
                (fun b -> { b with Annot.desc = sinstrs asm b.Annot.desc })
                catch_all;
          }
    | TryCatch { label; typ; block; arms } ->
        TryCatch
          {
            label;
            typ;
            block = { block with desc = sinstrs asm block.desc };
            arms =
              List.map
                (fun a ->
                  {
                    a with
                    arm_body =
                      { a.arm_body with desc = sinstrs asm a.arm_body.desc };
                  })
                arms;
          }
    | Set (idx, op, v) -> Set (idx, op, sone asm v)
    | Tee (idx, v) -> Tee (idx, sone asm v)
    | Labelled (l, v) -> Labelled (l, sone asm v)
    | Call (t, args) -> Call (sone asm t, List.map (sone asm) args)
    | TailCall (t, args) -> TailCall (sone asm t, List.map (sone asm) args)
    | Cast (v, t) -> Cast (sone asm v, t)
    | CastDesc (v, t, d) -> CastDesc (sone asm v, t, sone asm d)
    | Test (v, t) -> Test (sone asm v, t)
    | NonNull v -> NonNull (sone asm v)
    | Struct (idx, fields) ->
        Struct
          (idx, List.map (fun (i, v) -> (i, Option.map (sone asm) v)) fields)
    | StructDesc (d, fields) ->
        StructDesc
          ( sone asm d,
            List.map (fun (i, v) -> (i, Option.map (sone asm) v)) fields )
    | StructDefaultDesc d -> StructDefaultDesc (sone asm d)
    | StructGet (v, idx) -> StructGet (sone asm v, idx)
    | GetDescriptor v -> GetDescriptor (sone asm v)
    | StructSet (v, idx, w) -> StructSet (sone asm v, idx, sone asm w)
    | Array (idx, a, b) -> Array (idx, sone asm a, sone asm b)
    | ArrayDefault (idx, v) -> ArrayDefault (idx, sone asm v)
    | ArrayFixed (idx, l) -> ArrayFixed (idx, List.map (sone asm) l)
    | ArraySegment (idx, d, a, b) ->
        ArraySegment (idx, d, sone asm a, sone asm b)
    | ArrayGet (a, b) -> ArrayGet (sone asm a, sone asm b)
    | ArraySet (a, b, c) -> ArraySet (sone asm a, sone asm b, sone asm c)
    | BinOp (op, a, b) -> BinOp (op, sone asm a, sone asm b)
    | UnOp (op, v) -> UnOp (op, sone asm v)
    | Let (bs, body) -> Let (bs, Option.map (sone asm) body)
    | Br (l, v) -> Br (l, Option.map (sone asm) v)
    | Br_if (l, v) -> Br_if (l, sone asm v)
    | On (v, h) -> On (sone asm v, h)
    | Br_table (ls, v) -> Br_table (ls, sone asm v)
    | Dispatch { index; cases; default; arms } ->
        Dispatch
          {
            index = sone asm index;
            cases;
            default;
            arms =
              List.map
                (fun (l, body) ->
                  (l, { body with Annot.desc = sinstrs asm body.Annot.desc }))
                arms;
          }
    | Match { scrutinee; arms; default } ->
        Match
          {
            scrutinee = sone asm scrutinee;
            arms =
              List.map
                (fun (pat, body) ->
                  (pat, { body with Annot.desc = sinstrs asm body.Annot.desc }))
                arms;
            default = { default with desc = sinstrs asm default.desc };
          }
    | Br_on_null (l, v) -> Br_on_null (l, sone asm v)
    | Br_on_non_null (l, v) -> Br_on_non_null (l, sone asm v)
    | Br_on_cast (l, t, v) -> Br_on_cast (l, t, sone asm v)
    | Br_on_cast_fail (l, t, v) -> Br_on_cast_fail (l, t, sone asm v)
    | Br_on_cast_desc_eq (l, t, v, d) ->
        Br_on_cast_desc_eq (l, t, sone asm v, sone asm d)
    | Br_on_cast_desc_eq_fail (l, t, v, d) ->
        Br_on_cast_desc_eq_fail (l, t, sone asm v, sone asm d)
    | Throw (idx, v) -> Throw (idx, List.map (sone asm) v)
    | ThrowRef v -> ThrowRef (sone asm v)
    | ContNew (ct, v) -> ContNew (ct, sone asm v)
    | ContBind (src, dst, l) -> ContBind (src, dst, List.map (sone asm) l)
    | Suspend (tag, l) -> Suspend (tag, List.map (sone asm) l)
    | Resume (ct, h, l) -> Resume (ct, h, List.map (sone asm) l)
    | ResumeThrow (ct, tag, h, l) ->
        ResumeThrow (ct, tag, h, List.map (sone asm) l)
    | ResumeThrowRef (ct, h, l) -> ResumeThrowRef (ct, h, List.map (sone asm) l)
    | Switch (ct, tag, l) -> Switch (ct, tag, List.map (sone asm) l)
    | Return v -> Return (Option.map (sone asm) v)
    | Sequence l -> Sequence (sinstrs asm l)
    | Select (c, t, e) -> Select (sone asm c, sone asm t, sone asm e)
    | If_annotation _ -> assert false (* handled in [sinstr] *)
    | ( Unreachable | Nop | Hole | Null | Get _ | Path _ | Char _ | String _
      | Int _ | Float _ | StructDefault _ ) as x ->
        x
  in
  (* Resolve each per-attribute [if <cond>] guard against the configuration.
     A guard gates the presence of just this export, so it partitions the space
     exactly like an [#[if]] block: [choose] prunes the export in configurations
     where the guard cannot hold and enqueues the complementary configuration
     where it does not, threading the surviving assumption into later fields. The
     guard itself is dropped -- in each explored configuration the export is
     unconditionally present or absent. *)
  let sattrs asm (attrs : attributes) : attributes * S.t =
    List.fold_left
      (fun (acc, asm) (a : Ast.attribute) ->
        match a.attr_guard with
        | None -> (acc @ [ a ], asm)
        | Some g ->
            let kept, asm =
              choose asm g.Annot.desc ~location:g.info
                ~then_branch:(fun _ -> [ { a with attr_guard = None } ])
                ~else_branch:(fun _ -> [])
            in
            (acc @ kept, asm))
      ([], asm) attrs
  in
  let sdecl asm (decl : (Ast.import_decl, location) annotated) =
    let attributes, asm = sattrs asm decl.desc.attributes in
    ({ decl with desc = { decl.desc with attributes } }, asm)
  in
  let rec sdecls asm = function
    | [] -> ([], asm)
    | d :: rest ->
        let d, asm = sdecl asm d in
        let ds, asm = sdecls asm rest in
        (d :: ds, asm)
  in
  let rec sfields asm fl =
    match fl with
    | [] -> []
    | f :: rest ->
        let fields, asm = sfield asm f in
        fields @ sfields asm rest
  and sfield asm (f : (_ modulefield, _) annotated) =
    let sa attributes = sattrs asm attributes in
    match f.desc with
    | Conditional { cond; then_fields; else_fields } ->
        choose asm cond ~location:f.info
          ~then_branch:(fun asm' -> sfields asm' then_fields.desc)
          ~else_branch:(fun asm' ->
            match else_fields with Some e -> sfields asm' e.desc | None -> [])
    | Func ({ body = lbl, instrs; attributes; _ } as r) ->
        let attributes, asm = sa attributes in
        ( [
            {
              f with
              desc =
                Func { r with body = (lbl, sinstrs asm instrs); attributes };
            };
          ],
          asm )
    | Global ({ def; attributes; _ } as g) ->
        let attributes, asm = sa attributes in
        ( [ { f with desc = Global { g with def = sone asm def; attributes } } ],
          asm )
    | Tag ({ attributes; _ } as r) ->
        let attributes, asm = sa attributes in
        ([ { f with desc = Tag { r with attributes } } ], asm)
    | Memory ({ attributes; _ } as r) ->
        let attributes, asm = sa attributes in
        ([ { f with desc = Memory { r with attributes } } ], asm)
    | Table ({ attributes; _ } as r) ->
        let attributes, asm = sa attributes in
        ([ { f with desc = Table { r with attributes } } ], asm)
    | Import { module_; decl } ->
        let decl, asm = sdecl asm decl in
        ([ { f with desc = Import { module_; decl } } ], asm)
    | Import_group { module_; decls } ->
        let decls, asm = sdecls asm decls in
        ([ { f with desc = Import_group { module_; decls } } ], asm)
    | Module_annotation attrs ->
        let attrs, asm = sa attrs in
        ([ { f with desc = Module_annotation attrs } ], asm)
    | Type _ | Data _ | Elem _ -> ([ f ], asm)
  in
  sfields asm0 fields

(* [let] bindings are not allowed inside a conditional branch: branches are
   transparent and mutually exclusive, so a binding declared in one would leak
   past the conditional and clash with the other branch. *)
let rec check_let_in_conditionals diagnostics (i : _ instr) =
  (match i.desc with
  | If_annotation { then_body; else_body; _ } ->
      let check_branch =
        List.iter (fun (s : _ instr) ->
            match s.desc with
            (* Only a binding that introduces a name would leak; an anonymous
               [Let] ([_ = e], a drop) binds nothing, so it is allowed. *)
            | Let (bindings, _)
              when List.exists (fun (name, _) -> Option.is_some name) bindings
              ->
                Error.let_in_conditional diagnostics ~location:s.info
            | _ -> ())
      in
      check_branch then_body.desc;
      Option.iter (fun b -> check_branch b.Annot.desc) else_body
  | _ -> ());
  List.iter (check_let_in_conditionals diagnostics) (Ast_utils.sub_instrs i)

let check_let_bindings diagnostics fields =
  Ast_utils.iter_fields
    (fun (field : (_ modulefield, _) annotated) ->
      match field.desc with
      | Func { body = _, instrs; _ } ->
          List.iter (check_let_in_conditionals diagnostics) instrs
      | Global { def; _ } -> check_let_in_conditionals diagnostics def
      | _ -> ())
    fields

(* Apply the module's [#![feature = "…"]] declarations to [features]: each
   declared feature is enabled, in union with the command-line configuration —
   unless the command line explicitly disabled it, which is a conflict reported
   once, at the attribute. Runs at the entry points, before anything consults
   [is_enabled]. Only top-level attributes count: the attribute states a fact
   about the whole module, so it takes no guard and lives at the top of the
   file. An ill-shaped value (no string) is reported by [check_attribute_list]
   and ignored here. *)
let apply_declared_features diagnostics features fields =
  List.iter
    (fun (field : (_ modulefield, _) annotated) ->
      match field.desc with
      | Module_annotation attrs ->
          List.iter
            (fun (a : Ast.attribute) ->
              match (a.attr_name, a.attr_value) with
              | "feature", Some { desc = String (_, name); info = location; _ }
                -> (
                  match Wax_utils.Feature.of_name name with
                  | None -> Error.unknown_feature diagnostics ~location name
                  | Some feature ->
                      if Wax_utils.Feature.explicitly_disabled features feature
                      then Error.feature_conflict diagnostics ~location feature;
                      (* Enable it even on a conflict: the error has been
                         reported once, at the attribute; without this every
                         gated construct below would error too. *)
                      Wax_utils.Feature.declare features feature)
              | _ -> ())
            attrs
      (* A feature declaration or a module name nested in a conditional is only
         seen here, never applied: both state a module-wide fact resolved before
         any branch is specialized (a guarded module name is dropped by
         [to_wasm]'s top-level scan; a guarded feature leaves its gated
         constructs erroring). Diagnose the misplacement rather than accepting it
         silently; [check_attribute_list] otherwise allows the annotation in a
         conditional. *)
      | Conditional { then_fields; else_fields; _ } ->
          let rec reject fields =
            List.iter
              (fun (field : (_ modulefield, _) annotated) ->
                match field.desc with
                | Module_annotation attrs ->
                    List.iter
                      (fun (a : Ast.attribute) ->
                        let key = a.attr_name and location = a.attr_span in
                        if key = "feature" then
                          Error.feature_declaration_in_conditional diagnostics
                            ~location
                        else if key = "module" then
                          Error.module_name_in_conditional diagnostics ~location)
                      attrs
                | Conditional { then_fields; else_fields; _ } ->
                    reject then_fields.desc;
                    Option.iter (fun e -> reject e.Annot.desc) else_fields
                | _ -> ())
              fields
          in
          reject then_fields.desc;
          Option.iter (fun e -> reject e.Annot.desc) else_fields
      | _ -> ())
    fields

(* Check every reachable configuration of a conditional module: each is
   specialized to be conditional-free and typed independently, so a diagnostic
   is reported once with the assumption under which it is reachable. Only the
   diagnostics matter here, so the typed module is not built ([~build:false]). *)
let check_configurations ~warn_unused ~features ~simplify ~suggest ~faithful
    diagnostics (fields : location module_) =
  Wax_wasm.Cond_explore.check_all diagnostics
    ?truncation_location:
      (match fields with hd :: _ -> Some hd.info | [] -> None)
    ~explain:(fun env c -> Wax_wasm.Cond_solver.explain env ~style:`Wax c)
    ~specialize:(fun env asm ~enqueue ~record ->
      specialize_fields env diagnostics ~enqueue ~record asm fields)
    ~check:(fun ctx m ->
      ignore
        (type_configuration ~build:false ~warn_unused ~suggest ~features
           ~faithful ~simplify ctx m
          : _ * _))
    ()

let f_infer ?(simplify = false) ?(warn_unused = false) ?(suggest = false)
    ?(resolve_links = None) ?(pun_spans = None) ?(member_completions = None)
    ?(faithful = false) ?(features = Wax_utils.Feature.default ()) diagnostics
    fields =
  Wax_utils.Debug.timed "type-check" @@ fun () ->
  apply_declared_features diagnostics features fields;
  (* [check_let_bindings] reports a [let] binding inside an [(@if)] branch, which
     can only exist when the module has a conditional; gate it on that so a
     conditional-free module (the common case) skips a whole-module walk. The
     same predicate then selects the type-checking path. *)
  let has_conditional = List.exists field_has_conditional fields in
  if has_conditional then check_let_bindings diagnostics fields;
  if not has_conditional then
    type_configuration ~warn_unused ~suggest ~resolve_links ~pun_spans
      ~member_completions ~faithful ~features ~simplify diagnostics fields
  else begin
    check_configurations ~warn_unused ~features ~simplify ~suggest ~faithful
      diagnostics fields;
    (* Build the typed module (consumed only by the deferred WAT conversion and
       the editor; validation-only paths use [check] and never reach here) by
       typing the module with conditionals preserved. [type_configuration]
       resolves names per branch (condition-aware tables), so each branch is
       typed under its own assumption. Diagnostics are discarded —
       [check_configurations] above did the real checking; references are
       recorded here, off the single tree the editor consumes. *)
    type_configuration ~resolve_links ~pun_spans ~member_completions ~faithful
      ~features ~simplify
      (Wax_utils.Diagnostic.collector ())
      fields
  end

(* Report a "Trojan Source" bidirectional control character in any string the
   module carries — an export/import name or feature (in an attribute), a string
   literal, a data segment, or a conditional string. Purely syntactic; runs
   whenever the module is type-checked, shown or hidden by the warning policy. *)
let lint_confusable diagnostics fields =
  let check_str ~location s =
    match Wax_utils.Unicode.first_confusable s with
    | Some u -> Error.confusable_unicode diagnostics ~location u
    | None -> ()
  in
  let check (s : (string, location) annotated) =
    check_str ~location:s.info s.desc
  in
  let rec check_cond (c : Wax_wasm.Ast.cond) =
    match c with
    | Cond_string s -> check s
    | Cond_var _ | Cond_version _ -> ()
    | Cond_and l | Cond_or l -> List.iter check_cond l
    | Cond_not c -> check_cond c
    | Cond_cmp (_, a, b) ->
        check_cond a;
        check_cond b
  in
  let check_instr (i : _ instr) =
    match i.desc with
    | String (_, s) -> check_str ~location:i.info s
    | If_annotation { cond; _ } -> check_cond cond
    | _ -> ()
  in
  let check_body instrs = List.iter (Ast_utils.iter_instr check_instr) instrs in
  let check_attrs (attrs : attributes) =
    List.iter
      (fun (a : Ast.attribute) ->
        Option.iter (Ast_utils.iter_instr check_instr) a.attr_value;
        Option.iter
          (fun (g : (Wax_wasm.Ast.cond, location) annotated) ->
            check_cond g.desc)
          a.attr_guard)
      attrs
  in
  let check_data ~location init =
    List.iter
      (function
        | Data_string s -> check_str ~location s
        | Data_run (_, l) -> List.iter check l
        | Data_v128 _ -> ())
      init
  in
  let rec walk fields =
    List.iter
      (fun (field : (_ modulefield, location) annotated) ->
        let location = field.info in
        match field.desc with
        | Type _ -> ()
        | Func { body = _, instrs; attributes; _ } ->
            check_attrs attributes;
            check_body instrs
        | Global { def; attributes; _ } ->
            check_attrs attributes;
            check_body [ def ]
        | Tag { attributes; _ } -> check_attrs attributes
        | Memory { data; attributes; _ } ->
            check_attrs attributes;
            List.iter (fun (m : _ memdata) -> check_data ~location m.init) data
        | Data { init; attributes; _ } ->
            check_attrs attributes;
            check_data ~location init
        | Table { init; attributes; _ } ->
            check_attrs attributes;
            Option.iter (fun i -> check_body [ i ]) init
        | Elem { init; attributes; _ } ->
            check_attrs attributes;
            check_body init
        | Import { module_; decl } ->
            check module_;
            check_attrs decl.desc.attributes
        | Import_group { module_; decls } ->
            check module_;
            List.iter
              (fun (d : (import_decl, _) annotated) ->
                check_attrs d.desc.attributes)
              decls
        | Module_annotation attrs -> check_attrs attrs
        | Conditional { cond; then_fields; else_fields } ->
            check_cond cond;
            walk then_fields.desc;
            Option.iter (fun f -> walk f.Annot.desc) else_fields)
      fields
  in
  walk fields

let f ?(simplify = false) ?(warn_unused = false) ?(suggest = false)
    ?(faithful = false) ?(width_check = `Off)
    ?(features = Wax_utils.Feature.default ()) diagnostics fields =
  if warn_unused then lint_confusable diagnostics fields;
  let types, typed =
    f_infer ~simplify ~warn_unused ~suggest ~faithful ~features diagnostics
      fields
  in
  (* Reconcile the recorded widths BEFORE projecting: the pass settles the
     inference cell of whatever it pins, so the projection then reports the pinned
     width both at that node and at every node its tree shares a cell with. *)
  let typed = reconcile_module_widths width_check diagnostics typed in
  (types, project_module typed)

let check ?(warn_unused = false) ?(suggest = false)
    ?(features = Wax_utils.Feature.default ()) diagnostics fields =
  Wax_utils.Debug.timed "type-check" @@ fun () ->
  apply_declared_features diagnostics features fields;
  if warn_unused then lint_confusable diagnostics fields;
  let has_conditional = List.exists field_has_conditional fields in
  if has_conditional then check_let_bindings diagnostics fields;
  if not has_conditional then
    ignore
      (type_configuration ~build:false ~warn_unused ~suggest ~features
         ~simplify:false diagnostics fields
        : _ * _)
  else
    check_configurations ~warn_unused ~features ~simplify:false ~suggest
      ~faithful:false diagnostics fields

let erase_types m =
  List.map
    (fun (m : (_ modulefield, location) Ast.annotated) ->
      { m with desc = Ast_utils.map_modulefield snd m.desc })
    m
