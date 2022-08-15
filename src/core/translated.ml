module W = Warnings
open Ppxlib

type mutability =
  | Unknown
  | Immutable
  | Mutable
  | Dependant of (mutability list -> mutability)

type term = {
  txt : string;
  loc : Location.t;
  translation : (expression, W.t) result;
}

type check = {
  txt : string;
  loc : Location.t;
  translations : (expression * expression, W.t) result;
      (** The first expression ensures the condition holds, the second one
          contains the negative test (used when [Invalid_argument] is raised) *)
}

type invariant = {
  txt : string;
  loc : Location.t;
  translation : (string * structure_item, W.t) result;
}

type type_ = {
  name : string;
  args : type_ list;
  loc : Location.t;
  mutable_ : mutability;
  ghost : Gospel.Tast.ghost;
  models : (string * type_) list;
  invariants : invariant list;
  equality : (expression, W.t) result;
  comparison : (expression, W.t) result;
  copy : (expression, W.t) result;
}

let type_ ~name ~loc ~mutable_ ~ghost =
  {
    name;
    args = [];
    loc;
    mutable_;
    ghost;
    models = [];
    invariants = [];
    equality = Error (W.Unsupported "equality", loc);
    comparison = Error (W.Unsupported "comparison", loc);
    copy = Error (W.Unsupported "copy", loc);
  }

type ocaml_var = {
  name : string;
  label : arg_label;
  type_ : type_;
  modified : bool;
  consumed : bool;
}

type xpost = {
  exn : string;
  args : int;
  translation : (cases, W.t list) result;
}

type postcondition = {post : term; contains_returns: bool}

type value = {
  name : string;
  loc : Location.t;
  arguments : ocaml_var list;
  returns : ocaml_var list;
  register_name : string;
  ghost : Gospel.Tast.ghost;
  pure : bool;
  checks : check list;
  preconditions : term list; 
  postconditions : postcondition list;
  (*the contains_returns is only for the STM plugin, the other plugins can use any value
  *)
  xpostconditions : xpost list;
}

let value ~name ~loc ~arguments ~returns ~register_name ~ghost ~pure =
  {
    name;
    loc;
    arguments;
    returns;
    register_name;
    ghost;
    pure;
    checks = [];
    preconditions = [];
    postconditions = [];
    xpostconditions = [];
  }

type constant = {
  name : string;
  loc : Location.t;
  type_ : type_;
  register_name : string;
  ghost : Gospel.Tast.ghost;
  checks : term list;
  invariants : expression list;
}

let constant ~name ~loc ~type_ ~register_name ~ghost =
  { name; loc; type_; register_name; ghost; checks = []; invariants = [] }

type axiom = {
  name : string;
  loc : Location.t;
  register_name : string;
  definition : term;
}

type function_ = {
  name : string;
  loc : Location.t;
  rec_ : bool;
  arguments : ocaml_var list;
  definition : term option;
}

type structure_item =
  | Type of type_
  | Value of value
  | Constant of constant
  | Function of function_
  | Predicate of function_
  | Axiom of axiom
