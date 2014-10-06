open Utils

let param_gc = ref false
let param_memo = ref false
let k = ref 1

let speclist = [
  "-gc", Arg.Set param_gc,
  "Garbage collection";
  "-memo", Arg.Set param_memo,
  "Abstract memoization";
  "-k", Arg.Set_int k,
  "Polyvariance";
]

module type AddressSignature =
sig
  type t
  type time
  (** Define the ordering between two addresses *)
  val compare : t -> t -> int
  (** Convert an address to a string *)
  val to_string : t -> string
  (** Allocate a new address *)
  val alloc : string -> int -> time -> t
end

module type TimeSignature =
sig
  type t
  type arg
  val initial : t
  val compare : t -> t -> int
  val to_string : t -> string
  val tick : arg -> t -> t
end

module MakeAddress :
  functor (T : TimeSignature) -> AddressSignature with type time = T.t =
  functor (T : TimeSignature) ->
    struct
      type time = T.t
      type t = string * int * T.t
      let compare (v, tag, t) (v', tag', t') =
        order_concat [lazy (BatString.compare v v');
                      lazy (Pervasives.compare tag tag');
                      lazy (T.compare t t')]
      let to_string (v, _, t) = v ^ "@" ^ T.to_string t
      let alloc v n t = (v, n, t)
    end

module KCFATime : TimeSignature with type arg = int =
struct
  type arg = int
  type t = int list
  let initial = []
  let compare = compare_list Pervasives.compare
  let to_string t = String.concat "," (BatList.map string_of_int t)
  let tick x t = BatList.take !k (x :: t)
end

module type EnvSignature =
  functor (A : AddressSignature) ->
  functor (T : TimeSignature) ->
  sig
    type t
    (** The empty environment *)
    val empty : t
    (** Add a binding to the environment *)
    val extend : t -> string -> A.t -> t
    (** Find a binding in the environment *)
    val lookup : t -> string -> A.t
    (** Define the ordering between two environments *)
    val compare : t -> t -> int
    (** String representation of an environment *)
    val to_string : t -> string
    (** Update the environment tag when a function is called *)
    val call : T.arg -> t -> t
    (** Get the time stored inside the environment *)
    val time : t -> T.t
  end

module MapEnv : EnvSignature =
  functor (A : AddressSignature) -> 
  functor (T : TimeSignature) ->
  struct
    module StringMap = BatMap.Make(BatString)
    type t = {
      env : A.t StringMap.t;
      time : T.t;
    }
    let empty = {env = StringMap.empty; time = T.initial}
    let extend t var addr =
      {t with env = StringMap.add var addr t.env}
    let lookup t var = StringMap.find var t.env
    let compare t t' =
      order_concat [lazy (StringMap.compare A.compare t.env t'.env);
                    lazy (T.compare t.time t'.time)]
    let to_string t = String.concat ", "
        (BatList.map (fun (v, a) -> v ^ ": " ^ (A.to_string a))
           (StringMap.bindings t.env))
    let call arg t =
      {t with time = T.tick arg t.time}
    let time t = t.time
  end

module type LatticeSignature =
sig
  (** The concrete type represented by this lattice *)
  type elt
  (** The type of lattice values *)
  type t
  (** Raised when doing stuff that can't be done on a too abstracted value *)
  exception TooAbstracted of t
  (** Bottom element *)
  val bot : t
  (** Top element *)
  val top : t
  (** Join two lattice elements *)
  val join : t -> t -> t
  (** Abstract multiple values at once *)
  val abst : elt list -> t
  (** String representation of a lattice *)
  val compare : t -> t -> int
  (** Concretize a lattice values into a list of possible values if possible
      (can raise a TooAbstracted exception) *)
  val concretize : t -> elt list
  (** String representation of a lattice value *)
  val to_string : t -> string
end

module type LatticeArg = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
end

module SetLattice : functor (V : LatticeArg)
  -> LatticeSignature with type elt = V.t =
  functor (V : LatticeArg) ->
  struct
    module VSet = BatSet.Make(V)
    type elt = V.t
    type t =
      | Top
      | Set of VSet.t
    exception TooAbstracted of t
    let bot = Set VSet.empty
    let top = Top
    let join x y = match x, y with
      | Top, _ | _, Top -> Top
      | Set a, Set b -> Set (VSet.union a b)
    let abst l = Set (List.fold_left (fun s el -> VSet.add el s) VSet.empty l)
    let concretize = function
      | Top -> raise (TooAbstracted Top)
      | Set s -> VSet.elements s
    let compare x y = match x, y with
      | Top, Top -> 0
      | Top, _ -> 1
      | _, Top -> -1
      | Set a, Set b -> VSet.compare a b
    let to_string = function
      | Top -> "Top"
      | Set s -> String.concat "|"
                   (VSet.fold (fun v acc -> (V.to_string v) :: acc) s [])
  end

module type StoreSignature =
  functor (L : LatticeSignature) ->
  functor (A : AddressSignature) ->
  sig
    (** The store itself *)
    type t
    (** The empty store *)
    val empty : t
    (** Add a value to the store, joining it with the existing value, if
        present *)
    val join : t -> A.t -> L.t -> t
    (** Same as join, but can perform a strong update if possible *)
    val set : t -> A.t -> L.t -> t
    (** Find a value in the store. Raise Not_found if no value reside at the
        given address *)
    val lookup : t -> A.t -> L.t
    (** Keep only addresses in the given list *)
    val restrict : t -> A.t list -> t
    (** Define ordering between stores *)
    val compare : t -> t -> int
    (** Give the size of the store *)
    val size : t -> int
  end

module MapStore : StoreSignature =
  functor (L : LatticeSignature) ->
  functor (A : AddressSignature) ->
  struct
    module AddrMap = BatMap.Make(A)
    type count = One | Infinity
    type t = (L.t * count) AddrMap.t
    let empty = AddrMap.empty

    let join store a v =
      if AddrMap.mem a store then
        let (v', count) = AddrMap.find a store in
        AddrMap.add a ((L.join v v'), Infinity) store
      else
        AddrMap.add a (v, One) store

    let set store a v =
      if AddrMap.mem a store then
        let (v', count) = AddrMap.find a store in
        match count with
        | One -> AddrMap.add a (v, One) store
        | Infinity -> join store a v
      else
        AddrMap.add a (v, One) store

    let lookup store a =
      match AddrMap.find a store with
      | v, _ -> v
      | exception Not_found -> failwith ("Cannot find value at address " ^ (A.to_string a))

    let restrict store addrs =
      AddrMap.filter (fun a _ ->
          if (List.mem a addrs) then
            true
          else begin
            print_endline ("reclaim(" ^ (A.to_string a) ^ ")");
            false end) store
    let compare =
      AddrMap.compare (fun (v, c) (v', c') ->
          order_concat [lazy (L.compare v v');
                        lazy (Pervasives.compare c c')])

    let size = AddrMap.cardinal
  end

module type LangSignature =
sig
  (** An expression *)
  type exp
  (** Parse an expression *)
  val parse : string -> exp
  (** Convert an expression to a printable string *)
  val string_of_exp : exp -> string

  (** A configuration, ie. a machine state *)
  type conf
  (** Convert a configuration to a printable string *)
  val string_of_conf : conf -> string
  (** Ordering between configurations *)
  module ConfOrdering : BatInterfaces.OrderedType with type t = conf

  (** A stack frame *)
  type frame
  (** Convert a stack frame to a printable string *)
  val string_of_frame : frame -> string
  (** Ordering between stack frames *)
  module FrameOrdering : BatInterfaces.OrderedType with type t = frame

  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged of string
  module StackChangeOrdering : BatInterfaces.OrderedType with type t = stack_change
  val string_of_stack_change : stack_change -> string

  (** Inject an expression in an initial configuration *)
  val inject : exp -> conf
  (** Step between the machine configurations. The second argument is potential
      frame that reside on the top of the stack, along with the preceding
      configuration. Returns the successor configurations with the corresponding
      changes to the stack *)
  val step : conf -> (conf * frame) option -> (stack_change * conf) list

  (** Associate a color with a configuration. Used for displaying the graph *)
  val conf_color : conf -> int
end

module ANFStructure =
struct
  type var = string
  type operator =
    | Plus | Minus | Times | Divide
    | Lesser | LesserOrEqual | Greater | GreaterOrEqual | Equal
    | Id
  type lam = var * exp
  and aexp =
    | Var of var
    | Lambda of lam
    | Int of int
    | True | False
    | Op of operator * aexp list
  and cexp =
    | Call of aexp * aexp * int
    | Set of var * aexp
  and exp =
    | Let of var * exp *  exp
    | LetRec of var * exp * exp
    | If of aexp * exp * exp
    | CExp of cexp
    | AExp of aexp

  let parse s =
    let i = ref 0 in
    let new_id () = i := !i + 1; !i in
    let is_op = function
      | "+" | "-" | "*" | "/" | "<" | "<=" | ">" | ">=" | "=" -> true
      | _ -> false in
    let to_op = function
      | "+" -> Plus | "-" -> Minus | "*" -> Times | "/" -> Divide
      | "<" -> Lesser | "<=" -> LesserOrEqual | ">" -> Greater | ">=" -> GreaterOrEqual
      | "=" -> Equal
      | "id" -> Id | op -> failwith ("unknown op: " ^ op) in
    let open SExpr in
    let rec convert_aexp = function
      | Expr [Atom "lambda"; Expr [Atom arg]; body] ->
        Lambda (arg, convert_exp body)
      | Expr [Atom "lambda"; Expr args_expr; body] as e ->
        (* parse lambda into currified expressions *)
        let args = BatList.rev_map (function
            | Atom v -> v
            | _ -> failwith ("Cannot parse aexp " ^ (string_of_sexpr [e])))
            args_expr in
        let exp = BatList.fold_left (fun acc arg -> AExp (Lambda (arg, acc)))
            (convert_exp body) args in
        begin match exp with
          | AExp aexp -> aexp
          | body -> Lambda ("dummy", body) (* no argument *)
        end
      | Atom "#t" -> True
      | Atom "#f" -> False
      | Atom x -> begin try Int (int_of_string x) with
            Failure "int_of_string" -> Var x
        end
      | Expr (Atom op :: args) when is_op op ->
        Op (to_op op, BatList.map convert_aexp args)
      | sexp -> failwith ("cannot parse aexp: " ^ (string_of_sexpr [sexp]))
    and convert_cexp = function
      | Expr [Atom "set!"; Atom v; aexp] ->
        if is_op v then failwith ("cannot set! an operator: " ^ v) else
          Set (v, convert_aexp aexp)
      | Expr [f] ->
        Call (convert_aexp f, Int 0 (* dummy var *), new_id ())
      | Expr [f; arg] ->
        Call (convert_aexp f, convert_aexp arg, new_id ())
      | sexp -> failwith ("cannot parse cexp: " ^ (string_of_sexpr [sexp]))
    and convert_exp = function
      | Expr [Atom "let"; Expr [Expr [Atom v; exp]]; body] ->
        Let (v, convert_exp exp, convert_exp body)
      | Expr [Atom "letrec"; Expr [Expr [Atom v; exp]]; body] ->
        LetRec (v, convert_exp exp, convert_exp body)
      | Expr [Atom "if"; cond; cons; alt] ->
        If (convert_aexp cond, convert_exp cons, convert_exp alt)
      | exp ->
        try CExp (convert_cexp exp) with
        | Failure f1 -> try AExp (convert_aexp exp) with
          | Failure f2 -> try begin match exp with
            | Expr (f :: arg_expr :: args_expr) ->
              (* parse call into currified call *)
              let arg = convert_aexp arg_expr in
              let args = BatList.map convert_aexp args_expr in
              let rec build_exp n = function
                | [] -> failwith "should not happen"
                | arg :: [] ->
                  CExp (Call (Var ("_call" ^ (string_of_int n)), arg, new_id ()))
                | arg :: args ->
                  Let ("_call" ^ (string_of_int (n+1)),
                       CExp (Call (Var ("_call" ^ (string_of_int n)), arg, new_id ())),
                       build_exp (n+1) args) in
              Let ("_call0", CExp (Call (convert_aexp f, arg, new_id ())),
                   build_exp 0 args)
            | _ -> failwith ("cannot parse exp: " ^ f1 ^ ", " ^ f2)
          end with Failure f3 ->
            failwith ("cannot parse exp: " ^ f1 ^ ", " ^ f2 ^ ", " ^ f3) in
    convert_exp (BatList.hd (SExpr.parse_string s))

  let rec free = function
    | Let (v, exp, body) ->
      StringSet.union (free exp) (StringSet.remove v (free body))
    | LetRec (v, exp, body) ->
      StringSet.remove v (StringSet.union (free exp) (free body))
    | If (cond, cons, alt) ->
      free_aexp cond |>
      StringSet.union (free cons) |>
      StringSet.union (free alt)
    | AExp ae -> free_aexp ae
    | CExp ce -> free_cexp ce
  and free_cexp = function
    | Call (f, ae, _) ->
      StringSet.union (free_aexp f) (free_aexp ae)
    | Set (v, ae) ->
      StringSet.add v (free_aexp ae)
  and free_aexp = function
    | Var v -> StringSet.singleton v
    | Lambda (v, exp) -> StringSet.remove v (free exp)
    | Op (op, args) ->
      BatList.fold_left (fun acc arg -> StringSet.union acc (free_aexp arg))
        StringSet.empty args
    | Int _ | True | False -> StringSet.empty

  let string_of_op = function
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Divide -> "/"
    | Lesser -> "<"
    | LesserOrEqual -> "<="
    | Greater -> ">"
    | GreaterOrEqual -> ">="
    | Equal -> "="
    | Id -> "id"
  let rec string_of_exp = function
    | Let (v, exp, body) ->
      Printf.sprintf "(let ((%s %s)) %s)"
        v (string_of_exp exp) (string_of_exp body)
    | LetRec (v, exp, body) ->
      Printf.sprintf "(letrec ((%s %s)) %s)"
        v (string_of_exp exp) (string_of_exp body)
    | If (cond, cons, alt) ->
      Printf.sprintf "(if %s %s %s)"
        (string_of_aexp cond) (string_of_exp cons) (string_of_exp alt)
    | CExp ce -> string_of_cexp ce
    | AExp ae -> string_of_aexp ae
  and string_of_cexp = function
    | Call (f, ae, _) ->
      Printf.sprintf "(%s %s)" (string_of_aexp f) (string_of_aexp ae)
    | Set (v, ae) ->
      Printf.sprintf "(set! %s %s)" v (string_of_aexp ae)
  and string_of_aexp = function
    | Var v -> v
    | Lambda (v, e) ->
      Printf.sprintf "(lambda (%s) %s)" v (string_of_exp e)
    | Int n ->
      string_of_int n
    | True -> "#t"
    | False -> "#f"
    | Op (op, args) ->
      Printf.sprintf "(%s %s)"
        (string_of_op op) (String.concat " " (BatList.map string_of_aexp args))

  module Time = KCFATime
  module Address = MakeAddress(Time)
  type addr = Address.t
  module AddressSet = BatSet.Make(Address)

  module Env = MapEnv(Address)(Time)
  type env = Env.t

  type clo = lam * env

  let compare_clo (lam1, env1) (lam2, env2) =
    order_concat [lazy (Pervasives.compare lam1 lam2);
                  lazy (Env.compare env1 env2)]

  module V = struct
    type t =
      | Clos of clo
      | Num
      | True
      | False
      | Boolean
      | Undefined
    let compare x y = match x, y with
      | Clos c, Clos c' -> compare_clo c c'
      | Clos _, _ -> 1
      | _, Clos _ -> -1
      | x, y -> Pervasives.compare x y
    let to_string = function
      | Clos _ -> "<clos>"
      | Num -> "Num"
      | True -> "#t"
      | False -> "#f"
      | Boolean -> "Bool"
      | Undefined -> "<undefined>"
  end
  module Lattice = SetLattice(V)
  module Store = MapStore(Lattice)(Address)

  type id = lam * env
  module ProcIdOrdering = struct
    type t = id
    let compare (lam, env) (lam', env') =
      order_concat [lazy (Pervasives.compare lam lam');
                    lazy (Env.compare env env')]
  end
  module ProcIdMap = BatMap.Make(ProcIdOrdering)
  module ProcIdSet = BatSet.Make(ProcIdOrdering)

  module ValueTable = BatMap.Make(Lattice)
  type table =
    | Impure
    | Poly
    | Table of Lattice.t ValueTable.t
  type memo = table ProcIdMap.t
  let memo_empty : memo = ProcIdMap.empty
  module AddressMap = BatMap.Make(Address)
  type reads = ProcIdSet.t AddressMap.t
  let reads_empty : reads = AddressMap.empty

  type store = Store.t
  type control =
    | Exp of exp
    | Val of Lattice.t
  type state = {
    control: control;
    env: env;
    store: store;
    memo: memo;
    reads: reads;
    time: Time.t
  }
  type frame =
    | FLet of var * exp * env
    | FLetRec of Address.t * var * exp * env
    | FMark of id * Lattice.t * env

  let create_id lam env store : id = (lam, env)

  let string_of_frame = function
    | FLet (v, e, env) -> Printf.sprintf "Let(%s)" v
    | FLetRec (a, v, e, env) -> Printf.sprintf "LetRec(%s)" v
    | FMark _ -> "Mark"

  let compare_frame x y = match x, y with
    | FLet (v, exp, env), FLet (v', exp', env') ->
      order_concat [lazy (Pervasives.compare v v');
                    lazy (Pervasives.compare exp exp');
                    lazy (Env.compare env env')]
    | FLet _, _ -> 1 | _, FLet _ -> -1
    | FLetRec (a, v, exp, env), FLetRec (a', v', exp', env') ->
      order_concat [lazy (Address.compare a a');
                    lazy (Pervasives.compare v v');
                    lazy (Pervasives.compare exp exp');
                    lazy (Env.compare env env')]
    | FLetRec _, _ -> 1 | _, FLetRec _ -> -1
    | FMark ((lam, env), d, env2), FMark ((lam', env'), d', env2') ->
      order_concat [lazy (Pervasives.compare lam lam');
                    lazy (Env.compare env env');
                    lazy (Lattice.compare d d');
                    lazy (Env.compare env2 env2')]

  let compare_control x y = match x, y with
    | Exp e, Exp e' -> Pervasives.compare e e'
    | Exp _, _ -> 1
    | _, Exp _ -> -1
    | Val v, Val v' -> Lattice.compare v v'
  let string_of_control = function
    | Exp e -> string_of_exp e
    | Val v -> Lattice.to_string v

  let compare_state state state' =
    order_concat
      [lazy (compare_control state.control state'.control);
       lazy (Env.compare state.env state'.env);
       lazy (Store.compare state.store state'.store)]
  let string_of_state state =
    (string_of_control state.control)

  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged of string

  let compare_stack_change g1 g2 = match (g1, g2) with
    | StackPop f1, StackPop f2 -> compare_frame f1 f2
    | StackPush f1, StackPush f2 -> compare_frame f1 f2
    | StackUnchanged s, StackUnchanged s' -> Pervasives.compare s s'
    | StackPop _, _ -> 1
    | _, StackPop _ -> -1
    | StackPush _, StackUnchanged _ -> 1
    | StackUnchanged _, _ -> -1

  let string_of_stack_change = function
    | StackPush f -> "+" ^ (string_of_frame f)
    | StackPop f -> "-" ^ (string_of_frame f)
    | StackUnchanged s -> s

  module FrameOrdering = struct
    type t = frame
    let compare = compare_frame
  end

  module StackChangeOrdering = struct
    type t = stack_change
    let compare = compare_stack_change
  end

  let apply_op op args = match op with
    | Plus | Minus | Times | Divide -> Lattice.abst [V.Num]
    | Lesser | LesserOrEqual | Greater | GreaterOrEqual | Equal -> Lattice.abst [V.Boolean]
    | Id -> match args with
      | x :: [] -> x
      | _ -> failwith "Invalid numbre of arguments to 'id'"

  let rec atomic_eval atom env store =
    match atom with
    | Var var ->
      let a = Env.lookup env var in
      (Store.lookup store a, AddressSet.singleton a, ProcIdSet.empty)
    | Lambda lam ->
      (Lattice.abst [V.Clos (lam, env)], AddressSet.empty,
       ProcIdSet.singleton (create_id lam env store))
    | Int n ->
      (Lattice.abst [V.Num], AddressSet.empty, ProcIdSet.empty)
    | True ->
      (Lattice.abst [V.True], AddressSet.empty, ProcIdSet.empty)
    | False ->
      (Lattice.abst [V.False], AddressSet.empty, ProcIdSet.empty)
    | Op (op, args) ->
      let (revds, addrs, ids) = BatList.fold_left (fun (ds, addrs, ids) arg ->
          let (d, addrs', ids') = atomic_eval arg env store in
          (d :: ds, AddressSet.union addrs addrs', ProcIdSet.union ids ids'))
          ([], AddressSet.empty, ProcIdSet.empty) args in
      let ds = BatList.rev revds in
      let d = apply_op op ds in
      (d, addrs, ids)

  let alloc v state =
    Address.alloc v 0 (Env.time state.env)
end

module type StackSummary =
sig
  type t
  (** The empty stack summary *)
  val empty : t
  (** Define ordering between stack summaries *)
  val compare : t -> t -> int
  (** Convert a stack summary to a printable string *)
  val to_string : t -> string
  (** Add information related to a new frame in the stack summary *)
  val push : t -> ANFStructure.frame -> t
  (** Set of addresses reachable from the stack summary *)
  val reachable : t -> ANFStructure.AddressSet.t
  (** Set of marked procedures stored in the stack summary *)
  val marked : t -> ANFStructure.ProcIdSet.t
end

module ReachableAddressesAndMarksSummary : StackSummary =
struct
  open ANFStructure
  type t = AddressSet.t * ProcIdSet.t
  let empty = (AddressSet.empty, ProcIdSet.empty)
  let compare (addrs, procids) (addrs', procids') =
    order_concat [lazy (AddressSet.compare addrs addrs');
                  lazy (ProcIdSet.compare procids procids')]
  let to_string (addrs, procids) =
    "[" ^ (String.concat ", "
             (BatList.map Address.to_string
                (AddressSet.elements addrs))) ^ "]"

  let touch =
    let helper env vars =
      StringSet.fold (fun v acc -> AddressSet.add (Env.lookup env v) acc)
        vars AddressSet.empty in
    function
    | FLet (v, e, env) ->
      helper env (StringSet.remove v (free e))
    | FLetRec (a, v, e, env) ->
      AddressSet.add a (helper env (StringSet.remove v (free e)))
    | FMark (_, _, _) ->
      AddressSet.empty

  let push (addrs, procids) f =
    (AddressSet.union addrs (touch f),
     match f with
     | FMark (id, _, _) -> ProcIdSet.add id procids
     | _ -> procids)

  let reachable (addrs, _) = addrs

  let marked (_, procids) = procids
end

module ANFGarbageCollected : LangSignature with type exp = ANFStructure.exp =
struct
  include ANFStructure
  module Summary = ReachableAddressesAndMarksSummary
  type conf = state * Summary.t

  let compare_conf (s1, ss1) (s2, ss2) =
    order_concat [lazy (compare_state s1 s2);
                  lazy (Summary.compare ss1 ss2)]

  let string_of_conf (state, ss) =
    (string_of_state state)

  let inject e =
    ({control = Exp e; env = Env.empty; store = Store.empty;
      memo = memo_empty; reads = reads_empty; time = Time.initial},
     Summary.empty)

  let apply_kont f d state = match f with
    | FLet (v, e, env') ->
      let a = alloc v state in
      let env'' = Env.extend env' v a in
      let store' = Store.join state.store a d in
      [{state with store = store'; env = env''; control = Exp e}]
    | FLetRec (a, v, e, env') ->
      let store' = Store.set state.store a d in
      [{state with store = store'; control = Exp e; env = env'}]
    | FMark (id, d_arg, env') ->
      if !param_memo then
        [{state with memo = begin match ProcIdMap.find id state.memo with
             | Table table ->
               ProcIdMap.add id (Table (ValueTable.add d_arg d table)) state.memo
             | exception Not_found ->
               ProcIdMap.add id (Table (ValueTable.add d_arg d ValueTable.empty)) state.memo
             | Impure | Poly -> state.memo end;
                env = env'}]
      else
        [{state with env = env'}]

  let update_memo memo ids =
    if !param_memo then
      ProcIdSet.fold (fun id acc ->
          if ProcIdMap.mem id acc then
            ProcIdMap.add id Poly acc
          else
            acc) ids memo
    else
      memo

  let update_reads reads addrs marked =
    if !param_memo then
      AddressSet.fold (fun addr acc ->
          AddressMap.add addr (ProcIdSet.union marked
                                 (if AddressMap.mem addr acc then
                                    AddressMap.find addr acc
                                  else
                                    ProcIdSet.empty)) acc)
        addrs reads
    else
      reads

  let step_no_gc (state, ss) frame = match state.control with
    | Exp (CExp (Call (f, ae, tag))) ->
      let (rator, addrs, ids) = atomic_eval f state.env state.store in
      let (rand, addrs', ids') = atomic_eval ae state.env state.store in
      List.fold_left (fun acc -> function
          | V.Clos ((v, e), env') ->
            let a = alloc v state in
            (* TODO: don't call create_id anywhere else than in the atomic evaluator *)
            let id = create_id (v, e) env' state.store in
            let memo' =  update_memo state.memo (ProcIdSet.union ids ids') in
            let reads' = update_reads state.reads
                (AddressSet.union addrs addrs') (Summary.marked ss) in
            let cached = match ProcIdMap.find id state.memo with
              | Table table ->
                begin try Some (ValueTable.find rand table)
                  with Not_found -> None
                end
              | Impure | Poly -> None
              | exception Not_found -> None in
            begin match cached with
              | None ->
                let f = FMark (id, rand, state.env) in
                (StackPush f,
                 ({control = Exp e;
                   env = Env.call tag (Env.extend env' v a);
                   store = Store.join state.store a rand;
                   memo = memo';
                   reads = reads';
                   time = Time.tick tag state.time}, ss)) :: acc
              | Some d ->
                Printf.printf "Hit\n%!";
                (StackUnchanged "memo", ({state with control = Val d;
                                                     memo = memo';
                                                     reads = reads';
                                                     time = Time.tick tag state.time}, ss)) :: acc
            end
          | V.Undefined | V.Num | V.True | V.False | V.Boolean -> acc)
        [] (Lattice.concretize rator)
    | Exp (CExp (Set (v, ae))) ->
      let (clo, addrs, ids) = atomic_eval ae state.env state.store in
      List.fold_left (fun acc -> function
          | V.Clos ((var, exp), env') ->
            let id = create_id (var, exp) env' state.store in
            let addr = Env.lookup state.env v in
            let store' = Store.join state.store addr clo in (* TODO: set *)
            let v = Lattice.abst [V.Undefined] in
            let reads_ids = (AddressMap.find addr state.reads) in
            let memo' = update_memo state.memo ids |>
                        ProcIdMap.add id Impure |>
                        ProcIdMap.filter (fun id _ -> not (ProcIdSet.mem id reads_ids)) in
            (StackUnchanged "e", ({state with control = Val v; store = store';
                                          memo = memo';
                                          reads = update_reads state.reads addrs
                                              (Summary.marked ss)}, ss)) :: acc
          | _ -> acc) [] (Lattice.concretize clo)
    | Exp (AExp ae) ->
      let (clo, addrs, ids) = atomic_eval ae state.env state.store in
      [(StackUnchanged "e", ({state with control = Val clo;
                                     memo = update_memo state.memo ids;
                                     reads = update_reads state.reads addrs
                                         (Summary.marked ss)}, ss))]
    | Exp (Let (v, exp, body)) ->
      let f = FLet (v, body, state.env) in
      [(StackPush f, ({state with control = Exp exp}, Summary.push ss f))]
    | Exp (LetRec (v, exp, body)) ->
      let a = alloc v state in
      let env' = Env.extend state.env v a in
      let store' = Store.join state.store a (Lattice.abst [V.Undefined]) in
      let f = FLetRec (a, v, body, env') in
      [(StackPush f, ({state with control = Exp exp;
                                  env = env';
                                  store = store'}, Summary.push ss f))]
    | Exp (If (cond, cons, alt)) ->
      let (d, addrs, ids) = atomic_eval cond state.env state.store in
      let states = BatList.flatten (BatList.map (function
          | V.True -> [{state with control = Exp cons}]
          | V.False -> [{state with control = Exp alt}]
          | V.Boolean -> [{state with control = Exp cons};
                          {state with control = Exp alt}]
          | V.Num | V.Clos _ | V.Undefined -> []) (Lattice.concretize d)) in
      BatList.map (fun s -> (StackUnchanged "e", (s, ss))) states
    | Val v -> begin match frame with
        | Some ((_, ss'), f) ->
          BatList.map (fun state -> (StackPop f, (state, ss'))) (apply_kont f v state)
        | None ->
          []
      end

  module ConfOrdering = struct
    type t = conf
    let compare = compare_conf
  end

  let addresses_of_vars vars env =
    StringSet.fold (fun v acc ->
        AddressSet.add (Env.lookup env v) acc)
      vars AddressSet.empty

  let root ((state, ss) : conf) = match state.control with
    | Exp e -> AddressSet.union (Summary.reachable ss)
                 (addresses_of_vars (free e) state.env)
    | Val _ -> Summary.reachable ss

  let touch (lam, env) =
    addresses_of_vars (free (AExp (Lambda lam))) env

  (* Applies one step of the touching relation *)
  let touching_rel1 addr store =
    List.fold_left (fun acc -> function
        | V.Clos a -> AddressSet.union acc (touch a)
        | V.Undefined | V.Num | V.True | V.False | V.Boolean -> acc)
      AddressSet.empty
      (Lattice.concretize (Store.lookup store addr))

  (* Transitive closure of the touching relation *)
  let touching_rel addr store =
    let rec aux todo acc =
      if AddressSet.is_empty todo then
        acc
      else
        let a = AddressSet.choose todo in
        if AddressSet.mem a acc then
          aux (AddressSet.remove a todo) acc
        else
          let addrs = touching_rel1 addr store in
          aux (AddressSet.remove a (AddressSet.union addrs todo))
            (AddressSet.add a (AddressSet.union addrs acc))
    in
    aux (AddressSet.singleton addr) AddressSet.empty

  let reachable (conf : conf) =
    let (state, _) = conf in
    AddressSet.fold (fun a acc ->
        AddressSet.union acc (touching_rel a state.store))
      (root conf) AddressSet.empty

  let gc ((state, ss) as conf) =
    ({state with store = Store.restrict state.store (AddressSet.to_list
                                                       (reachable conf))},
     ss)

  let step conf =
    if !param_gc then
      step_no_gc (gc conf)
    else
      step_no_gc conf

  let conf_color (state, _) = match state.control with
    | Exp _ -> 0xFFDDDD
    | Val _ -> 0xDDFFDD
end

module type BuildDSGSignature =
  functor (L : LangSignature) ->
  sig
    module G : Graph.Sig.P
    module ConfSet : BatSet.S with type elt = L.conf
    module EdgeSet : BatSet.S with type elt = (L.conf * L.stack_change * L.conf)
    module EpsSet : BatSet.S with type elt = L.conf * L.conf
    type dsg = { g : G.t; q0 : L.conf; ecg : G.t }
    val build_dyck : L.exp -> dsg
    val add_short : dsg -> L.conf -> L.conf -> ConfSet.t * EdgeSet.t * EpsSet.t
    val add_edge : dsg -> L.conf -> L.stack_change -> L.conf -> ConfSet.t * EdgeSet.t * EpsSet.t
    val explore : dsg -> L.conf -> ConfSet.t * EdgeSet.t * EpsSet.t
    val output_dsg : dsg -> string -> unit
    val output_ecg : dsg -> string -> unit
    val print_stats : dsg -> unit
  end

module BuildDSG : BuildDSGSignature =
  functor (L : LangSignature) ->
  struct
    module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(struct
        include L.ConfOrdering
        let hash = Hashtbl.hash
        let equal x y = compare x y == 0
      end)(struct
        include L.StackChangeOrdering
        let default = L.StackUnchanged "e"
      end)

    module DotArg = struct
      include G

      module ConfMap = Map.Make(L.ConfOrdering)
      let id = ref 0
      let new_id () =
        id := !id + 1;
        !id

      let nodes = ref ConfMap.empty
      let node_id node =
        if ConfMap.mem node !nodes then
          ConfMap.find node !nodes
        else
          let id = new_id () in
          nodes := ConfMap.add node id !nodes;
          id

      let edge_attributes ((_, f, _) : E.t) =
        [`Label (BatString.slice ~last:20 (L.string_of_stack_change f))]
      let default_edge_attributes _ = []
      let get_subgraph _ = None
      let vertex_name (state : V.t) =
        (string_of_int (node_id state))
      let vertex_attributes (state : V.t) =
        [`Label (BatString.slice ~last:20 (L.string_of_conf state));
         `Style `Filled;
         `Fillcolor (L.conf_color state)]
      let default_vertex_attributes _ = []
      let graph_attributes _ = []
    end

    module Dot = Graph.Graphviz.Dot(DotArg)
    let output_graph graph file =
      let out = open_out_bin file in
      Dot.output_graph out graph;
      close_out out

    module ConfSet = BatSet.Make(L.ConfOrdering)
    module EdgeOrdering = struct
      type t = L.conf * L.stack_change * L.conf
      let compare (c1, g, c2) (c1', g', c2') =
        order_concat [lazy (L.ConfOrdering.compare c1 c1');
                      lazy (L.StackChangeOrdering.compare g g');
                      lazy (L.ConfOrdering.compare c2 c2')]
    end
    module EdgeSet = BatSet.Make(EdgeOrdering)
    module EpsOrdering = struct
      type t = L.conf * L.conf
      let compare (c1, c2) (c1', c2') =
        order_concat [lazy (L.ConfOrdering.compare c1 c1');
                      lazy (L.ConfOrdering.compare c2 c2')]
    end
    module EpsSet = BatSet.Make(EpsOrdering)

    type dsg = { g : G.t; q0 : L.conf; ecg : G.t }
    let output_dsg dsg = output_graph dsg.g
    let output_ecg dsg = output_graph dsg.ecg
    let print_stats dsg = Printf.printf "Size: %d/%d\n%!" (G.nb_vertex dsg.g) (G.nb_edges dsg.g)

    let add_short dsg c c' =
      let (de, dh) = G.fold_edges_e
          (fun e (de, dh) -> match e with
             | (c1, L.StackPush k, c1') when L.ConfOrdering.compare c1' c == 0 ->
               let de', dh' =
                 (List.fold_left (fun (de, dh) edge -> match edge with
                      | (L.StackPop k', c2) when L.FrameOrdering.compare k k' == 0 ->
                        (EdgeSet.add (c', L.StackPop k, c2) de,
                         EpsSet.add (c1, c2) dh)
                      | _ -> (de, dh))
                     (EdgeSet.empty, EpsSet.empty) (L.step c' (Some (c, k)))) in
               (EdgeSet.union de de', EpsSet.union dh dh')
             | _ -> (de, dh))
          dsg.g (EdgeSet.empty, EpsSet.empty) in
      let ds = EdgeSet.fold (fun (c1, g, c2) acc -> match g with
          | L.StackPop k -> ConfSet.add c2 acc
          | _ -> acc)
          de ConfSet.empty in
      let dh' =
        let (end_w_c, start_w_c') = G.fold_edges
            (fun c1 c2 (ec, sc') ->
               ((if L.ConfOrdering.compare c2 c == 0 then (c1, c2) :: ec else ec),
                (if L.ConfOrdering.compare c1 c' == 0 then (c1, c2) :: sc' else sc')))
            dsg.ecg ([], []) in
        List.fold_left EpsSet.union dh
          [List.fold_left (fun acc (c1, c2) -> EpsSet.add (c1, c') acc)
             EpsSet.empty end_w_c;
           List.fold_left (fun acc (c1, c2) -> EpsSet.add (c, c2) acc)
             EpsSet.empty start_w_c';
           List.fold_left (fun acc ((c1, _), (_, c2)) -> EpsSet.add (c1, c2) acc)
             EpsSet.empty (BatList.cartesian_product end_w_c start_w_c')] in
      (ConfSet.filter (fun c -> not (G.mem_vertex dsg.g c)) ds,
       EdgeSet.filter (fun c -> not (G.mem_edge_e dsg.g c)) de,
       EpsSet.filter (fun (c1, c2) -> not (G.mem_edge dsg.ecg c1 c2)) dh')

    let add_edge dsg c g c' = match g with
      | L.StackUnchanged s ->
        let (ds, de, dh) = add_short { dsg with ecg = G.add_edge dsg.ecg c c' } c c' in
        (ds, de, EpsSet.add (c, c') dh)
      | L.StackPush k ->
        let de = G.fold_edges
            (fun c_ c1 acc ->
               if L.ConfOrdering.compare c_ c' == 0 then
                 let c2s = List.filter (fun (g', c2) -> match g' with
                     | L.StackPop k' -> L.FrameOrdering.compare k k' == 0
                     | _ -> false) (L.step c1 (Some (c1, k))) in
                 List.fold_left (fun acc (g, c2) -> EdgeSet.add (c1, g, c2) acc)
                   acc c2s
               else
                 acc)
            dsg.ecg EdgeSet.empty in
        let ds = EdgeSet.fold
            (fun (_, _, c2) acc -> ConfSet.add c2 acc)
            de ConfSet.empty in
        let dh = G.fold_edges
            (fun (c_ : L.conf) (c1 : L.conf) (acc : EpsSet.t) ->
               if L.ConfOrdering.compare c_ c' == 0 then
                 let c2s = G.fold_edges_e (fun (c1_, g', c2) acc -> match g' with
                     | L.StackPop k' when L.FrameOrdering.compare k k' == 0 &&
                                          L.ConfOrdering.compare c1 c1_ == 0 ->
                       c2 :: acc
                     | _ -> acc) dsg.g [] in
                 List.fold_left (fun acc c2 -> EpsSet.add (c1, c2) acc)
                   acc c2s
               else
                 acc)
            dsg.ecg EpsSet.empty in
        (ConfSet.filter (fun c -> not (G.mem_vertex dsg.g c)) ds,
         EdgeSet.filter (fun c -> not (G.mem_edge_e dsg.g c)) de,
         EpsSet.filter (fun (c1, c2) -> not (G.mem_edge dsg.ecg c1 c2)) dh)
      | L.StackPop k ->
        let dh = G.fold_edges
            (fun c2 c_ acc ->
               if L.ConfOrdering.compare c_ c == 0 then
                 let c1s = G.fold_edges_e (fun (c1, g', c2_) acc -> match g' with
                     | L.StackPush k' when L.FrameOrdering.compare k k' == 0 &&
                                           L.ConfOrdering.compare c2 c2_ == 0 ->
                       c1 :: acc
                     | _ -> acc) dsg.g [] in
                 List.fold_left (fun acc c1 -> EpsSet.add (c1, c') acc)
                   acc c1s
               else
                 acc)
            dsg.ecg EpsSet.empty in
        (ConfSet.empty,
         EdgeSet.empty,
         EpsSet.filter (fun (c1, c2) -> not (G.mem_edge dsg.ecg c1 c2)) dh)

    let explore dsg c =
      let stepped = L.step c None in
      let ds = (List.fold_left
                  (fun set (_, conf) -> ConfSet.add conf set)
                  ConfSet.empty stepped)
      and de = (List.fold_left
                  (fun set (stack_op, conf) -> EdgeSet.add (c, stack_op, conf) set)
                  EdgeSet.empty stepped) in
      (ConfSet.filter (fun c -> not (G.mem_vertex dsg.g c)) ds,
       EdgeSet.filter (fun c -> not (G.mem_edge_e dsg.g c)) de,
       EpsSet.empty)

    let build_dyck exp =
      let c0 = L.inject exp in
      let i = ref 0 in
      let rec loop dsg ds de dh =
        i := !i + 1;
        if not (EpsSet.is_empty dh) then
          let c, c' = EpsSet.choose dh in
          let (ds', de', dh') = add_short dsg c c' in
          loop { dsg with ecg = G.add_edge dsg.ecg c c' }
            (ConfSet.union ds ds')
            (EdgeSet.union de de')
            (EpsSet.remove (c, c') (EpsSet.union dh dh'))
        else if not (EdgeSet.is_empty de) then
          let c, g, c' = EdgeSet.choose de in
          let (ds', de', dh') = add_edge dsg c g c' in
          loop { dsg with g = G.add_edge_e dsg.g (c, g, c') }
            (ConfSet.union ds ds')
            (EdgeSet.remove (c, g, c') (EdgeSet.union de de'))
            (EpsSet.union dh dh')
        else if not (ConfSet.is_empty ds) then
          let c = ConfSet.choose ds in
          let (ds', de', dh') = explore dsg c in
          loop { dsg with g = G.add_vertex dsg.g c; ecg = G.add_vertex dsg.ecg c }
            (ConfSet.remove c (ConfSet.union ds ds'))
            (EdgeSet.union de de')
            (EpsSet.union dh dh')
        else
          dsg
      in loop { g = G.empty; q0 = c0; ecg = G.empty }
        (ConfSet.singleton c0) EdgeSet.empty EpsSet.empty
  end

module L = ANFGarbageCollected
module DSG = BuildDSG(L)

let usage = "usage: " ^ (Sys.argv.(0)) ^ " [params] file"
let file = ref None
let () =
  let () = Arg.parse speclist (fun x -> file := Some x) usage in
  match !file with
  | None -> print_endline usage
  | Some f ->
    let str = Std.input_file f in
    let exp = L.parse str in
    let dsg = DSG.build_dyck exp in
    DSG.output_dsg dsg "dsg.dot";
    DSG.output_ecg dsg "ecg.dot";
    DSG.print_stats dsg
