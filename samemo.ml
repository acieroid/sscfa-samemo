open Utils

module type Address_signature =
sig
  type t
  (** Define the ordering between two addresses *)
  val compare : t -> t -> int
  (** Convert an address to a string *)
  val to_string : t -> string
  (** Allocate a new address from an integer *)
  val alloc : int -> t
end

module IntegerAddress : Address_signature =
struct
  type t = int
  let compare = Pervasives.compare
  let to_string = string_of_int
  let alloc x =
    let a = x mod 5 in
    print_string ("allocated address " ^ (to_string a));
    print_newline ();
    a
end

module type Env_signature =
  functor (A : Address_signature) ->
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
    (** Give the environment size *)
    val size : t -> int
    (** String representation of an environment *)
    val to_string : t -> string
  end

module MapEnv : Env_signature =
  functor (A : Address_signature) ->
  struct
    module StringMap = BatMap.Make(BatString)
    type t = A.t StringMap.t
    let empty = StringMap.empty
    let extend env var addr = StringMap.add var addr env
    let lookup env var = StringMap.find var env
    let compare = StringMap.compare A.compare
    let size = StringMap.cardinal
    let to_string env = String.concat ", "
        (BatList.map (fun (v, a) -> v ^ ": " ^ (A.to_string a))
           (StringMap.bindings env))
  end

module type Lattice_signature =
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
  -> Lattice_signature with type elt = V.t =
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

module type Store_signature =
  functor (L : Lattice_signature) ->
  functor (A : Address_signature) ->
  sig
    (** The store itself *)
    type t
    (** The empty store *)
    val empty : t
    (** Add a value to the store, joining it with the existing value, if
        present *)
    val join : t -> A.t -> L.t -> t
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

module MapStore : Store_signature =
  functor (L : Lattice_signature) ->
  functor (A : Address_signature) ->
  struct
    module AddrMap = BatMap.Make(A)
    type t = L.t AddrMap.t
    let empty = AddrMap.empty
    let join store a v =
      if AddrMap.mem a store then
        AddrMap.add a (L.join (AddrMap.find a store) v) store
      else
        AddrMap.add a v store
    let lookup store a = AddrMap.find a store
    let restrict store addrs =
      AddrMap.filter (fun a _ ->
          if (List.mem a addrs) then
            true
          else begin
            print_endline ("reclaim(" ^ (A.to_string a) ^ ")");
            false end) store
    let compare = AddrMap.compare L.compare
    let size = AddrMap.cardinal
  end

module type Lang_signature =
sig
  (** An expression *)
  type exp
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
    | StackUnchanged
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
    | Lesser | LesserOrEqual | Greater | GreaterOrEqual
    | Id
  type lam = var * exp
  and aexp =
    | Var of var
    | Lambda of lam
    | Int of int
    | True | False
  and cexp =
    | Call of aexp * aexp
    | Set of var * aexp
    | Op of operator * aexp list
  and exp =
    | Let of var * exp *  exp
    | LetRec of var * exp * exp
    | CExp of cexp
    | AExp of aexp

  let rec free = function
    | Let (v, exp, body) ->
      StringSet.union (free exp) (StringSet.remove v (free body))
    | LetRec (v, exp, body) ->
      StringSet.remove v (StringSet.union (free exp) (free body))
    | AExp ae -> free_aexp ae
    | CExp ce -> free_cexp ce
  and free_cexp = function
    | Call (f, ae) ->
      StringSet.union (free_aexp f) (free_aexp ae)
    | Set (v, ae) ->
      StringSet.add v (free_aexp ae)
    | Op (op, args) ->
      BatList.fold_left (fun acc arg -> StringSet.union acc (free_aexp arg))
        StringSet.empty args
  and free_aexp = function
    | Var v -> StringSet.singleton v
    | Lambda (v, exp) -> StringSet.remove v (free exp)
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
    | Id -> "id"
  let rec string_of_exp = function
    | Let (v, exp, body) ->
      Printf.sprintf "(let ((%s %s)) %s)"
        v (string_of_exp exp) (string_of_exp body)
    | LetRec (v, exp, body) ->
      Printf.sprintf "(letrec ((%s %s)) %s)"
        v (string_of_exp exp) (string_of_exp body)
    | CExp ce -> string_of_cexp ce
    | AExp ae -> string_of_aexp ae
  and string_of_cexp = function
    | Call (f, ae) ->
      Printf.sprintf "(%s %s)" (string_of_aexp f) (string_of_aexp ae)
    | Set (v, ae) ->
      Printf.sprintf "(set! %s %s)" v (string_of_aexp ae)
    | Op (op, args) ->
      Printf.sprintf "(%s %s)"
        (string_of_op op) (String.concat " " (BatList.map string_of_aexp args))
  and string_of_aexp = function
    | Var v -> v
    | Lambda (v, e) ->
      Printf.sprintf "(lambda (%s) %s)" v (string_of_exp e)
    | Int n ->
      string_of_int n
    | True -> "#t"
    | False -> "#f"

  module Address = IntegerAddress
  type addr = Address.t
  module AddressSet = BatSet.Make(Address)

  module Env = MapEnv(Address)
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
  }
  type frame =
    | FLet of var * exp * env
    | FLetRec of Address.t * var * exp * env
    | FMark of id * Lattice.t

  let create_id lam env store : id = (lam, env)

  let string_of_frame = function
    | FLet (v, e, env) -> Printf.sprintf "Let(%s)" v
    | FLetRec (a, v, e, env) -> Printf.sprintf "LetRec(%s)" v
    | FMark _ -> Printf.sprintf "Mark"

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
    | FMark ((lam, env), d), FMark ((lam', env'), d') ->
      order_concat [lazy (Pervasives.compare lam lam');
                    lazy (Env.compare env env');
                    lazy (Lattice.compare d d')]

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
    string_of_control state.control

  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged

  let compare_stack_change g1 g2 = match (g1, g2) with
    | StackPop f1, StackPop f2 -> compare_frame f1 f2
    | StackPush f1, StackPush f2 -> compare_frame f1 f2
    | StackUnchanged, StackUnchanged -> 0
    | StackPop _, _ -> 1
    | _, StackPop _ -> -1
    | StackPush _, StackUnchanged -> 1
    | StackUnchanged, _ -> -1

  let string_of_stack_change = function
    | StackPush f -> "+" ^ (string_of_frame f)
    | StackPop f -> "-" ^ (string_of_frame f)
    | StackUnchanged -> "e"

  module FrameOrdering = struct
    type t = frame
    let compare = compare_frame
  end

  module StackChangeOrdering = struct
    type t = stack_change
    let compare = compare_stack_change
  end

  let atomic_eval atom env store =
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

  let alloc v state =
    Address.alloc (Store.size state.store + 1)
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

  let touch = function
    | FLet (v, e, env) ->
      StringSet.fold (fun v' acc ->
          if v' = v then
            acc
          else
            AddressSet.add (Env.lookup env v') acc)
        (free e) AddressSet.empty
    | FLetRec (a, v, e, env) ->
      AddressSet.add a (StringSet.fold (fun v' acc ->
          if v' = v then
            acc
          else
            AddressSet.add (Env.lookup env v') acc)
        (free e) AddressSet.empty)
    | FMark (_, _) ->
      AddressSet.empty

  let push (addrs, procids) f =
    (AddressSet.union addrs (touch f),
     match f with
     | FMark (id, _) -> ProcIdSet.add id procids
     | _ -> procids)

  let reachable (addrs, _) = addrs

  let marked (_, procids) = procids
end

module ANFGarbageCollected : Lang_signature with type exp = ANFStructure.exp =
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
      memo = memo_empty; reads = reads_empty},
     Summary.empty)

  let apply_kont f d state = match f with
    | FLet (v, e, env') ->
      let a = alloc v state in
      let env'' = Env.extend env' v a in
      let store' = Store.join state.store a d in
      {state with store = store'; env = env''; control = Exp e}
    | FLetRec (a, v, e, env') ->
      let store' = Store.join state.store a d in (* TODO: set *)
      {state with store = store'; control = Exp e}
    | FMark (id, d_arg) ->
      {state with memo = match ProcIdMap.find id state.memo with
           | Table table ->
             ProcIdMap.add id (Table (ValueTable.add d_arg d table)) state.memo
           | exception Not_found ->
             ProcIdMap.add id (Table (ValueTable.add d_arg d ValueTable.empty)) state.memo
           | Impure | Poly -> state.memo}

  let update_memo memo ids =
    ProcIdSet.fold (fun id acc ->
        if ProcIdMap.mem id acc then
          ProcIdMap.add id Poly acc
        else
          acc) ids memo

  let update_reads reads addrs marked =
    AddressSet.fold (fun addr acc ->
        AddressMap.add addr (ProcIdSet.union marked
                               (if AddressMap.mem addr acc then
                                  AddressMap.find addr acc
                                else
                                  ProcIdSet.empty)) acc)
      addrs reads

  let apply_op op args = match op with
    | Plus | Minus | Times | Divide -> Lattice.abst [V.Num]
    | Lesser | LesserOrEqual | Greater | GreaterOrEqual -> Lattice.abst [V.Boolean]
    | Id -> match args with
      | x :: [] -> x
      | _ -> failwith "Invalid numbre of arguments to 'id'"

  let step_no_gc (state, ss) frame = match state.control with
    | Exp (CExp (Call (f, ae))) ->
      Printf.printf "Call\n%!";
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
                let f = FMark (id, rand) in
                (StackPush f,
                 ({control = Exp e;
                   env = Env.extend env' v a;
                   store = Store.join state.store a rand;
                   memo = memo';
                   reads = reads'}, ss)) :: acc
              | Some d ->
                (StackUnchanged, ({state with control = Val d;
                                              memo = memo';
                                              reads = reads'}, ss)) :: acc
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
            (StackUnchanged, ({state with control = Val v; store = store';
                                          memo = memo';
                                          reads = update_reads state.reads addrs
                                              (Summary.marked ss)}, ss)) :: acc
          | _ -> acc) [] (Lattice.concretize clo)
    | Exp (CExp (Op (op, args))) ->
      let (revds, addrs, ids) = BatList.fold_left (fun (ds, addrs, ids) arg ->
          let (d, addrs', ids') = atomic_eval arg state.env state.store in
          (d :: ds, AddressSet.union addrs addrs', ProcIdSet.union ids ids'))
          ([], AddressSet.empty, ProcIdSet.empty) args in
      let ds = BatList.rev revds in
      let d = apply_op op ds in
      [(StackUnchanged, ({state with control = Val d;
                                     memo = update_memo state.memo ids;
                                     reads = update_reads state.reads addrs
                                         (Summary.marked ss)}, ss))]
    | Exp (AExp ae) ->
      let (clo, addrs, ids) = atomic_eval ae state.env state.store in
      [(StackUnchanged, ({state with control = Val clo;
                                     memo = update_memo state.memo ids;
                                     reads = update_reads state.reads addrs
                                         (Summary.marked ss)}, ss))]
    | Exp (Let (v, cexp, exp)) ->
      let f = FLet (v, exp, state.env) in
      [(StackPush f, ({state with control = Exp exp}, Summary.push ss f))]
    | Exp (LetRec (v, cexp, exp)) ->
      let a = alloc v state in
      let env' = Env.extend state.env v a in
      let store' = Store.join state.store a (Lattice.abst [V.Undefined]) in
      let f = FLetRec (a, v, exp, env') in
      [(StackUnchanged, ({state with control = Exp exp;
                                     env = env'; store = store'}, Summary.push ss f))]
    | Val v -> begin match frame with
        | Some ((_, ss'), f) ->
          [(StackPop f, (apply_kont f v state, ss'))]
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
    | Exp e -> AddressSet.union (Summary.reachable ss) (addresses_of_vars (free e) state.env)
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
    step_no_gc (gc conf)

  let conf_color (state, _) = match state.control with
    | Exp _ -> 0xFFDDDD
    | Val _ -> 0xDDFFDD
end

module type BuildDSG_signature =
  functor (L : Lang_signature) ->
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
  end

module BuildDSG : BuildDSG_signature =
  functor (L : Lang_signature) ->
  struct
    module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(struct
        include L.ConfOrdering
        let hash = Hashtbl.hash
        let equal x y = compare x y == 0
      end)(struct
        include L.StackChangeOrdering
        let default = L.StackUnchanged
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
        [`Label (L.string_of_stack_change f)]
      let default_edge_attributes _ = []
      let get_subgraph _ = None
      let vertex_name (state : V.t) =
        (string_of_int (node_id state))
      let vertex_attributes (state : V.t) =
        [`Label (L.string_of_conf state);
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
      | L.StackUnchanged ->
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

let _ =
  let exp = let open ANFStructure in
    Let ("f",
         AExp (Lambda ("x", AExp (Var "x"))),
         Let ("u", (CExp (Call (Var "f", Int 1))),
              CExp (Call (Var "f", Int 3)))) in
  let dsg = DSG.build_dyck exp in
  DSG.output_dsg dsg "dsg.dot";
  DSG.output_ecg dsg "ecg.dot"

