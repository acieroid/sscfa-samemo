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
end

module SetLattice : functor (V : BatInterfaces.OrderedType)
  -> Lattice_signature with type elt = V.t =
  functor (V : BatInterfaces.OrderedType) ->
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
end

module ANFStructure =
struct
  type var = string
  and lam = var * exp
  and aexp =
    | Var of var
    | Lambda of lam
  and cexp =
    | Call of aexp * aexp
    | Set of var * aexp
  and exp =
    | Let of var * cexp *  exp
    | CExp of cexp
    | AExp of aexp

  let rec free = function
    | Let (v, cexp, exp) ->
      StringSet.remove v (StringSet.union (free_cexp cexp) (free exp))
    | AExp ae -> free_aexp ae
    | CExp ce -> free_cexp ce
  and free_cexp = function
    | Call (f, ae) ->
      StringSet.union (free_aexp f) (free_aexp ae)
    | Set (v, ae) ->
      StringSet.add v (free_aexp ae)
  and free_aexp = function
    | Var v -> StringSet.singleton v
    | Lambda (v, exp) -> StringSet.remove v (free exp)

  let rec string_of_exp = function
    | Let (v, cexp, exp) ->
      Printf.sprintf "(let ((%s %s)) %s)"
        v (string_of_cexp cexp) (string_of_exp exp)
    | CExp ce -> string_of_cexp ce
    | AExp ae -> string_of_aexp ae
  and string_of_cexp = function
    | Call (f, ae) ->
      Printf.sprintf "(%s %s)" (string_of_aexp f) (string_of_aexp ae)
    | Set (v, ae) ->
      Printf.sprintf "(set! %s %s)" v (string_of_aexp ae)
  and string_of_aexp = function
    | Var v -> v
    | Lambda (v, e) ->
      Printf.sprintf "(lambda (%s) %s)" v (string_of_exp e)

  module Address = IntegerAddress
  type addr = Address.t

  module Env = MapEnv(IntegerAddress)
  type env = Env.t

  type clo = lam * env

  let compare_clo (lam1, env1) (lam2, env2) =
    order_concat [lazy (Pervasives.compare lam1 lam2);
                  lazy (Env.compare env1 env2)]

  module V = struct
    type t =
      | Clos of clo
      | Undefined
    let compare x y = match x, y with
      | Clos c, Clos c' -> compare_clo c c'
      | Clos _, _ -> 1
      | _, Clos _ -> -1
      | Undefined, Undefined -> 0
  end
  module Lattice = SetLattice(V)
  module Store = MapStore(Lattice)(Address)

  type store = Store.t
  type state = exp * env * store
  type frame = var * exp * env

  let string_of_frame (v, e, env) = "(" ^ v ^ ", " ^ (string_of_exp e) ^ ")"

  let compare_frame (v1, exp1, env1) (v2, exp2, env2) =
    order_concat [lazy (Pervasives.compare v1 v2);
                  lazy (Pervasives.compare exp1 exp2);
                  lazy (Env.compare env1 env2)]

  let compare_state (exp1, env1, store1) (exp2, env2, store2) =
    order_concat
      [lazy (Pervasives.compare exp1 exp2);
       lazy (Env.compare env1 env2);
       lazy (Store.compare store1 store2)]

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

  let atomic_eval atom env store = match atom with
    | Var var -> Store.lookup store (Env.lookup env var)
    | Lambda lam -> Lattice.abst [V.Clos (lam, env)]

  let alloc v state = match state with
    | (_, _, store) -> Address.alloc (Store.size store + 1)
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
end

module ReachableAddressesSummary =
struct
  module AddressSet = BatSet.Make(ANFStructure.Address)
  type t = AddressSet.t
  let empty = AddressSet.empty
  let compare = AddressSet.compare
  let to_string ss = "[" ^ (String.concat ", "
                              (BatList.map ANFStructure.Address.to_string
                                 (AddressSet.elements ss))) ^ "]"

  let touch (v, e, env) =
    StringSet.fold (fun v' acc ->
        if v' = v then
          acc
        else
          AddressSet.add (ANFStructure.Env.lookup env v') acc)
      (ANFStructure.free e) AddressSet.empty

  let push ss f =
    AddressSet.union ss (touch f)
end

module ANFGarbageCollected : Lang_signature with type exp = ANFStructure.exp =
struct
  include ANFStructure

  module AddressSet = BatSet.Make(Address)
  module Summary = ReachableAddressesSummary
  type conf = state * Summary.t

  let compare_conf (s1, ss1) (s2, ss2) =
    order_concat [lazy (compare_state s1 s2);
                  lazy (Summary.compare ss1 ss2)]

  let string_of_conf ((e, _, _), ss) = (string_of_exp e) ^ " " ^
                                       (Summary.to_string ss)

  let inject e =
    ((e, Env.empty, Store.empty), Summary.empty)

  let apply_kont f d state = match f with
    | (v, e, env') ->
      let a = alloc v state in
      let env'' = Env.extend env' v a in
      let (_, _, store) = state in
      let store' = Store.join store a d in
      (e, env'', store')

  let step_no_gc (state, ss) frame = match state with
    | (CExp (Call (f, ae)), env, store) ->
      let rands = atomic_eval f env store in
      let rator = atomic_eval ae env store in
      List.fold_left (fun acc -> function
        | V.Clos ((v, e), env') ->
          let a = alloc v state in
          ((StackUnchanged,
            ((e, Env.extend env' v a,
              Store.join store a rator), ss))
           :: acc)
        | V.Undefined -> acc)
        [] (Lattice.concretize rands)
    | (CExp (Set (v, ae)) as cexp, env, store) ->
      let clo = atomic_eval ae env store in
      let addr = Env.lookup env v in
      begin match frame with
        | Some ((_, ss'), f) ->
          let store' = Store.join store addr clo in (* TODO: set *)
          let state' = (cexp, env, store') in
          [(StackPop f, (apply_kont f (Lattice.abst [V.Undefined]) state', ss'))]
        | None ->
          print_endline "No frame when popping, reached end of evaluation";
          []
      end
    | (AExp ae, env, store) -> begin match frame with
        | Some ((_, ss'), f) ->
          [(StackPop f, (apply_kont f (atomic_eval ae env store) state, ss'))]
        | None ->
          print_endline "No frame when popping, reached end of evaluation";
          []
      end
    | (Let (v, cexp, exp), env, store) ->
      let f = (v, exp, env) in
      [(StackPush f, ((CExp cexp, env, store), Summary.push ss f))]

  module ConfOrdering = struct
    type t = conf
    let compare = compare_conf
  end

  let addresses_of_vars vars env =
    StringSet.fold (fun v acc ->
        AddressSet.add (Env.lookup env v) acc)
      vars AddressSet.empty

  let root (((e, env, store), ss) : conf) =
    AddressSet.union ss (addresses_of_vars (free e) env)

  let touch (lam, env) =
    addresses_of_vars (free (AExp (Lambda lam))) env

  (* Applies one step of the touching relation *)
  let touching_rel1 addr store =
    List.fold_left (fun acc -> function
      | V.Clos a -> AddressSet.union acc (touch a)
      | V.Undefined -> acc)
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
    let ((_, _, store), _) = conf in
    AddressSet.fold (fun a acc ->
        AddressSet.union acc (touching_rel a store))
      (root conf) AddressSet.empty

  let gc conf =
    let ((exp, env, store), ss) = conf in
    ((exp, env, Store.restrict store (AddressSet.to_list (reachable conf))), ss)

  let step conf = step_no_gc (gc conf)

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
        [`Label (L.string_of_conf state)]
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
        (* output_dsg dsg ("/tmp/dsg/dsg-" ^ (string_of_int !i) ^ ".dot"); *)
        (* output_ecg dsg ("/tmp/dsg/ecg-" ^ (string_of_int !i) ^ ".dot"); *)
        if not (EpsSet.is_empty dh) then
          let c, c' = EpsSet.choose dh in
          print_string ("eps: " ^ (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c'));
          print_newline ();
          let (ds', de', dh') = add_short dsg c c' in
          loop { dsg with ecg = G.add_edge dsg.ecg c c' }
            (ConfSet.union ds ds')
            (EdgeSet.union de de')
            (EpsSet.remove (c, c') (EpsSet.union dh dh'))
        else if not (EdgeSet.is_empty de) then
          let c, g, c' = EdgeSet.choose de in
          print_string ("edge: " ^ (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c'));
          print_newline ();
          let (ds', de', dh') = add_edge dsg c g c' in
          loop { dsg with g = G.add_edge_e dsg.g (c, g, c') }
            (ConfSet.union ds ds')
            (EdgeSet.remove (c, g, c') (EdgeSet.union de de'))
            (EpsSet.union dh dh')
        else if not (ConfSet.is_empty ds) then
          let c = ConfSet.choose ds in
          print_string ("conf: " ^ (L.string_of_conf c));
          print_newline ();
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
         (Call ((Lambda ("x", AExp (Var "x"))), (Lambda ("x", AExp (Var "x"))))),
         Let ("u", (Call (Var "f", Var "f")),
              CExp (Call (Var "f", Var "u")))) in
  let dsg = DSG.build_dyck exp in
  DSG.output_dsg dsg "dsg.dot";
  DSG.output_ecg dsg "ecg.dot"
