module type ELEMENT = sig (* Core type definitions  *)
  type t
  val compare : t -> t -> int
  val to_string : t -> string
  val of_int : int -> t
end

module SetTheory (E: ELEMENT) = struct
  module ElementSet = Set.Make(E)

  type element =
    | Atom of E.t
    | Pair of element * element
    | Empty

  type set_value =
    | Finite of ElementSet.t
    | Function of (element -> element option)
    | Comprehension of (element -> bool) * set_value
    | Union of set_value * set_value
    | Intersection of set_value * set_value
    | PowerSet of set_value
    | LazySet of (unit -> element Seq.t)

  type set = {
    value: set_value;
    universe: set_value option; (* For bounded quantification *)
  }

  (* Exception definitions *)
  exception InvalidSetOperation of string
  exception UndefinedOperation of string

  (* Comparison functions for elements *)
  let rec compare_elements a b = match (a, b) with
    | (Empty, Empty) -> 0
    | (Empty, _) -> -1
    | (_, Empty) -> 1
    | (Atom x, Atom y) -> E.compare x y
    | (Pair(a1, b1), Pair(a2, b2)) ->
        let cmp = compare_elements a1 a2 in
        if cmp = 0 then compare_elements b1 b2 else cmp
    | (Atom _, Pair _) -> -1
    | (Pair _, Atom _) -> 1

  let empty = { value = Finite ElementSet.empty; universe = None }

  let singleton (x: element) : set =
    { value = Finite (ElementSet.singleton (match x with
      | Atom v -> v
      | _ -> raise
        (InvalidSetOperation "Can only create singleton of atoms")));
    universe = None }

  let rec member x s = match s.value with
      | Finite set ->
          (match x with
           | Atom v -> ElementSet.mem v set
           | _ -> false)
      | Function _ -> false (* Functions aren't elements *)
      | Comprehension (p, set) ->
          p x && member x { value = set; universe = None }

      | Union (s1, s2) ->
          member x {value = s1; universe = None} ||
          member x {value = s2; universe = None}
      | Intersection (s1, s2) ->
          member x {value = s1; universe = None} &&
          member x {value = s2; universe = None}
      | PowerSet set ->
          (* x must be a set and a subset of base *)
          match x with
          | Empty -> true
          | _ -> false (* Need more complex subset checking *)
      | LazySet gen ->
          Seq.exists ((=) x) (gen ())

  (* Function application *)
  let apply f arg = match f.value with
    | Function g -> g arg
    | _ -> raise (InvalidSetOperation "Not a function")

  (* Set operations *)
  let union s1 s2 = { value = Union (s1.value, s2.value); universe = None }

  let intersection s1 s2 = { value = Intersection (s1.value, s2.value); universe = None }

  let comprehension pred set = { value = Comprehension (pred, set.value); universe = None }

  (* Power Set construction *)
  let power_set s = { value = PowerSet s.value; universe = None }

  let filter_set p set =
    ElementSet.fold
      (fun x acc -> if p x then ElementSet.add x acc else acc)
      set
      ElementSet.empty

  (* Type system with bounded quantification *)
  module Type = struct
   type  t =
      | SetOf of t
      | FunctionSpace of t * t
      | Universal of string * t (* For polymorphic types *)
      | Bounded of string * t * t (* For bounded quantification *)

   let rec check_type expr typ = match (expr, typ) with
     | ({ value = Finite _ }, SetOf _) -> true
     | ({ value = Function f }, FunctionSpace (dom, cod)) ->
        (* Would need to check domain and codomain *)
        true
     | _ -> false
  end

  (* Support for infinite sets *)
  module Infinite = struct
    (* Natural numbers using von Neuman construction *)
    let naturals =
      let gen () =
        let rec next n =
          Seq.cons (Atom (E.of_int n)) (Seq.delay (fun () ->
            next (n + 1))) in
        next 0
      in { value = LazySet gen; universe = None }

      (* Constructive operations on infinite sets *)
    let map f set = match set.value with
      | LazySet gen ->
         { value = LazySet (fun () -> Seq.map f (gen ())); universe = None }
      | _ -> raise (InvalidSetOperation "Not a lazy set")

    let filter p set = match set.value with
      | LazySet gen ->
          { value = LazySet (fun () -> Seq.filter p (gen ())); universe = None }
      | _ -> raise (InvalidSetOperation "Not a lazy set")
  end

  (* Category thepry inspired operations *)
  module Category = struct
    (* Composition of functions as relations *)
    let compose f g = match (f.value, g.value) with
      | (Function f', Function g') ->
          { value = Function (fun x ->
            match g' x with
            | Some y -> f' y
            | None -> None); universe = None }
      | _ -> raise (InvalidSetOperation "Cannot compose non-functions")

    (* Product of sets *)
    let product s1 s2 = match (s1.value, s2.value) with
      | (Finite set1, Finite set2) ->
        let pairs = ElementSet.fold
          (fun x acc ->
            ElementSet.fold
              (fun y acc ->
                ElementSet.add x acc)
              set2 acc)
          set1 ElementSet.empty in
        { value = Finite pairs; universe = None }
      | _ -> raise (InvalidSetOperation "Cannot compute product of infinite sets")
  end

  (* Evaluation strategies *)
  module Eval = struct
  let rec force_finite = function
    | { value = Finite s } -> s
    | { value = Comprehension (p, set) } ->
      let base_set = force_finite {value = set; universe = None} in
      filter_set (fun x -> p (Atom x)) base_set
    | { value = Union (s1, s2) } ->
      ElementSet.union
        (force_finite {value = s1; universe = None})
        (force_finite {value = s2; universe = None})
    | { value = Intersection (s1, s2) } ->
      ElementSet.inter
        (force_finite {value = s1; universe = None})
        (force_finite {value = s2; universe = None})
    | _ -> raise (InvalidSetOperation "Cannot force infinite set to finite")

    let take n { value = LazySet gen } =
      let elements = Seq.take n (gen ())
        |> List.of_seq
        |> List.filter_map (function
          | Atom x -> Some x
          | _ -> None) in
      let set = List.fold_left (fun acc x -> ElementSet.add x acc)
        ElementSet.empty
        elements in
      { value = Finite set; universe = None }
  end
end

(* Example usage *)
module StringElement = struct
  type t = string
  let compare = String.compare
  let to_string x = x
  let of_int n = string_of_int n
end

module StringSet = SetTheory(StringElement)

let example () =
  let open StringSet in
  (* Create some basic sets *)
  let s1 = singleton (Atom "a") in
  let s2 = singleton (Atom "b") in
  let union_set = union s1 s2 in

  (* Create a function as a set *)
  let increment = {
    value = Function (function
      | Atom s -> Some (Atom (s ^ "1"))
      | _ -> None);
    universe = None
  } in

  (* Use category operations *)
  let product = Category.product s1 s2 in

  (* Work with infinite sets *)
  let first_10_naturals =
    Infinite.naturals
    |> Infinite.filter (fun x -> true) (* Example predicate *)
    |> Eval.take 10
  in
  ()

module Interpreter = struct

  type expr =
    | EEmpty
    | ESingleton of StringSet.element
    | EUnion of expr * expr
    | EComprehension of string * expr * expr (* Variable, predicate, set *)
    | EApply of expr * expr

  let rec eval env = function
    | EEmpty -> StringSet.empty
    | ESingleton e -> StringSet.singleton e
    | EUnion (e1, e2) -> StringSet.union (eval env e1) (eval env e2)
    | EComprehension (var, set, pred) ->
      (* Would need environment handling *)
      StringSet.empty
    | EApply (f, arg) ->
    let f_val = eval env f in
    let arg_val = eval env arg in
    match StringSet.apply f_val (StringSet.Atom "dummy") with
    | Some result -> StringSet.singleton result
    | None -> StringSet.empty
end
