type loc = {
  line: int;
  col: int;
  len: int;
}

module Identifier = struct
  type t = {
   name: string;
   loc: loc;
  }

  let reserved_words = [
    "empty";
    "union";
    "inter";
    "diff";
    "in";
    "subset";
    "let";
    "where";
    "type";
    "module";
    "Set";
    "Prop";
    "true";
    "false";
    "axiom";
    "theorem";
    "proof";
  ]

  let is_valid_first_char c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'

  let is_valid_char c =
    is_valid_first_char c || (c >= '0' && c <= '9') || c = '\''

  let validate name loc =
    if String.length name = 0 then
      Error "Identifier cannot be empty"
    else if String.length name > 255 then
      Error "Identifier too long max 255 characters)"
    else if List.mem name reserved_words then
      Error (Printf.sprintf "'%s' is a reserved word" name)
    else if not (is_valid_first_char name.[0]) then
      Error "Identifier must start with a letter or underscore"
    else if not (String.for_all is_valid_char name) then
      Error "Identifier contains invalid characters"
    else Ok { name; loc }

  let to_string id = id.name
end

type expr =
  | EmptySet of loc
  | Variable of Identifier.t
  | Union of expr * expr * loc
  | Intersection of expr * expr * loc
  | SetDifference of expr * expr * loc
  | Element of expr * expr * loc
  | Subset of expr * expr * loc
  | ComprehensionSet of Identifier.t * expr * loc

type parse_error =
  | LexError of string * loc
  | ParseError of string * loc
  | IdentifierError of string * loc

exception ZornError of parse_error

type token = {
  token_type: token_type;
  loc: loc;
}
and token_type =
  | IDENT of string
  | EMPTY
  | UNION
  | INTER
  | DIFF
  | ElEMENT
  | SUBSET
  | LPAREN
  | RPAREN
  | LCURLY
  | RCURLY
  | BAR
  | EOF

let tokenize input =
  let pos = ref { line = 1; col = 1; len = 0 } in
  let advance n =
    pos := {
      line = !pos.line;
      col = !pos.col + n;
      len = n;
    }
  in
  let newline () =
    pos := {
      line = !pos.line + 1;
      col = 1;
      len = 1;
    }
  in

  let rec tokenize_helper index =
  if index >= String.length input then
    [{ token_type = EOF; loc = !pos }]
  else
    let current_loc = !pos in
    match input.[index] with
    | ' ' | '\t' -> advance 1; tokenize_helper (index + 1)
    | '\n' -> newline (); tokenize_helper (index + 1)
    | '(' -> advance 1;
      { token_type = LPAREN; loc = current_loc } :: tokenize_helper (index + 1)
    | ')' -> advance 1;
      { token_type = RPAREN; loc = current_loc } :: tokenize_helper (index + 1)
    | '{' -> advance 1;
      { token_type = LCURLY; loc = current_loc } :: tokenize_helper (index + 1)
    | '}' -> advance 1;
      { token_type = RCURLY; loc = current_loc } :: tokenize_helper (index + 1)
    | c when Identifier.is_valid_first_char c ->
      let rec read_ident pos acc =
      if pos >= String.length input then
        (acc, pos)
      else if Identifier.is_valid_char input.[pos] then
        read_ident (pos + 1) (acc ^ String.make 1 input.[pos])
      else
        (acc, pos)
    in
    let (ident, new_pos) = read_ident index "" in
      advance (String.length ident);
    let token = match ident with
      | "empty" -> EMPTY
      | "union" -> UNION
      | "inter" -> INTER
      | "diff" -> DIFF
      | "in" -> ElEMENT
      | "subset" -> SUBSET
      | _ -> IDENT ident
    in
      { token_type = token; loc = current_loc } :: tokenize_helper new_pos

    | c -> raise (ZornError (LexError (Printf.sprintf "Unexpected character: '%c'" c, current_loc)))
  in
  tokenize_helper 0

let parse tokens =
  let rec parse_expr tokens =
    match tokens with
    | { token_type = EMPTY; loc } :: rest -> (EmptySet loc, rest)
    | { token_type = IDENT name; loc } :: rest ->
      (match Identifier.validate name loc with
        | Ok id -> (Variable id, rest)
        | Error msg -> raise (ZornError (IdentifierError (msg, loc))))
    | { token_type = LCURLY; loc } ::
      { token_type = IDENT name; loc = var_loc } ::
      { token_type = BAR; _ } :: rest ->
       (match Identifier.validate name var_loc with
        | Ok var_id ->
          let (pred, rest1) = parse_expr rest in
          (match rest1 with
           | { token_type = RCURLY; _ } :: rest2 ->
             (ComprehensionSet (var_id, pred, loc), rest2)
           | { loc; _ } :: _ ->
             raise (ZornError (ParseError ("Expected closing brace", loc)))
           | [] -> raise (ZornError (ParseError ("Unexpected end of input", loc))))
        | Error msg ->
           raise (ZornError (IdentifierError (msg, var_loc))))
    | { token_type = LCURLY; loc } :: _ :: _ :: _ ->
       raise (ZornError (ParseError ("Invalid comprehension syntax", loc)))
    | { loc; _ } :: _ ->
      raise (ZornError (ParseError ("Expected expression", loc)))
    | [] -> raise (ZornError (ParseError ("Unexpected end of input",
      { line = 0; col = 0; len = 0 })))
  in
  let (expr, remaining) = parse_expr tokens in
  match remaining with
  | [] -> expr
  | { loc; _ } :: _ ->
    raise (ZornError (ParseError ("Unexpected tokens after expression", loc)))
