module TypeCheck

open AST

// Symbol table is a mapping from 'Identifier' (string) to 'CType'. Note that
// 'Identifier' and 'Ctype' are defined in AST.fs file.
type SymbolTable = Map<Identifier,CType>

// For semantic analysis, you will need the following type definition. Note the
// difference between 'Ctype' and 'Typ': 'Ctype' represents the type annoted in
// the C code, whereas 'Typ' represents the type obtained during type checking.
type Typ = Int | Bool | NullPtr | IntPtr | BoolPtr | Error

// Convert 'CType' into 'Typ'.
let ctypeToTyp (ctype: CType) : Typ =
  match ctype with
  | CInt -> Int
  | CBool -> Bool
  | CIntPtr -> IntPtr
  | CBoolPtr -> BoolPtr

// Check expression 'e' and return its type. If the type of expression cannot be
// decided due to some semantic error, return 'Error' as its type.
let rec checkExp (symTab: SymbolTable) (e: Exp) : Typ =
  match e with
  | Null -> NullPtr
  | Num _ -> Int
  | Boolean _ -> Bool
  | Var x -> 
      match Map.tryFind x symTab with
      | Some typ -> ctypeToTyp typ
      | None -> Error
  | Deref x ->
      match Map.tryFind x symTab with
      | Some CIntPtr -> Int
      | Some CBoolPtr -> Bool
      | _ -> Error
  | AddrOf x -> 
      match Map.tryFind x symTab with
      | Some CInt -> IntPtr
      | Some CBool -> BoolPtr
      | _ -> Error
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) ->
      let typ1 = checkExp symTab e1
      let typ2 = checkExp symTab e2
      match (typ1, typ2) with
      | (Int, Int) -> Int
      | _ -> Error
  | Neg e ->
      let typ = checkExp symTab e
      match typ with
      | Int -> Int
      | _ -> Error
  | LessEq (e1, e2) | LessThan (e1, e2) | GreaterEq (e1, e2) | GreaterThan (e1, e2) ->
      let typ1 = checkExp symTab e1
      let typ2 = checkExp symTab e2
      match (typ1, typ2) with
      | (Int, Int) -> Bool
      | _ -> Error
  | Equal (e1, e2) | NotEq (e1, e2) ->
      let typ1 = checkExp symTab e1
      let typ2 = checkExp symTab e2
      match (typ1, typ2) with
      | (Int, Int) | (Bool, Bool) | (IntPtr, IntPtr) | (BoolPtr, BoolPtr) | (NullPtr, BoolPtr)
      | (NullPtr, NullPtr) | (IntPtr, NullPtr) | (BoolPtr, NullPtr) | (NullPtr, IntPtr) -> Bool
      | _ -> Error
  | And (e1, e2) | Or (e1, e2) ->
      let typ1 = checkExp symTab e1
      let typ2 = checkExp symTab e2
      match (typ1, typ2) with
      | (Bool, Bool) -> Bool
      | _ -> Error
  | Not e ->
      let typ = checkExp symTab e
      match typ with
      | Bool -> Bool
      | _ -> Error
  // | _ -> Error // TODO: Fill in the remaining cases to complete the code.

// Check statement 'stmt' and return a pair of (1) list of line numbers that
// contain semantic errors, and (2) symbol table updated by 'stmt'.
let rec checkStmt (symTab: SymbolTable) (retTyp: CType) (stmt: Stmt) =
  match stmt with
  | Declare (line, ctyp, x) -> ([], Map.add x ctyp symTab)
  | Define (line, ctyp, x, e) ->
      let typ = checkExp symTab e
      let symTab = Map.add x ctyp symTab
      match (ctypeToTyp ctyp, typ) with
      | (Error, _) | (_, Error) -> ([line], symTab)
      | (typ', typ) -> 
        match (typ', typ) with
        | (Int, Int) | (Bool, Bool) | (IntPtr, IntPtr) | (BoolPtr, BoolPtr)
        | (IntPtr, NullPtr) | (BoolPtr, NullPtr) ->
          ([], symTab)
        | _ ->
          ([line], symTab)
  | Assign (line, x, e) ->
      let typ = checkExp symTab e
      match Map.tryFind x symTab with
      | Some ctyp ->
        match (ctypeToTyp ctyp, typ) with
        | (Int, Int) | (Bool, Bool) | (IntPtr, IntPtr) | (BoolPtr, BoolPtr) 
        | (IntPtr, NullPtr) | (BoolPtr, NullPtr) -> 
          ([], symTab)
        | _ -> ([line], symTab)
      | None -> ([line], symTab)
  | PtrUpdate (line, x, e) ->
      let typ = checkExp symTab e
      match Map.tryFind x symTab with
      | Some CIntPtr when typ = Int -> ([], symTab)
      | Some CBoolPtr when typ = Bool -> ([], symTab)
      | _ -> ([line], symTab)
  | Return (line, e) ->
      let typ = checkExp symTab e
      match (ctypeToTyp retTyp, typ) with
      | (_, Error) -> ([line], symTab)
      | (typ', typ) when typ = typ' -> ([], symTab)
      | (IntPtr, NullPtr) | (BoolPtr, NullPtr) -> ([], symTab)
      | _ -> ([line], symTab)
  | If (line, e, stmts1, stmts2) ->
      let typ = checkExp symTab e
      match typ with
      | Bool | Int | IntPtr | BoolPtr | NullPtr ->
          let errorLines1 = checkStmts symTab retTyp stmts1
          let errorLines2 = checkStmts symTab retTyp stmts2
          (errorLines1 @ errorLines2, symTab)
      | _ -> 
          let e0 = [line]
          let e1 = checkStmts symTab retTyp stmts1
          let e2 = checkStmts symTab retTyp stmts2
          (e0 @ e1 @ e2, symTab)
  | While (line, e, stmts) ->
      let typ = checkExp symTab e
      match typ with
      | Bool | Int | IntPtr | BoolPtr | NullPtr ->
          let errorLines = checkStmts symTab retTyp stmts
          (errorLines, symTab)
      | _ -> 
          let e0 = [line]
          let e1 = checkStmts symTab retTyp stmts
          (e0 @ e1, symTab)

// Check the statement list and return the line numbers of semantic errors. Note
// that 'checkStmt' and 'checkStmts' are mutually-recursive (they can call each
// other). This function design will make your code more concise.
and checkStmts symTab (retTyp: CType) (stmts: Stmt list): LineNo list =
  match stmts with
  | [] -> []
  | stmt::stmts' ->
      let (errorLines, symTab') = checkStmt symTab retTyp stmt
      errorLines @ checkStmts symTab' retTyp stmts'

// Record the type of arguments to the symbol table.
let rec collectArgTypes argDecls symTab =
  match argDecls with
  | [] -> symTab
  | (ctyp, x)::argDecls' -> collectArgTypes argDecls' (Map.add x ctyp symTab)

// Check the program and return the line numbers of semantic errors.
let run (prog: Program) : LineNo list =
  let (retTyp, _, args, stmts) = prog
  let symTab = collectArgTypes args Map.empty
  let errorLines = checkStmts symTab retTyp stmts
  // Remove duplicate entries and sort in ascending order.
  List.sort (List.distinct errorLines)
