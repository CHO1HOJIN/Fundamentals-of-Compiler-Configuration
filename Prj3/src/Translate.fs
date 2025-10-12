module Translate

open AST
open IR
open Helper

// Symbol table is a mapping from identifier to a pair of register and type.
// Register is recorded here will be containg the address of that variable.
type SymbolTable = Map<Identifier,Register * CType>

let arrayRegNum = ref 0
let addrOfRegNum = ref 0
let createArrRegName () =
    let reg = sprintf "arr%d" !arrayRegNum
    let _ = arrayRegNum := !arrayRegNum + 1
    reg

let createAddrOfRegName () =
    let reg = sprintf "addr%d" !addrOfRegNum
    let _ = addrOfRegNum := !addrOfRegNum + 1
    reg

// Let's assume the following size for each data type.
let sizeof (ctyp: CType) =
  match ctyp with
  | CInt -> 4
  | CBool -> 1
  | CIntPtr -> 8
  | CBoolPtr -> 8
  | CIntArr n -> 4 * n
  | CBoolArr n -> n

// Find the register that contains pointer to variable 'vname'
let lookupVar (symtab: SymbolTable) (vname: Identifier) : Register =
  let _ = if not (Map.containsKey vname symtab) then failwith "Unbound variable"
  fst (Map.find vname symtab)

let rec transExp (symtab: SymbolTable) (e: Exp) : Register * Instr list =
  match e with
  | Null ->
      let r = createRegName ()
      (r, [Set (r, Imm 0)])
  | Num i ->
      let r = createRegName ()
      (r, [Set (r, Imm i)])
  | Boolean b ->
      let r = createRegName ()
      (r, [Set (r, Imm (if b then 1 else 0))])
  | Var vname ->
      let varReg = lookupVar symtab vname // Contains the address of 'vname'
      let r = createRegName ()
      (r, [Load (r, varReg)])
  | Deref vname ->
      let r1 = createRegName ()
      let vReg = lookupVar symtab vname
      let r = createRegName ()
      (r, [Load (r1, vReg); Load (r, r1)])
  | AddrOf x -> 
      let r = createAddrOfRegName ()
      let varReg = lookupVar symtab x
      (r, [Set (r, Reg varReg)])
  | Arr (x, e) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e
      let varReg = lookupVar symtab x
      let ctyp = 
        match snd (Map.find x symtab) with
        | CIntArr _ -> CInt
        | CBoolArr _ -> CBool
        | _ -> failwith "Invalid array type"
      let instr1 = BinOp (r, MulOp, Reg r1, Imm (sizeof ctyp))
      let r' = createRegName ()
      let r'' = createRegName ()
      let instr2 = BinOp (r', AddOp, Reg varReg, Reg r)
      (r'', instrs1 @ [instr1; instr2; Load (r'', r')])
  | Add (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, AddOp, Reg r1, Reg r2)])
  | Sub (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, SubOp, Reg r1, Reg r2)])
  | Mul (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, MulOp, Reg r1, Reg r2)])
  | Div (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, DivOp, Reg r1, Reg r2)])
  | Neg e ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e
      (r, instrs1 @ [UnOp (r, NegOp, Reg r1)])
  | Equal (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, EqOp, Reg r1, Reg r2)])
  | NotEq (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, NeqOp, Reg r1, Reg r2)])
  | LessEq (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, LeqOp, Reg r1, Reg r2)])
  | LessThan (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, LtOp, Reg r1, Reg r2)])
  | GreaterEq (e1, e2) ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, GeqOp, Reg r1, Reg r2)])
  | GreaterThan (e1, e2) ->
      let r = createRegName () 
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      (r, instrs1 @ instrs2 @ [BinOp (r, GtOp, Reg r1, Reg r2)])
  | And (e1, e2) ->
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      let l1 = createLabel()
      let l2 = createLabel()
      let r = createRegName()
      (r, instrs1 @ [GotoIfNot (Reg r1, l1)] @ instrs2 @ [GotoIfNot (Reg r2, l1); 
        Set (r, Imm 1); Goto l2; Label l1; Set (r, Imm 0); Label l2])
  | Or (e1, e2) ->
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      let l1 = createLabel()
    //   let l2 = createLabel()
      let r = createRegName()
      let r3 = createRegName()
      (r, instrs1 @ [Set (r3, Imm 1)] @ [GotoIf (Reg r1, l1)] @ instrs2 @ [Set (r3, Reg r2); Label l1; Set (r, Reg r3)])
    //   (r, instrs1 @ [GotoIf (Reg r1, l1)] @ instrs2 @ [GotoIf (Reg r2, l1); 
    //     Set (r, Imm 0); Goto l2; Label l1; Set (r, Imm 1); Label l2])
  | Not e ->
      let r = createRegName ()
      let r1, instrs1 = transExp symtab e
      (r, instrs1 @ [UnOp (r, NotOp, Reg r1)])

let rec transStmt (symtab: SymbolTable) stmt : SymbolTable * Instr list =
  match stmt with
  | Declare (_, typ, vname) ->
      let size = sizeof typ
      let r = 
        match typ with
        | CIntArr n | CBoolArr n -> createArrRegName ()
        | _ -> createRegName () 
      let symtab = Map.add vname (r, typ) symtab
      (symtab, [LocalAlloc (r, size)])
  | Define (_, typ, vname, e) ->
      let r = createRegName ()
      let size = sizeof typ
      let symtab = Map.add vname (r, typ) symtab
      let r1, instrs1 = transExp symtab e
      (symtab, instrs1 @ [LocalAlloc (r, size); Store (Reg r1, r)])
  | Assign (_, vname, e) ->
      let r1, instrs1 = transExp symtab e
      let varReg = lookupVar symtab vname
      (symtab, instrs1 @ [Store (Reg r1, varReg)])
  | PtrUpdate (_, vname, e) ->
      let r1, instrs1 = transExp symtab e
      let varReg = lookupVar symtab vname
      let r2 = createRegName ()
      (symtab, instrs1 @ [Load (r2, varReg); Store (Reg r1, r2)])
  | ArrUpdate (_, vname, e1, e2) ->
      let r1, instrs1 = transExp symtab e1
      let r2, instrs2 = transExp symtab e2
      let off1 = createRegName ()
      let off2 = createRegName ()
      let varReg = lookupVar symtab vname
      let ctyp = 
        match snd (Map.find vname symtab) with
        | CIntArr _ -> CInt
        | CBoolArr _ -> CBool
        | _ -> failwith "Invalid array type"
      (symtab, instrs1 @ instrs2 @ [BinOp (off1, MulOp, Reg r1, Imm (sizeof ctyp));
        BinOp (off2, AddOp, Reg varReg, Reg off1); Store (Reg r2, off2)])
  | If (_, e, stmts1, stmts2) ->
      let r, instrs = transExp symtab e
      let l1 = createLabel ()
      let l2 = createLabel ()
      let instrs1 = transStmts symtab stmts1
      let instrs2 = transStmts symtab stmts2
      (symtab, instrs @ [GotoIfNot (Reg r, l1)] @ instrs1 @ [Goto l2; Label l1] @ instrs2 @ [Label l2])
  | While (_, e, stmts) ->
      let r, instrs = transExp symtab e
      let instrs' = transStmts symtab stmts
      let l1 = createLabel ()
      let l2 = createLabel ()
      (symtab, [Label l1] @ instrs @ [GotoIfNot (Reg r, l2)] @ instrs' @ [Goto l1] @ [Label l2])
  | Return (_, e) ->
      let r, instrs = transExp symtab e
      (symtab, instrs @ [Ret (Reg r)])

and transStmts symtab stmts: Instr list =
  match stmts with
  | [] -> []
  | headStmt :: tailStmts ->
      let symtab, instrs = transStmt symtab headStmt
      instrs @ transStmts symtab tailStmts

// This code allocates memory for each argument and records information to the
// symbol table. Note that argument can be handled similarly to local variable.
let rec transArgs accSymTab accInstrs args =
  match args with
  | [] -> accSymTab, accInstrs
  | headArg :: tailArgs ->
      // In our IR model, register 'argName' is already defined at the entry.
      let (argTyp, argName) = headArg
      let r = createRegName ()
      let size = sizeof argTyp
      // From now on, we can use 'r' as a pointer to access 'argName'.
      let accSymTab = Map.add argName (r, argTyp) accSymTab
      let accInstrs = [LocalAlloc (r, size); Store (Reg argName, r)] @ accInstrs
      transArgs accSymTab accInstrs tailArgs

// Translate input program into IR code.
let run (prog: Program) : IRCode =
  let (_, fname, args, stmts) = prog
  let argRegs = List.map snd args
  let symtab, argInstrs = transArgs Map.empty [] args
  let bodyInstrs = transStmts symtab stmts
  (fname, argRegs, argInstrs @ bodyInstrs)
