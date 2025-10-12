module Optimize

open IR
open CFG
open DFA


let toRegister r =
  match r with
  | Reg r' -> Register r'
  | _ -> failwith "Invalid register type"

let toOperand (r: Register) = (Reg r)

module ConstantFolding =
  let foldConstant instr : Instr option =
    match instr with
    | UnOp (r, NegOp, Imm x) -> Some (Set (r, Imm (-x)))
    | UnOp (r, NotOp, Imm x) -> Some (Set (r, Imm (if x = 0 then 1 else 0)))
    | BinOp (r, AddOp, Reg r1, Imm 0) -> Some (Set (r, Reg r1))
    | BinOp (r, AddOp, Imm 0, Reg r1) -> Some (Set (r, Reg r1))
    | BinOp (r, AddOp, Imm x, Imm y) -> Some (Set (r, Imm (x + y)))
    | BinOp (r, SubOp, Reg r1, Imm 0) -> Some (Set (r, Reg r1))
    | BinOp (r, SubOp, Imm 0, Reg r1) -> Some (UnOp (r, NegOp, Reg r1))
    | BinOp (r, SubOp, Imm x, Imm y) -> Some (Set (r, Imm (x - y)))
    | BinOp (r, MulOp, Reg r1, Imm 1) -> Some (Set (r, Reg r1))
    | BinOp (r, MulOp, Reg r1, Imm 0) -> Some (Set (r, Imm 0))
    | BinOp (r, MulOp, Imm 1, Reg r1) -> Some (Set (r, Reg r1))
    | BinOp (r, MulOp, Imm 0, Reg r1) -> Some (Set (r, Imm 0))
    | BinOp (r, MulOp, Imm x, Imm y) -> Some (Set (r, Imm (x * y)))
    | BinOp (r, DivOp, Imm x, Imm y) -> Some (Set (r, Imm (x / y)))
    | BinOp (r, DivOp, Reg r1, Imm 1) -> Some (Set (r, Reg r1))
    | BinOp (r, DivOp, Imm 0, Reg r1) -> Some (Set (r, Imm 0))
    | BinOp (r, EqOp, Imm x, Imm y) -> Some (Set (r, Imm (if x = y then 1 else 0)))
    | BinOp (r, NeqOp, Imm x, Imm y) -> Some (Set (r, Imm (if x <> y then 1 else 0)))
    | BinOp (r, LeqOp, Imm x, Imm y) -> Some (Set (r, Imm (if x <= y then 1 else 0)))
    | BinOp (r, LtOp, Imm x, Imm y) -> Some (Set (r, Imm (if x < y then 1 else 0)))
    | BinOp (r, GeqOp, Imm x, Imm y) -> Some (Set (r, Imm (if x >= y then 1 else 0)))
    | BinOp (r, GtOp, Imm x, Imm y) -> Some (Set (r, Imm (if x > y then 1 else 0)))
    | GotoIf (Imm x, l) when x <> 0 -> Some (Goto l)
    | GotoIfNot (Imm 0, l) -> Some (Goto l)
    | GotoIf (Imm 0, l) -> None
    | GotoIfNot (Imm x, l) when x <> 0 -> None
    | _ -> Some instr

  // goto랑 label 사이에 label 밖에 없으면 지워도 되겠지??
  let rec foldGoto worklist =
    let rec canErase worklist' label =
      match worklist' with
      | [] -> true 
      | instr :: rest ->
        match instr with
        | Label l when l = label -> true
        | Label _ -> canErase rest label
        | _ -> false
    match worklist with
    | [] -> []
    | instr :: rest ->
      match instr with
      | Goto l when canErase rest l -> foldGoto rest
      | _ -> instr :: foldGoto rest

  let run instrs =
    let (instrMap, _, _) = CFG.make instrs
    let updatedInstrs = Map.fold (fun acc nodeId instr -> 
      match foldConstant instr with | Some i -> acc @ [i] | None -> acc ) [] instrMap
    let updatedInstrs = foldGoto updatedInstrs
    if updatedInstrs = instrs then (false, instrs) else (true, updatedInstrs)

module ConstantPropagation =

  let regToconst rdSet r =
    match r with
    | Imm x -> Imm x
    | Reg r -> 
      let rdList = Set.toList rdSet |> List.filter (fun instr -> 
        match instr with
        | Set (r1, _ ) when r = r1 -> true | _ -> false)
      if Set.count (Set.ofList rdList) = 1 then
        match List.head rdList with | Set (_, Imm x) -> Imm x | _ -> Reg r
      else Reg r

  let doConstantPropagation (rdMap: Map<int,RDSet>) (nodeId: int) (instr: Instr) cfg : Instr =
    let preds = CFG.getPreds nodeId cfg
    // RD_in[n] = ⋃ RD_out[p] for all p ∈ pred(n)
    let predRDs = Map.filter (fun k v -> List.contains k preds) rdMap
    let rdIn = 
      if predRDs = Map.empty then Set.empty
      else Map.fold (fun acc k v -> Set.union acc v) Set.empty predRDs
    match instr with
    | Set (r, r2) -> Set (r, regToconst rdIn r2)
    | UnOp (r, op, r2) -> UnOp (r, op, regToconst rdIn r2)
    | BinOp (r, op, r1, r2) -> BinOp (r, op, regToconst rdIn r1, regToconst rdIn r2)
    | Load (r1, r2) ->  Load (r1, toRegister (regToconst rdIn (toOperand r2)))
    | Store (o, r) -> Store (regToconst rdIn o, r)
    | GotoIf (r, l) -> GotoIf (regToconst rdIn r, l)
    | GotoIfNot (r, l) -> GotoIfNot (regToconst rdIn r, l)
    | Ret (r) -> Ret (regToconst rdIn r)
    | _ -> instr

  let run instrs =
    let cfg = CFG.make instrs
    let rdMap = RDAnalysis.run cfg
    let (instrMap, _, _) = cfg
    let updatedInstrs = Map.fold (fun acc nodeId instr -> 
      let updatedInstr = doConstantPropagation rdMap nodeId instr cfg
      acc @ [updatedInstr] ) [] instrMap
    if updatedInstrs = instrs then (false, instrs) else (true, updatedInstrs)

module CopyPropagation =

  let regTonewReg rdSet r =
    match r with
    | Imm x -> Imm x
    | Reg r ->
      let rdList = Set.toList rdSet
      let rdList = List.filter (fun instr -> 
        match instr with
        | Set (r1, _ ) when r = r1 -> true
        | _ -> false) rdList
      if Set.count (Set.ofList rdList) = 1 then
        match List.head rdList with
        | Set (_, Reg r2) -> Reg r2
        | _ -> Reg r
      else Reg r

  let doCopyPropagation (aeMap: Map<int,AESet>) (nodeId: int) (instr: Instr) cfg : Instr =
    let preds = CFG.getPreds nodeId cfg
    // AEin[n] = ⋂ AEout[p] for all p ∈ pred(n)
    let predAEs = Map.filter (fun k v -> List.contains k preds) aeMap
    let aeIn = 
      if predAEs = Map.empty then Set.empty
      else Map.fold (fun acc k v -> Set.intersect acc v) AEAnalysis.AllInstrSet predAEs
   
    match instr with
    | Set (r, r2) -> Set (r, regTonewReg aeIn r2)
    | UnOp (r, op, r2) -> UnOp (r, op, regTonewReg aeIn r2)
    | BinOp (r, op, r1, r2) -> BinOp (r, op, regTonewReg aeIn r1, regTonewReg aeIn r2)
    | Load (r1, r2) -> Load (r1, toRegister (regTonewReg aeIn (toOperand r2)))
    | Store (o, r) -> Store (regTonewReg aeIn o, toRegister (regTonewReg aeIn (toOperand r)))
    | GotoIf (r, l) -> GotoIf (regTonewReg aeIn r, l)
    | GotoIfNot (r, l) -> GotoIfNot (regTonewReg aeIn r, l)
    | Ret (r) -> Ret (regTonewReg aeIn r)
    | _ -> instr

  let run instrs =
    let cfg = CFG.make instrs
    let aeMap = AEAnalysis.run cfg
    let (instrMap, _, _) = cfg
    let updatedInstrs = Map.fold (fun acc nodeId instr -> 
      let updatedInstr = doCopyPropagation aeMap nodeId instr cfg
      acc @ [updatedInstr]) [] instrMap
    if updatedInstrs = instrs then (false, instrs) else (true, updatedInstrs)

module CommonSubexpressionElimination =
  
  let eliminate instr aeSet =
    let aeSeq = Set.toSeq aeSet
    match instr with
    | UnOp (r, op, o) -> 
      match Seq.tryFind (fun instr -> 
        match instr with 
        | UnOp (r1, op1, o1) when op = op1 && o = o1 -> true 
        | _ -> false) aeSeq with
      | Some (UnOp (r1, _, _)) -> Set (r, Reg r1) | _ -> instr
    | BinOp (r, op, o1, o2) -> 
      match Seq.tryFind (fun instr -> 
        match instr with 
        | BinOp (r1, op1, o11, o21) when op = op1 && o1 = o11 && o2 = o21 -> true
        | BinOp (r1, op1, o21, o11) when op = op1 && o1 = o21 && o2 = o11 && (op = AddOp || op = MulOp) -> true
        | _ -> false) aeSeq with
      | Some (BinOp (r1, _, _, _)) -> Set (r, Reg r1) | _ -> instr
    | Load (r1, r2) ->
      match Seq.tryFind (fun instr ->
        match instr with
        // | Store (o, r) when r= r2 -> true
        | Load (r1, r2') when r2 = r2' -> true
        | _ -> false) aeSeq with
      | Some (Load (r1', _)) -> Set (r1, Reg r1') | _ -> instr
    | _ -> instr 

  let doCSE (aeMap: Map<int,AESet>) (nodeId: int) (instr: Instr) cfg : Instr =
    let preds = CFG.getPreds nodeId cfg
    // AEin[n] = ⋂ AEout[p] for all p ∈ pred(n)
    let predAEs = Map.filter (fun k v -> List.contains k preds) aeMap
    let aeIn = 
      if predAEs = Map.empty then Set.empty
      else Map.fold (fun acc k v -> Set.intersect acc v) AEAnalysis.AllInstrSet predAEs
    eliminate instr aeIn
   
  let run instrs =
    let cfg = CFG.make instrs
    let aeMap = AEAnalysis.run cfg
    let instrMap, _, _ = cfg
    let updatedInstrs = Map.fold (fun acc nodeId instr ->
      let updatedInstr = doCSE aeMap nodeId instr cfg
      acc @ [updatedInstr]) [] instrMap
    if updatedInstrs = instrs then (false, instrs) else (true, updatedInstrs)

module DeadCodeElimination =

  let isContained r laOut instr =
    if Set.contains r laOut then Some instr else None
  
  let doDCE (laMap: Map<int, LASet>) (nodeId: int) (instr: Instr) cfg: Instr Option =
    let instr = CFG.getInstr nodeId cfg
    let succs = CFG.getSuccs nodeId cfg
    // LA_out[n] = ⋃ LA_in[p] for all p ∈ succs(n)
    let succLAs = Map.filter (fun k v -> List.contains k succs) laMap 
    let laOut =
      if succLAs = Map.empty then Set.empty
      else Map.fold (fun acc k v -> Set.union acc v) Set.empty succLAs 
    match instr with
    | Set (r, _) | UnOp (r, _, _)
    | BinOp (r, _, _, _) | Load (r, _)
    | LocalAlloc (r, _) -> isContained r laOut instr
    | _ -> Some instr

  let run instrs =
    let cfg = CFG.make instrs
    let laMap = LivenessAnalysis.run cfg
    let (instrMap, _, _) = cfg
    let updatedInstrs = Map.fold (fun acc nodeId instr ->
        match doDCE laMap nodeId instr cfg with
        | Some i -> acc @ [i] | None -> acc ) [] instrMap
    if updatedInstrs = instrs then (false, instrs) else (true, updatedInstrs)

module Mem2Reg =

  let mutable REGSET = Set.empty
  let filterCandidates instr =
    match instr with
    | Set (r, Reg varReg) when r.StartsWith ("addr") -> 
      REGSET <- Set.filter (fun (rx, _) -> rx <> varReg) REGSET
    | _ -> ()

  let candidate (instr : Instr) =
    match instr with
    | LocalAlloc (r, _) ->
      if not (r.StartsWith ("arr")) then // array type is not considered
        let r' = Helper.createRegName()
        REGSET <- Set.add (r, r') REGSET
    | _ -> ()

  let optimize (instr : Instr) : Instr Option =
    match instr with
    | LocalAlloc (r, _) when (Set.exists (fun (rx, _) -> rx = r) REGSET) -> None
    | Load (r1, r2) when (Set.exists (fun (r, _) -> r = r2) REGSET) ->
      let r' = REGSET |> Set.toSeq |> Seq.tryFind (fun (rx, ry) -> rx = r2) |> Option.get |> snd
      Some (Set (r1, Reg r'))
    | Store (o, r) when (Set.exists (fun (rx, _) -> rx = r) REGSET) ->
      let r' = REGSET |> Set.toSeq |> Seq.tryFind (fun (rx, ry) -> rx = r) |> Option.get |> snd
      Some (Set (r', o))
    | _ -> Some instr
  
  let run instrs =
    let (instrMap, _, _) = CFG.make instrs
    let _ = Map.iter (fun nodeId instr -> candidate instr) instrMap
    let _ = Map.iter (fun nodeId instr -> filterCandidates instr) instrMap
    let updatedInstrs = Map.fold (fun acc nodeId instr ->
      match optimize instr with
      | Some i -> acc @ [i] | None -> acc ) [] instrMap
    if updatedInstrs = instrs then (false, instrs) else (true, updatedInstrs)

// You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =
  let mem2reg, instrs = Mem2Reg.run instrs
  let rec inner instrs =
    let cf, instrs = ConstantFolding.run instrs
    let cp, instrs = ConstantPropagation.run instrs
    let cp2, instrs = CopyPropagation.run instrs
    let cse, instrs = CommonSubexpressionElimination.run instrs
    let dce, instrs = DeadCodeElimination.run instrs
    let isOptimized =   dce || cse || cf || cp2 || cp 
    if isOptimized then inner instrs else instrs
  inner instrs

// Optimize input IR code into faster version.
let run (ir: IRCode) : IRCode =
  let (fname, args, instrs) = ir
  (fname, args, optimizeLoop instrs)