module DFA

open IR
open CFG

type RDSet = Set<Instr>
type AESet = Set<Instr>
type LASet = Set<Register>

module RDAnalysis =
  // Write your logic to compute reaching definition set for each CFG node.

  let mutable RDMap = Map.empty

  let isDefined instr =
    match instr with
    | Set _ | UnOp _ | BinOp _ | Load _| LocalAlloc _ -> true
    | _ -> false

  let DefinedReg instr =
    match instr with
    | Set (r, _) | UnOp (r, _, _)
    | BinOp (r, _, _, _) | Load (r, _) 
    | LocalAlloc (r, _) -> r
    | _ -> failwith "Invalid instruction"

  // Transfer function: RD_out[n] = GEN[n] ∪ (RD_in[n] - KILL[n])
  let transferfunc (instr: Instr) (rdIn: RDSet): RDSet =
    if isDefined instr then
      let definedReg = DefinedReg instr
      let filter instr =
        match instr with
        | Set (r, _) | UnOp (r, _, _)
        | BinOp (r, _, _, _) | Load (r, _)
        | LocalAlloc (r, _) -> if r = definedReg then false else true
        | _ -> true
      let rdOut = Set.filter filter rdIn
      Set.add instr rdOut
    else rdIn

  let rec computeRD (cfg: CFG): Map<int,RDSet> =
    let (instrMap, succMap, predMap) = cfg
    let rec loop (rdMap: Map<int,RDSet>) (worklist: int list) : Map<int,RDSet> =
      match worklist with
      | [] -> rdMap
      | nodeID :: rest ->
        let instr = CFG.getInstr nodeID cfg
        let preds = CFG.getPreds nodeID cfg
        // RD_in[n] = ⋃ RD_out[p] for all p ∈ pred(n)
        let predRDs = Map.filter (fun k v -> List.contains k preds) rdMap
        let rdIn = 
          if predRDs = Map.empty then Set.empty
          else Map.fold (fun acc k v -> Set.union acc v) Set.empty predRDs
        // RD_out[n] = GEN[n] ∪ (RD_in[n] - KILL[n])   
        let rdOut = transferfunc instr rdIn
        let rdMap = Map.add nodeID rdOut rdMap
        // Add all successors of n to the worklist
        loop rdMap rest 
    // for each node n, RD_in[n] = ∅
    let worklist = CFG.getAllNodes cfg
    let prevRDMap = RDMap
    RDMap <- loop prevRDMap worklist
    if prevRDMap = RDMap then RDMap else computeRD cfg

  // Compute reaching definition set for each node in the CFG.
  let run (cfg: CFG) : Map<int,RDSet> =
    let (instrMap, _, _) = cfg
    RDMap <- Map.fold (fun acc nodeId instr -> Map.add nodeId Set.empty acc) Map.empty instrMap
    computeRD cfg

module AEAnalysis =

  let mutable AEMap = Map.empty
  let mutable AllInstrSet = Set.empty
  let findReginOperand (o: Operand) : Register Set =
    match o with
    | Reg r -> Set.singleton r
    | _ -> Set.empty
  
  let definedRegister instr =
    match instr with
    | Set (r, o) -> 
      if (findReginOperand o) <> Set.empty then Set.singleton r
      else Set.empty
    | UnOp (r, _, _) -> Set.singleton r
    | BinOp (r, _, _, _) -> Set.singleton r
    | _ -> Set.empty

  let regsinInstr instr =
    match instr with
    | Set (r, o) -> Set.union (findReginOperand o) (Set.singleton r)
    | UnOp (r, _, o) -> Set.union (findReginOperand o) (Set.singleton r)
    | BinOp (r, _, o1, o2) -> Set.union (Set.union (findReginOperand o1) (findReginOperand o2)) (Set.singleton r)
    //TODO: check if store is correct
    // | Store (o, r) -> Set.union (findReginOperand o) (Set.singleton r)
    | Load (r1, r2) -> (Set.singleton r1)
    | _ -> Set.empty
  
  let usedInBothSide instr =
    match instr with
    | Set (r, o) -> Set.intersect (findReginOperand o) (Set.singleton r)
    | UnOp (r, _, o) -> Set.intersect (findReginOperand o) (Set.singleton r)
    | BinOp (r, _, o1, o2) -> Set.intersect(Set.union (findReginOperand o1) (findReginOperand o2)) (Set.singleton r)
    | _ -> Set.empty
  
  let isAEDefined instr =
    match instr with
    | Set _ | UnOp _ | BinOp _ -> true
    | _ -> false
  
  let isAlloc instr =
    match instr with
    | LocalAlloc _ -> true | _ -> false
  
  let isStore instr =
    match instr with
    | Store _ -> true | _ -> false

  let isLoad instr =
    match instr with
    | Load _ -> true | _ -> false

  // 1. Transfer function: AEout[n] = AEin[n] - {a contains %t} + {e in %t} if instr = (%t = e)
  let transferfunc1 (instr: Instr) (aeIn: AESet): AESet =
    // %t which is used in instr (%t = e)
    let usedRegs = definedRegister instr
    // if ae use registers that are used in instr, then erase all ae that contains used registers
    let filter1 usedRegs (ae:Instr) =
      let aeRegs = regsinInstr ae
      if (Set.intersect usedRegs aeRegs) = Set.empty then true else false
    // add {e in %t} if %t = e, where e is a register or binary/unary operation
    // **Corner case: if instr use %t in both sides, then erase all ae that contains %t //TODO
    if isAEDefined instr then 
      if (usedInBothSide instr) = Set.empty then Set.add instr (Set.filter (filter1 usedRegs) aeIn) 
      else Set.filter (filter1 usedRegs) aeIn
    else aeIn 
  
  // 2. f(AE, i) = AE - {a contains %r} if %r = alloc(n)
  let transferfunc2 (instr: Instr) (aeIn: AESet) : AESet =
    let usedRegs = if isAlloc instr then Set.singleton (match instr with | LocalAlloc (r, _) -> r | _ -> failwith "Invalid instruction") 
                    else Set.empty
    let filter usedRegs (ae:Instr) =
      let aeRegs = regsinInstr ae
      if (Set.intersect usedRegs aeRegs) = Set.empty then true else false
    Set.filter (filter usedRegs) aeIn
  

  // 3. f(AE, i) = AE - {ae contains %r)} if instr = load %r, %t
  let transferfunc3 (instr: Instr) (aeIn: AESet) : AESet =
    match instr with
    | Store (o, r) ->
      let usedRegs = Set.singleton r
      let filter usedRegs (ae:Instr) =
        match ae with
        | Store _ | Load _ -> false
        | _ -> true
      Set.filter (filter usedRegs) aeIn
    | Load (r1, r2) ->
      let usedRegs = Set.singleton r1
      let filter usedRegs (ae:Instr) =
        let aeRegs = regsinInstr ae
        if (Set.intersect usedRegs aeRegs) = Set.empty then true 
        else false
      let aein' = Set.filter (filter usedRegs) aeIn
      Set.add instr aein'
    | _ -> aeIn

  let rec computeAE (cfg: CFG) : Map<int,AESet> =
    let (instrMap, succMap, predMap) = cfg
    let rec loop (aeMap: Map<int,AESet>) (worklist: int list) : Map<int,AESet> =
      match worklist with
      | [] -> aeMap
      | nodeID :: rest ->
        let instr = CFG.getInstr nodeID cfg
        let preds = CFG.getPreds nodeID cfg
        // AEin[n] = ⋂ AEout[p] for all p ∈ pred(n)
        let predAEs = Map.filter (fun k v -> List.contains k preds) aeMap
        let aeIn = 
          if predAEs = Map.empty then Set.empty
          else
            Map.fold (fun acc k v -> Set.intersect acc v) AllInstrSet predAEs
        // 1. Transfer function: AEout[n] = AEin[n] ∪ {e in %t} - {a contains %t}
        // 2. f(AE, i) = AE - {a contains %r} if %r = alloc(n)
        // 3. f(AE, i) = AE - {ae contains (load %r)}
        let aeOut = transferfunc1 instr aeIn |> transferfunc2 instr |> transferfunc3 instr
        let aeMap = Map.add nodeID aeOut aeMap
        loop aeMap rest
    let prevAEMap = AEMap
    let worklist = CFG.getAllNodes cfg
    AEMap <- loop prevAEMap worklist
    if prevAEMap = AEMap then AEMap else computeAE cfg

  // Compute available expression set for each node in the CFG.
  let run (cfg: CFG) : Map<int,AESet> =
    let (instrMap, _, _) = cfg
    let instrList = Map.toList instrMap
    AllInstrSet <- List.fold (fun acc (_, instr) -> Set.add instr acc) Set.empty instrList
    AEMap <- Map.fold (fun acc nodeId instr -> Map.add nodeId  AllInstrSet acc) Map.empty instrMap
    computeAE cfg

module LivenessAnalysis =

  let mutable LAMap = Map.empty

  let findReginOperand (o: Operand) : Register Set =
    match o with
    | Reg r -> Set.singleton r
    | _ -> Set.empty

  let DefinedReg instr =
    match instr with
    | Set (r, _) | UnOp (r, _, _)
    | BinOp (r, _, _, _) | Load (r, _)
    | LocalAlloc (r, _) -> r
    | _ -> ""

  let usedRegsinInstr instr =
    match instr with
    | Set (_ , o) | UnOp (_ , _, o) | GotoIf (o, _)
    | GotoIfNot (o, _) | Ret o -> (findReginOperand o)
    | BinOp (r, _, o1, o2) -> (Set.union (findReginOperand o1) (findReginOperand o2))
    | Load (r1, r2) -> (Set.singleton r2)
    | Store (o, r) -> Set.union (findReginOperand o) (Set.singleton r)
    | _ -> Set.empty

  // Transfer function: LA_in[n] = LA_out[n] - definedReg + usedReg
  let transferfunc (instr: Instr) (laOut: LASet) =
    let definedReg = DefinedReg instr
    let usedRegs = usedRegsinInstr instr
    let laOut = Set.filter (fun r -> r <> definedReg) laOut
    Set.union usedRegs laOut

  let rec computeLA (cfg: CFG): Map<int,LASet> =
    let (instrMap, succMap, predMap) = cfg
    let rec loop (laMap: Map<int,LASet>) (worklist: int list) : Map<int,LASet> =
      match worklist with
      | [] -> laMap
      | nodeID :: rest ->
        let instr = CFG.getInstr nodeID cfg
        let succs = CFG.getSuccs nodeID cfg
        // LA_out[n] = ⋃ LA_in[p] for all p ∈ succs(n)
        let succLAs = Map.filter (fun k v -> List.contains k succs) laMap 
        let laOut =
          if succLAs = Map.empty then Set.empty
          else Map.fold (fun acc k v -> Set.union acc v) Set.empty succLAs 
        let lain = transferfunc instr laOut
        let laMap = Map.add nodeID lain laMap
        loop laMap rest
    // for each node n, RD_in[n] = ∅ (reverse order)
    let worklist = CFG.getAllNodes cfg |> List.rev
    let prevLAMap = LAMap
    let newLAMap = loop prevLAMap worklist
    if prevLAMap = newLAMap then newLAMap
    else 
      LAMap <- newLAMap
      computeLA cfg

  // Compute reaching definition set for each node in the CFG.
  let run (cfg: CFG) : Map<int,LASet> =
    let (instrMap, _, _) = cfg
    LAMap <- Map.fold (fun acc nodeId instr -> Map.add nodeId Set.empty acc) Map.empty instrMap
    computeLA cfg
