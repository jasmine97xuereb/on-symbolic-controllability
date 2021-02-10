open EnvFunctions
open EnvResources
open ExpressionEvaluator
open PrettyPrint
open SymFunctions
open SymResources
open SymEventGenerator
open SatFunction
open SymTransitions
open VisibilityLevel

let dep = ref DepTVars.empty
let tvar_vrd = ref TVars.empty
let tvar_brc = ref TVars.empty
let second_pass = ref false

(* get the set of verdicts that can be reached from the monitor-set ms *)
let rec get_rw (ms: Ast.Monitor.t list): VerdictSet.t = 
  let rec inner_get_rw (m: Ast.Monitor.t) (visited_tvar: Ast.TVar.t list): VerdictSet.t =
    match m with 
    | Ast.Monitor.Verdict(x) -> (
      match x.verd with 
      | ZERO -> VerdictSet.empty
      | _ -> VerdictSet.singleton x
    )
    | Ast.Monitor.TVar(x) -> ( 
      if List.mem x visited_tvar  
      then VerdictSet.empty
      else
        match TVars.find_opt x.tvar !mapTVar with
        | Some m -> inner_get_rw m (visited_tvar @ [x])
      | None -> VerdictSet.empty
    )
    | Ast.Monitor.ExpressionGuard(x) -> inner_get_rw x.consume visited_tvar
    | Ast.Monitor.QuantifiedGuard(x) -> inner_get_rw x.consume visited_tvar   
    | Ast.Monitor.Choice(x) -> VerdictSet.union (inner_get_rw x.left visited_tvar) (inner_get_rw x.right visited_tvar) 
    | Ast.Monitor.Conditional(x) -> VerdictSet.union (inner_get_rw x.if_true visited_tvar) (inner_get_rw x.if_false visited_tvar)
    | Ast.Monitor.Evaluate(x) -> inner_get_rw x.stmt visited_tvar
    | Ast.Monitor.Recurse(x) -> inner_get_rw x.consume visited_tvar
  in List.fold_right (fun x acc -> VerdictSet.union (inner_get_rw x []) acc) ms VerdictSet.empty 

(* checks whether the monitor-set contains visible verdicts *)
let rec vrd (ms: Ast.Monitor.t list): bool = 
  let rec inner_vrd (m: Ast.Monitor.t): bool = 
    match m with 
    | Ast.Monitor.Verdict(x) -> (
      match x.verd with 
      | ZERO -> false
      | _ -> true
    )
    | Ast.Monitor.TVar(x) -> (
      match TVars.find_opt x.tvar !mapTVar with
      | Some m -> inner_vrd m
      | None -> false
    )
    | Ast.Monitor.ExpressionGuard(x) -> x.verdict
    | Ast.Monitor.QuantifiedGuard(x) -> x.verdict    
    | Ast.Monitor.Choice(x) -> x.verdict
    | Ast.Monitor.Conditional(x) -> x.verdict
    | Ast.Monitor.Evaluate(x) -> x.verdict
    | Ast.Monitor.Recurse(x) -> x.verdict
  in match ms with 
  | [] -> false 
  | m::ms -> 
    if inner_vrd m 
    then true 
    else vrd ms

(* checks whether the monitor-set contains branching *)
let rec brc (ms: Ast.Monitor.t list): bool =
  let rec inner_brc (m: Ast.Monitor.t): bool =  
    match m with
    | Ast.Monitor.TVar(x) -> (
      match TVars.find_opt x.tvar !mapTVar with
      | Some m -> inner_brc m
      | None -> false
    )
    | Ast.Monitor.ExpressionGuard(x) -> x.brc
    | Ast.Monitor.QuantifiedGuard(x) -> x.brc    
    | Ast.Monitor.Choice(x) -> x.brc
    | Ast.Monitor.Conditional(x) -> x.brc
    | Ast.Monitor.Evaluate(x) -> x.brc
    | Ast.Monitor.Recurse(x) -> x.brc
    | _ -> false
  in match ms with 
  | [] -> false
  | m::ms ->
    if inner_brc m 
    then true 
    else brc ms

(* UNION-FIND ALGORITHM *)
(* creates an array where each element is mapped to itself *)
let create (n: int) (t: Ast.TVar.t list) =
  {
    tvar = t;
    parent = Array.init n (fun i -> i);
    rank = Array.make n 0
  }

(* UNION-FIND ALGORITHM *)
(* function that recursively follows the link until it finds the representative, i.e. an element mapped to itself *)
(* along the way it performs path compression *)
let rec find uf i = 
  let pi = uf.parent.(i) in 
  if pi == i then 
    i
  else begin 
    let ci = find uf pi in
    uf.parent.(i) <- ci; (* path compression *)
    ci
  end 

(* UNION-FIND ALGORITHM *)
(* function that finds out the two representatives of the given elements x and y and then links one to the other *)
let rec union ({ parent = p; rank = r; tvar = t } as uf) x y = 
  let cx = find uf x in 
  let cy = find uf y in 
  if cx != cy then begin
    if r.(cx) > r.(cy) then 
      p.(cy) <- cx
    else if r.(cx) < r.(cy) then 
      p.(cx) <- cy
    else begin 
      r.(cx) <- r.(cx) + 1;
      p.(cy) <- cx
    end
  end

(* given a tvar and a list, this function returns the position of the tvar in the list *)
let rec get_pos (x: Ast.TVar.t) (l: Ast.TVar.t list) (c: int): int = 
  match l with
  | [] -> 
    raise(Failure "Not Found")
  | hd::tl -> 
    if hd = x
    then c
    else get_pos x tl (c + 1)

(* l is a list of dependent tvars *)
(* this function updates the data structure uf accordingly *)
let rec update ({ parent = p; rank = r; tvar = t } as uf) (l: Ast.TVar.t list) = 
  match l with 
  | [] -> ()
  | x::[] -> ()
  | x::y::xs -> 
      let xpos = get_pos x t 0 
      in let ypos = get_pos y t 0 
      in union uf xpos ypos;
      update uf (y::xs)
    

(* function to determine whether each submonitor contains a syntactic verdict or branching *)
(* contains_v_b returns a triple *)
(* the first element is whether the monitor syntactically contains a verdict *)
(* the second element is wether the monitor branches internally or externally *)
(* the third element is the continuation of the monitor with these fields updated *) 
(* once finished, empty the map *)
(* return the new monitor with the fields 'verdict' and 'brc' filled *)

let rec populate (m: Ast.Monitor.t): Ast.Monitor.t = 
  let rec contains_v_b (m: Ast.Monitor.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    match m with 
      | Ast.Monitor.Verdict(x) -> contains_v_b_verdict x 
      | Ast.Monitor.TVar(x) -> contains_v_b_tvar x tvars_checked 
      | Ast.Monitor.ExpressionGuard(x) -> contains_v_b_exp_guard x tvars_checked 
      | Ast.Monitor.QuantifiedGuard(x) -> contains_v_b_quant_guard x tvars_checked 
      | Ast.Monitor.Choice(x) -> contains_v_b_choice x tvars_checked 
      | Ast.Monitor.Conditional(x) -> contains_v_b_conditional x tvars_checked 
      | Ast.Monitor.Evaluate(x) -> contains_v_b_evaluate x tvars_checked 
      | Ast.Monitor.Recurse(x) -> contains_v_b_recurse x tvars_checked 

  and contains_v_b_verdict (m: Ast.Monitor.Verdict.t): (bool * bool * Ast.Monitor.t ) = 
    match m.verd with
    | ONE -> (true, false, add_verdict 1)
    | TWO -> (true, false, add_verdict 2)
    | _ -> (false, false, add_verdict 0)

  and get_tvar (x:Ast.TVar.t) = 
    x.tvar
     
  and contains_v_b_tvar (x: Ast.TVar.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    if !second_pass == false
    then (
      dep := DepTVars.add ([x] @ tvars_checked) !dep;
      (false, false, create_tvar x.tvar)
    )
    else(
      let verdict = 
        try 
          let dependent_list = (DepTVars.find_first (fun lst -> List.mem x lst) !dep)
          in List.exists (fun t -> TVars.find (get_tvar t) !tvar_vrd) dependent_list        
        with Not_found -> false
      in 
      let branch = 
        try 
          let dependent_list = (DepTVars.find_first (fun lst -> List.mem x lst) !dep)
          in List.exists (fun t -> TVars.find (get_tvar t) !tvar_brc) dependent_list        
        with Not_found -> false
      in 
      (verdict, branch, create_tvar x.tvar)  
    )  

  and contains_v_b_recurse (m: Ast.Monitor.Recurse.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    mapTVar := TVars.add m.monvar.tvar m.consume !mapTVar;
    let (v, b, consume) = contains_v_b m.consume [m.monvar] in 
    tvar_vrd := TVars.add m.monvar.tvar v !tvar_vrd;
    tvar_brc := TVars.add m.monvar.tvar b !tvar_brc;
    (v, b, create_recurse_mon m.monvar consume v b)

  and contains_v_b_exp_guard (m: Ast.Monitor.ExpressionGuard.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    let (v, b, consume) = contains_v_b m.consume tvars_checked in
      (v, b, create_exp_guard_mon m.label m.payload consume v b)

  and contains_v_b_quant_guard (m: Ast.Monitor.QuantifiedGuard.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    let (v, b, consume) = contains_v_b m.consume tvars_checked in
      (v, b, create_quant_guard_mon m.label m.payload consume v b)

  and contains_v_b_choice (m: Ast.Monitor.Choice.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    let (v1, b1, lt) = contains_v_b m.left tvars_checked in
      let (v2, b2, rt) = contains_v_b m.right tvars_checked in
        let v = v1 || v2 in
          let b = b1 || b2 in 
            (v, b, create_choice_mon lt rt v b)

  and contains_v_b_conditional (m: Ast.Monitor.Conditional.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    let (v1, b1, tt) = contains_v_b m.if_true tvars_checked in
      let (v2, b2, ff) = contains_v_b m.if_false tvars_checked in
        let v = v1 || v2 in
          (v, true, create_conditional_mon m.condition tt ff v true)

  and contains_v_b_evaluate (m: Ast.Monitor.Evaluate.t) (tvars_checked: Ast.TVar.t list): (bool * bool * Ast.Monitor.t) = 
    let (v, b, stmt) = contains_v_b m.stmt tvars_checked in
      (v, b, create_evaluate_mon m.var m.subst stmt v b)

  in let (mv, mb, m) = (contains_v_b m [ ])
  in 
  if DepTVars.is_empty !dep
  then (
    mapTVar := TVars.empty;
    m
  )
  else (
    (* print_endline("contains rec monitors, second pass is necessary"); *)
    second_pass := true;
    (* print_endline ("truth is now " ^ string_of_bool !second_pass); *)
      
    let tvar = List.map (fun x -> fst x) (TVars.bindings !mapTVar) 
    in 
    (* print_endline("our tvars: "); *)
    List.iter (fun x -> print_string (x ^ " ")) tvar;
    let len = List.length tvar
    in let uf = create len (List.map (fun x -> {Ast.TVar.tvar = x}) tvar)
    in 
    (* print_endline("\nafter update it becomes"); *)
    Array.iter (fun x -> print_string ((string_of_int x) ^ " ")) uf.parent; 

    DepTVars.iter (fun x -> update uf x) !dep;

    (* print_endline("\nafter update it becomes"); *)
    Array.iter (fun x -> print_string ((string_of_int x) ^ " ")) uf.parent;

    print_newline();

    let p = Array.make len [ ] in 
    let rec part (pos: int) = 
      if pos < len 
      then (
        let temp = uf.parent.(pos) in
        (* print_endline("the parent is " ^ string_of_int temp); *)
        p.(temp) <- p.(temp) @ [List.nth uf.tvar pos];
        part (pos + 1)
      )
    in part 0;
    dep := DepTVars.remove [ ] (DepTVars.of_list (Array.to_list p));
    
    let rec print_tvars (x: Ast.TVar.t list) = 
      match x with
      | [] -> ()
      | t::ts -> print_string(t.tvar ^ " " ); print_tvars ts
    in 
    
    (* DepTVars.iter (fun x -> print_string ("[ "); print_tvars x; print_endline ("]");) !dep; *)
    let (mv, mb, m) = contains_v_b m [ ]
    in mapTVar := TVars.empty;
    m
  )

let rec reach_osaft (cm: cm) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t) (relation: cm list) (unseen_cms: (CMSet.t * cm) Queue.t) =
  let rec new_monitors mon_list = 
    match mon_list with
    | [] -> []
    | REDUCED(x)::m2 -> [x] @ (new_monitors m2)
    | ERROR(x)::m2 -> [add_verdict 0] @ (new_monitors m2)
  
  in let rec saft_aux (m: Ast.Monitor.t list) (res: cm) (saft_cms: cm list) =
    (match m with
    | [] -> 
      let optimized_res = ((cns (fst res) (snd res)), (snd res)) in
      optimized_res
    | ms::mss -> (
      let resulting_mons = sym_reduce ms (fst cm) evt c 
      (* use add_monitors_not_in_list to make sure not to add duplicates *)
      in saft_aux mss ([c], (add_monitors_not_in_list (snd res) (new_monitors resulting_mons))) saft_cms               
    ))
  in saft_aux (snd cm) ([],[]) []

(*get the next tuple that is not already in the relation*)
let rec get_next_unseen_r (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) (unseen_cms: (CMSet.t * cm) Queue.t): (CMSet.t * cm) = 
  if (Queue.is_empty unseen_cms) 
  then (CMSet.empty ,([],[])) 
  else(
    let (p, next_m) = Queue.pop unseen_cms in
    if tuple_exists_in_relation next_m relation 
    then get_next_unseen_r relation unseen_cms
    else (p, next_m)
  )  

(* print all the cms in set s *)
let print_cmset (s: CMSet.t) =
  CMSet.iter (fun x -> print_reach("<" ^ pretty_print_evt_list (fst x) ^ ", "^ pretty_print_monitor_list_string (snd x) ^ ">")) s
     
(* prints all the cms and the verdict-set they are reachbale wrt for each tuple in the list *)
let rec print_path (ll: (VerdictSet.t * CMSet.t) list) = 
  match ll with 
  | [] -> ()
  | l::ls -> 
    print_reach("All these monitors are reachable wrt " ^ pretty_print_verdict_list (VerdictSet.elements (fst l)));
    print_cmset (snd l);
    print_path ls

(* adds <rw_add, p_add> to result *)
(* if result has any entries with the same values as rw_add or p_add, they are merged accordingly *)
let rec add_rw_path (result: (VerdictSet.t * CMSet.t) list) (rw_add: VerdictSet.t) (p_add: CMSet.t): (VerdictSet.t * CMSet.t) list = 
  let rec inner_add (result: (VerdictSet.t * CMSet.t) list) (rw_add: VerdictSet.t) (p_add: CMSet.t): (VerdictSet.t * CMSet.t) list = 
    match result with 
    | [] -> [rw_add, p_add]
    | l::ls -> 
      let rw = fst l in 
      let p = snd l in
      
      (* if the verdict sets are equal then merge sets *)
      (* otherwise check if there are any common elements *)
      if VerdictSet.equal rw rw_add
      then inner_add ls rw (CMSet.union p_add p) 
      else (
        (* if p inter p_add = empty then add in ls *)
        let common = CMSet.inter p p_add in         
        if CMSet.is_empty common 
        then 
          [l] @ (inner_add ls rw_add p_add)
        else (
          (* add those that are in p but not in p_add (with verdict rw) *)
          let r1 = inner_add ls rw (CMSet.diff p common)
          (* add those that are in both p and p_add (with verdicts rw union rw_add)  *)
          in let r2 = inner_add r1 (VerdictSet.union rw_add rw) common
          (* add those that are in p_add but not in p (with verdicts rw_add) *)
          in let r3 = inner_add r2 rw_add (CMSet.diff p_add common)
          in r3
        )
      )

    (* remove any empty tuples from result *)
    in let filtered_result = List.filter (fun x -> not (CMSet.is_empty (snd x))) result in 
    inner_add filtered_result rw_add p_add 