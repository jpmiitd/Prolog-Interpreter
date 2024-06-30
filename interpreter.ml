type variable = string
type symbl = string
type signature = (symbl * int) list
type term = V of variable | Num of int | Node of symbl * (term list)
type atom = A of symbl * (term list)
type head = H of atom
type body = B of atom list
type clause = F of head | R of head * body
type program = clause list
type goal = G of atom list
type substi = (variable * term) list

exception NOT_UNIFIABLE
exception NotFound
exception InvalidProgram
exception NotPossible

type symbol = string*int;;
type tree = V of string | C of { node: symbol ; children: tree list };;

let rec check_sig sigs =
  let rec checker sigs seen =
    match sigs with
    | [] -> true 
    | (label, arity) :: rest ->
        if arity < 0 then false 
        else if List.mem label seen then false
        else checker rest (label :: seen)
  in
  checker sigs []


                  
let found label arity sigs = 
  if List.mem (label,arity) sigs then true
  else false 
    
      

let rec wftree tree sigs =
  match tree with
  |V leaf -> true
  |C {node=(label,arity); children=children_list} ->
      if arity = (List.length children_list ) then
        if (found label arity sigs ) then 
          List.fold_left (fun acc child -> acc && wftree child sigs) true children_list
        else 
          false 
      else false
                  
let rec ht tree =
  match tree with
  |V _ -> 0
  |C {node=_; children = children_list} ->
      1+List.fold_left(
        fun acc child -> 
          let child_ht = ht child in
          if child_ht < acc then
            acc
          else
            child_ht
      ) 0 children_list
        
let rec size tree =
  match tree with
  |V _ -> 1
  |C {node=_; children = children_list} ->
      1+List.fold_left(
        fun acc child -> acc + (size child) 
      ) 0 children_list
        
        
let rec union acc vars_in_child =
  List.fold_left
    (fun acc var ->
       if not (List.mem var acc) then
         var :: acc (* Prepend to avoid list reversal *)
       else
         acc
    ) acc vars_in_child
  
let rec vars tree =
  match tree with
  |V x -> [x] 
  |C {node=_; children = children_list} ->
      List.fold_left(
        fun acc child -> union acc (vars child)
      ) [] children_list
        
let rec mirror tree =
  match tree with
  |V x -> V x 
  |C {node=symbol; children = children_list} ->
      let new_child = 
        List.fold_left(
          fun acc child -> List.cons (mirror child) acc
        ) [] children_list in
      C {node=symbol; children = new_child}
        
        
        
type substitution = S of (string*tree) list;; 

let is_valid_subst (S subst) = 
  let visited_vars = ref [] in
  List.fold_left(fun acc (var,_) -> 
      if List.mem var !visited_vars then
        ( visited_vars :=var :: !visited_vars;
          false)
      else
        ( 
          visited_vars :=var :: !visited_vars;
          true)
    ) true subst 
          
let rec subst (S subs) t = 
  match t with
  | V x -> (match List.assoc_opt x subs with
      | Some new_value -> new_value
      | None -> t)
  | C {node = symbol; children = children_list} ->
      let new_children_list = List.map (subst (S subs)) children_list in
      C {node = symbol; children = new_children_list}
    
let two_comp (S s1) (S s2) =
  let compos = List.map (fun (var, tree) -> (var, subst (S s2) tree)) s1 in 
  let merged = List.fold_left (fun acc (var, tree) -> 
      if List.mem_assoc var acc then
        acc
      else
        (var, tree) :: acc
    ) compos s2 in
  S merged
    
let rec composition compos_list =
  List.fold_left (fun acc subs -> two_comp acc subs) (S []) compos_list
  


let rec exists x y = match y with
    [] -> false
  | z::ys -> (x = z) || (exists x ys)
;;

let rec foldl f e l = match l with
    [] -> e
  | x::xs -> foldl f (f e x) xs
;;

let rec map f l = match l with
    [] -> []
  | x::xs -> (f x)::map f xs
;;

let rec combine l1 l2 = match l1 with
    [] -> []
  | x::xs -> (x, (List.hd l2))::combine xs (List.tl l2)
;;

let rec union l1 l2 = match l1 with
    [] -> l2
  | x::xs -> if (exists x l2) then union xs l2
             else x::(union xs l2)
;;

let rec checkProgram (prog:program): bool = match prog with
    [] -> true
  | (F(H(a)))::xs | (R(H(a), _))::xs -> match a with
          A("_eq", _) | A("_not_eq", _) | A("_cut", _)
        | A(">", _) | A("<", _)-> raise InvalidProgram
        | _ -> checkProgram xs
;;

let rec modifyTerm (i:int) (t:term): term = match t with
    V(v) -> V((string_of_int i) ^ v)
  | Node(s, l) -> Node(s, map (modifyTerm i) l)
  | _ -> t
;;

let rec modifyAtom (i:int) (a:atom): atom = match a with
  A(s, l) -> A(s, map (modifyTerm i) l)
;;

let rec modifyClause (cl:clause) (i:int): clause = match cl with
    F(H(a)) -> F(H(modifyAtom i a))
  | R(H(a), B(l)) -> R(H(modifyAtom i a), B(map (modifyAtom i) l))
;;

let rec modifyInitialProg (prog:program) (i:int): program = match prog with
    [] -> []
  | cl::ps -> (modifyClause cl i)::modifyInitialProg ps (i+1)
;;

let rec modifyProg2 (prog:program) (A(s, _): atom): program = match prog with
    [] -> []
  | cl::ps -> match cl with F(H(A(s', _))) | R(H(A(s', _)), _) ->
                if s = s' then (modifyClause cl 0)::modifyProg2 ps (A(s, []))
                else cl::modifyProg2 ps (A(s, []))
;;

let rec vars_term (t:term): variable list =
  match t with
      V(v) -> [v]
    | Node(s, l) -> foldl union [] (map vars_term l)
    | _ -> []
;;

let vars_atom (A(s, l): atom): variable list = vars_term (Node(s, l))
;;

let rec vars_goal (G(g): goal): variable list = foldl union [] (map vars_atom g)
;;

let rec subst (s:substi) (t:term): term =
  match t with
      Node(s', l) -> Node(s', map (subst s) l)
    | Num(_) -> t
    | V(x) -> match s with
                  [] -> t
                | s'::xs -> if fst s' = x then snd s' else subst xs t
;;

let rec subst_atom (s:substi) (A(s', l): atom): atom = A(s', map (subst s) l)
;;

let rec variableInTerm (v:variable) (t:term): bool =
  match t with
      V(x) -> x = v
    | Node(s, l) -> foldl (||) false (map (variableInTerm v) l)
    | _ -> false
;;

let compose (s1:substi) (s2:substi): substi =
  let f s x = (fst x, subst s (snd x)) in (map (f s2) s1) @ s2
;;

let rec mgu (t1:term) (t2:term): substi =
  match (t1, t2) with
      (V(x), V(y)) -> if x = y then []
                      else [(x, V(y))]
    | (V(x), Node(_, _)) -> if variableInTerm x t2 then raise NOT_UNIFIABLE
                            else [(x, t2)]
    | (Node(_, _), V(y)) -> if variableInTerm y t1 then raise NOT_UNIFIABLE
                            else [(y, t1)]
    | (Num(n1), Num(n2)) -> if n1 = n2 then [] else raise NOT_UNIFIABLE
    | (Num(n1), V(x)) -> [(x, t1)]
    | (V(x), Num(n2)) -> [(x, t2)] 
    | (Node(s1, l1), Node(s2, l2)) ->
        if s1 <> s2 || (List.length l1 <> List.length l2) then raise NOT_UNIFIABLE
        else
          let f s tt = compose s (mgu (subst s (fst tt)) (subst s (snd tt))) in
          foldl f [] (combine l1 l2)
    | _ -> raise NOT_UNIFIABLE
;;

let mgu_atom (A(s1, l1): atom) (A(s2, l2): atom): substi = mgu (Node(s1, l1)) (Node(s2, l2))
;;

let rec print_term_list (tl:term list) = match tl with
    [] -> Printf.printf ""
  | [t] -> print_term t
  | t::tls -> (
      print_term t;
      Printf.printf ",";
      print_term_list tls;
    )

and print_list_body (t:term) = match t with
    Node("_empty_list", []) -> Printf.printf ""
  | Node("_list", [t1; Node("_empty_list", [])]) -> print_term t1
  | Node("_list", [t1; t2]) -> (
      print_term t1;
      Printf.printf ",";
      print_list_body t2;
    )
  | _ -> raise NotPossible

and print_term (t:term) = match t with
    V(v) -> Printf.printf " %s " v
  | Node("_empty_list", []) -> Printf.printf " [] "
  | Node(s, []) -> Printf.printf " %s " s
  | Node("_list", _) -> (
      Printf.printf " [";
      print_list_body t;
      Printf.printf "] ";
    )
  | Node(s, l) -> (
      Printf.printf " %s ( " s;
      print_term_list l;
      Printf.printf " ) ";
    )
  | Num(n) -> Printf.printf " %d " n
;;

let rec getSolution (unif:substi) (vars:variable list) = match vars with
    [] -> []
  | v::vs ->
      let rec occurs l = match l with
          [] -> raise NotFound
        | x::xs -> if (fst x) = v then x
                    else occurs xs
      in
      try (occurs unif)::getSolution unif vs
      with NotFound -> getSolution unif vs
;;

let get1char () =
  let termio = Unix.tcgetattr Unix.stdin in
  let () = Unix.tcsetattr Unix.stdin Unix.TCSADRAIN
          { termio with Unix.c_icanon = false } in
  let res = input_char stdin in
  Unix.tcsetattr Unix.stdin Unix.TCSADRAIN termio;
  res

let rec printSolution (unif:substi) = match unif with
    [] -> Printf.printf "true. "
  | [(v, t)] -> (
      Printf.printf "%s =" v;
      print_term t;
    )
  | (v, t)::xs -> (
      Printf.printf "%s =" v;
      print_term t;
      Printf.printf ", ";
      printSolution xs;
    )
;;

let solve_atom_atom (a1:atom) (a2:atom) (unif:substi): substi =
  compose unif (mgu_atom (subst_atom unif a1) (subst_atom unif a2))
;;

let solve_term_term (t1:term) (t2:term) (unif:substi): substi =
  compose unif (mgu (subst unif t1) (subst unif t2))
;;

let rec simplify_term (t:term): term = match t with
    Num(_) -> t
  | Node("+", [t1; t2]) -> (
      match ((simplify_term t1), (simplify_term t2)) with
          (Num(n1), Num(n2)) -> Num(n1 + n2)
        | _ -> raise NOT_UNIFIABLE
    )
  | Node("-", [t1; t2]) -> (
      match ((simplify_term t1), (simplify_term t2)) with
          (Num(n1), Num(n2)) -> Num(n1 - n2)
        | _ -> raise NOT_UNIFIABLE
    )
  | Node("*", [t1; t2]) -> (
      match ((simplify_term t1), (simplify_term t2)) with
          (Num(n1), Num(n2)) -> Num(n1 * n2)
        | _ -> raise NOT_UNIFIABLE
    )
  | Node("/", [t1; t2]) -> (
      match ((simplify_term t1), (simplify_term t2)) with
          (Num(n1), Num(n2)) -> Num(n1 / n2)
        | _ -> raise NOT_UNIFIABLE
      )
  | _ -> t
;;

let eval (a:atom) (unif:substi): substi = match a with
    A("_eq", [t1; t2])
  | A("_not_eq", [t1; t2]) -> compose unif (mgu (simplify_term (subst unif t1)) (simplify_term (subst unif t2)))
  | A(">", [t1; t2]) -> (
        match (simplify_term (subst unif t1), simplify_term (subst unif t2)) with
            (Num(n1), Num(n2)) -> if n1 > n2 then unif else raise NOT_UNIFIABLE
          | _ -> raise NOT_UNIFIABLE
    )
  | A("<", [t1; t2]) -> (
      match (simplify_term (subst unif t1), simplify_term (subst unif t2)) with
          (Num(n1), Num(n2)) -> if n1 < n2 then unif else raise NOT_UNIFIABLE
        | _ -> raise NOT_UNIFIABLE
    )
  | _ -> unif
;;

let rec solve_goal (prog:program) (g:goal) (unif:substi) (vars:variable list): (bool * substi) =
  match g with
      G([]) -> (
        printSolution (getSolution unif vars);
        flush stdout;
        let choice = ref (get1char()) in
        while(!choice <> '.' && !choice <> ';') do
          Printf.printf "\nUnknown Action: %c \nAction? " (!choice);
          flush stdout;
          choice := get1char();
        done;
        Printf.printf "\n";
        if !choice = '.' then (true, [])
        else (false, [])
      )
    | G(a::gs) -> match a with
          A("_eq", _) | A(">", _) | A("<", _) -> (
            try solve_goal prog (G(gs)) (eval a unif) vars
            with NOT_UNIFIABLE -> (false, [])
          )
        | A("_not_eq", _) -> (
            try (false, eval a unif)
            with NOT_UNIFIABLE -> solve_goal prog (G(gs)) unif vars
          )
        | A("_cut", _) -> let _ = solve_goal prog (G(gs)) unif vars in (true, [])
        | _ ->
          let new_prog = modifyProg2 prog a in
          let rec iter prog' = match prog' with
              [] -> (false, [])
            | cl::ps -> match cl with
                F(H(a')) -> (
                  try
                    let u = (solve_atom_atom a' a unif) in
                    match (solve_goal new_prog (G(gs)) u vars) with
                        (true, u') -> (true, u')
                      | _ -> iter ps
                  with NOT_UNIFIABLE -> iter ps
                )
              | R(H(a'), B(al)) -> (
                  try
                    let u = (solve_atom_atom a' a unif) in
                    match (solve_goal new_prog (G(al @ gs)) u vars) with
                        (true, u') -> (true, u')
                      | _ -> iter ps
                  with NOT_UNIFIABLE -> iter ps
                )
        in iter prog
;;

let interpret_goal (prog:program) (g:goal) = solve_goal prog g [] (vars_goal g)
;;
