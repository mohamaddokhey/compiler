(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;


type var = 
  | VarFree of string
  | VarParam of string * int      
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;


  
  let rec expr'_eq e1 e2 =
    match e1, e2 with
    | Const' Void, Const' Void -> true
    | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2

    | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
    | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
    | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
    | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                              (expr'_eq th1 th2) &&
                                                (expr'_eq el1 el2)
    | (Seq'(l1), Seq'(l2)
    | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
    | (Set'(var1, val1), Set'(var2, val2)
    | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                               (expr'_eq val1 val2)
    | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
    | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
       (String.equal var1 var2) &&
         (List.for_all2 String.equal vars1 vars2) &&
           (expr'_eq body1 body2)
    | Applic'(e1, args1), Applic'(e2, args2)
    | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
     (expr'_eq e1 e2) &&
       (List.for_all2 expr'_eq args1 args2)

    | Box'(var1), Box'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
    | BoxGet'(var1), BoxGet'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
    | BoxSet'(var1,expr1), BoxSet'(var2,expr2) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
    (expr'_eq (expr1) (expr2))

    | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_not_yet_implemented;;


module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'

end;;

module Semantics : SEMANTICS = struct

(* ---------------------------------------------HELP FUNCTIONS ---------------------------------------*)
let rec iterate_bound e layer ls = 
  match ls with
  |[]-> Var'(VarFree e)
  |head::tail -> let flag=(List.mem_assoc e head) in 
   (match flag with 
    |false->(iterate_bound e (layer+1) tail)
    |_-> Var'(VarBound(e,layer,List.assoc e head))
   ) 
;;
(*returns a list with indexes to the params lst of the lambdaa *)
let rec iter low high= 
    match low=high with 
    |false-> low::(iter(low+1)high)
    |_-> [];;

let make_pair=(fun one two->(one,two));;

let makePairsLstWithMinors ls=
  List.map2 make_pair ls (iter 0 (List.length ls));; (*loop from zero to list length*)

let get_last lst=
let len= ((List.length lst)-1)in
let last=(List.nth lst len)in
last;;

let get_with_out_last lst=
  let lst1=(List.rev lst)in
  let lst2=(List.tl lst1)in
  (List.rev lst2);;

(*************************************BOX FUNCTIONSS*********************************************)
(****************READS***************)
let count_appears1 = 
  let layer_count =ref 1 in 
  fun ()->(layer_count:=!layer_count+1);(* !layer_count returns the content of counter*)
          !layer_count;;

  let count_appears2 = 
   let layer_count =ref 1 in 
   fun ()->(layer_count:=!layer_count+1);
          !layer_count ;;


  let rec read_finder var body idlst  = 
  let mapper=(fun(x)->read_finder var x idlst)in
  match body with
  |Var'(VarBound(varname,_,_))|Var'(VarParam(varname,_))-> 
        (match varname = var with
          |false-> [] 
          |_->[idlst] 
        )

  |If'(test,dit,dif)->(mapper test)@(mapper dit)@(mapper dif)
  
  |Seq' exprs -> 
      let idlsts=(List.map mapper exprs)in
      (List.flatten idlsts)
    
  |Set' (Var'(_),expr)|BoxSet'(_,expr)-> (mapper expr)

  |Def'(variable,value)-> 
      (mapper variable)@
      (mapper value)
  
  |Or' exprs->  
       let idlsts=(List.map mapper exprs)in
       (List.flatten idlsts)
  
  |LambdaSimple'(params,expr)-> 
      let bound_or_not=(List.mem var params)in
      (match bound_or_not with 
      |false->let current_id = count_appears1() in
      (read_finder var expr(current_id::idlst))
      |_ ->[]
      )

  |LambdaOpt'(params,var1,expr)-> 
      let allparams=var1::params in
      let bound_or_not = (List.mem var allparams)in
      (match bound_or_not with 
      |false->let current_id = count_appears1() in 
      (read_finder var expr(current_id::idlst))
      |_ ->[]
      )

  |Applic' (func, expr_ls)|ApplicTP' (func, expr_ls) -> 
    let idlsts=(List.map mapper expr_ls)in
    (mapper func)@ 
    (List.map List.flatten idlsts)
  
  |_->[] ;;

let find_read_ids var body =read_finder var body[0];;
(**********************WRITES*************************)
  let rec write_finder var body idlst= 
  let mapper=(fun(x)->write_finder var x idlst)in
  match body with

  |If'(test,dit,dif)-> (mapper test)@(mapper dit)@(mapper dif)
  
  |Seq' exprs-> 
      let idlsts=(List.map mapper exprs)in
      (List.flatten idlsts)
    
  |Set'(Var'(VarBound(v,_,_)),expr)|Set'(Var'(VarParam(v,_)),expr)->
      (match var = v with 
       |false->(mapper expr) 
       |_->[idlst]@(mapper expr) 
      )

  |Set'(Var'(VarFree(_)),expr)|BoxSet'(_,expr)->(mapper expr) 

  |Def'(variable,value)-> (mapper variable)@(mapper value)
  
  |Or' exprs->  
       let idlsts=(List.map mapper exprs)in
       (List.flatten idlsts)
    
  |LambdaSimple'(params,expr)-> 
      let in_param_lst=(List.mem var params)in
      (match in_param_lst with 
      |false->let current_id = count_appears2() in
      (write_finder var expr(current_id::idlst))
      |_->[]
      )

  |LambdaOpt'(params,var1,expr)-> 
      let allparams= var1::params in
      let in_param_lst =(List.mem var allparams)in
      (match in_param_lst with 
      |false->let current_id = count_appears2() in 
      (write_finder var expr(current_id::idlst))
      |_->[]
      )

  |Applic'(func, expr_ls)|ApplicTP'(func, expr_ls) -> 
    let idlsts=(List.map mapper expr_ls)in
    (mapper func)@  
    (List.map List.flatten idlsts)
  
  | _->[];;
let find_write_ids var body =write_finder var body[0];;

let rec av_kedmon var1 var2 =
  if (var1!=[] && var2!=[]) 
  then (let ans=(List.hd var1 = List.hd var2)in
  (
    match ans with
    |false->(av_kedmon(List.tl var1)(List.tl var2))
    |_->false
  ))                                                   
  else true ;; 

let check_match (var1,var2) =
    let rev_var1_with_out_first=(List.tl(List.rev var1)) 
    and rev_var2_with_out_first=(List.tl(List.rev var2))in 
  let ans2=(av_kedmon rev_var1_with_out_first rev_var2_with_out_first)in 
  (List.hd var1 != List.hd var2)&&ans2 ;;

let nt_empty_lst exp = exp!=[];; 

let need_box var bdy = 
  let rd =find_read_ids var bdy in 
        let rd_filtered=(List.filter(fun(exp)->nt_empty_lst(exp))rd)in

  let wr =find_write_ids var bdy in 
        let wr_filtered=(List.filter(fun(exp)->nt_empty_lst(exp))wr)in

  let matcher=(fun(a)->List.map(fun(b)->(a,b))wr_filtered)in
  let match_ls=(List.concat(List.map matcher rd_filtered))in
        (match ormap check_match match_ls with 
        |false-> "not a var name"
        |_-> var 
        );;
              
let remove_me exp =exp != "not a var name";;

let filter_lambda_params paramsls bdy =
  let need_box_param_lst =(List.map(fun(a)->(need_box a bdy))paramsls)in 
       (List.filter remove_me need_box_param_lst);; 

 let rec write_params box_params params_index = 
  (match params_index with 
  |[]->params_index
  |_->(let head_pair=(List.hd params_index)in 
       let tail=(List.tl params_index)in 
       let (hd1,hd2)=head_pair in
       (match   not(List.mem hd1 box_params) with
       |false-> ((hd1,hd2)::(write_params box_params tail))
       |_-> (write_params box_params tail) 
      ))
  );;   

let attach_minors_to_params paramsls= 
    let len= (List.length paramsls) in 
    let rec continue_attach len n = 
      (match (n =len) with  
      |false->(n::continue_attach len (n+1))
      |_-> []) 
      in continue_attach len 0;;

let attach_params_to_minors paramsls  = 
     let minorsls = attach_minors_to_params paramsls in 
        (List.map2 make_pair paramsls minorsls);; 

let set_box_to_varParam (var,minor)= 
          Set'(Var'(VarParam(var,minor)),Box'(VarParam(var,minor)));; 

let new_body paramsls params_need_box = 
  let pairs_params_minors = (attach_params_to_minors paramsls) in 
      let params_index_write = (write_params params_need_box pairs_params_minors) in 
          (List.map (fun(a,b) -> set_box_to_varParam (a,b)) params_index_write) 
    ;; 

(* ----------------------starting the implementation of the functions------------------*)

(*********************************************FIRST FUNCTION***************************************************)
let annotate_lexical_addresses e = 
let rec rec_lexical pvar_ls bvar_ls e =  
match e with 
|Const expr-> Const' expr

|Var expr->

if(List.mem_assoc expr pvar_ls) 
            then Var'(VarParam (expr ,(List.assoc expr pvar_ls ))) 
            else(iterate_bound expr 0 bvar_ls)

|If(test,dit,dif)-> let test=(rec_lexical pvar_ls bvar_ls test)in 
                    let dit =(rec_lexical pvar_ls bvar_ls dit)in
                    let dif =(rec_lexical pvar_ls bvar_ls dif)in
                    If'(test,dit,dif)

|Seq expr_ls-> Seq'(List.map (rec_lexical pvar_ls bvar_ls ) expr_ls)

|Set (expr1,expr2) -> Set'((rec_lexical pvar_ls bvar_ls expr1 ),
                           (rec_lexical pvar_ls bvar_ls expr2))

|Def (expr1,expr2) -> Def'((rec_lexical pvar_ls bvar_ls expr1 ),
                           (rec_lexical pvar_ls bvar_ls expr2)) 

|Or expr_ls -> Or' (List.map (rec_lexical pvar_ls bvar_ls ) expr_ls)

|LambdaSimple (lst,expr)-> 
    let pairs_Lst=makePairsLstWithMinors(lst) in 
    LambdaSimple'(lst,(rec_lexical pairs_Lst (pvar_ls::bvar_ls) expr))

|LambdaOpt (lst,str,expr)-> 
    let lst1=(lst@[str]) in 
    let pairs_Lst=makePairsLstWithMinors(lst1) in 
    LambdaOpt'(lst,str,(rec_lexical pairs_Lst (pvar_ls::bvar_ls)expr))

|Applic(func,expr_ls)-> Applic'((rec_lexical pvar_ls bvar_ls func)
                                ,List.map (rec_lexical pvar_ls bvar_ls)expr_ls) 

in rec_lexical [] [] e ;;
(*********************************************SECOND FUNCTION***************************************************)
let annotate_tail_calls e =
  (*go on each form in expr' and call this procedure on each of the sub-exp*)
    let rec rec_tail_calls in_tp e = (*to indocate weather the current position in tail posisition *) 
    match e with 
     |(Const' x)->e 
     |(Var' x)  ->e
     (*BOX*)
     |If'(test,dit,dif)->If'(rec_tail_calls false test,
                             rec_tail_calls in_tp dit,
                             rec_tail_calls in_tp dif)

     |(Seq' ls) -> let last_expr=get_last ls in 
                   let last_in_arr = [(rec_tail_calls in_tp last_expr)]in 
                   let without_last= (get_with_out_last ls) in
                   Seq' ((List.map (rec_tail_calls false) without_last) @ last_in_arr)

     |Set'(expr_tag1,expr_tag2) -> Set'(expr_tag1, rec_tail_calls false expr_tag2)

     |Def'(expr_tag1,expr_tag2) -> Def'(expr_tag1, rec_tail_calls false expr_tag2)

     |(Or' ls)->let last_expr=(get_last ls )in 
                                 let last_in_arr =[(rec_tail_calls in_tp last_expr)]in 
                                 let without_last=(get_with_out_last ls)in
                                 Or'((List.map (rec_tail_calls false) without_last) @ last_in_arr)

     |LambdaSimple'(lst,expr_tag)->LambdaSimple'(lst,(rec_tail_calls true expr_tag))

     |LambdaOpt'(ls,str,expr_tag)-> LambdaOpt'(ls,str,(rec_tail_calls true expr_tag))

     |Applic'(expr_tag,expr_tag_lst)-> 
                   let tail_expr_tag= (rec_tail_calls false expr_tag ) in
                   let tail_expr_tag_lst = (List.map (rec_tail_calls false ) expr_tag_lst) in 
                   (match in_tp with
                   |false->  Applic'(tail_expr_tag,tail_expr_tag_lst)
                   |_-> ApplicTP'(tail_expr_tag,tail_expr_tag_lst)
                   )
          
     |_->raise X_syntax_error
     in rec_tail_calls false e;;
(*********************************************THIRD FUNCTION***************************************************)
let not_member paramls  = (fun(v)-> not (List.mem v paramls)) ;;
let rec start_box_set setList e =
  match e with 
  |Const' _|Box' _ |BoxGet' _|Var'(VarFree _)->e
  |Var'(VarParam(v,minor))->
        let member=(List.mem v setList)in
        (match member with
        |false->e
        |_->(BoxGet'(VarParam(v,minor))) 
        )

  |Var'(VarBound(v,index1,index2))-> 
        let member=(List.mem v setList)in
        (match member with
        |false->e
        |_->(BoxGet'(VarBound(v,index1,index2))) 
        )

  |BoxSet'(var,exp)-> let new_exp=start_box_set setList exp in
                      BoxSet'(var,new_exp)

  |If'(test,dit,dif)->let new_test=start_box_set setList test in
                      let new_dit= start_box_set setList dit in
                      let new_dif= start_box_set setList dif in
                      If'(new_test,new_dit,new_dif)

  |Seq' (exp_ls)->let new_exps= List.map(fun (a)->(start_box_set setList a))exp_ls in
                      Seq'(new_exps)

  |Set'(Var'(VarBound(var,major,minor)),exp)->
                      let new_exp=start_box_set setList exp in
                      (match (List.mem var setList) with
                      |false->Set'(Var'(VarBound(var,major,minor)),new_exp)
                      |_-> BoxSet'(VarBound(var,major,minor),new_exp)
                      )
  |Set'(Var'(VarParam(var,minor)),exp)->
                      (match  (List.mem var setList) with 
                      |false-> Set'(Var'(VarParam(var,minor)),start_box_set setList exp)
                      |_-> BoxSet'(VarParam(var,minor),start_box_set setList exp)
                      )

  |Set'(Var'(VarFree(var)),exp)->
                  let new_exp=start_box_set setList exp in
                   Set'(Var'(VarFree(var)),new_exp)

  |Def'(exp1,exp2)->
                  let new_exp1=start_box_set setList exp1 in
                  let new_exp2= start_box_set setList exp2 in
                  Def'((new_exp1),(new_exp2))

  |Or'(exp_lss)-> let new_exps=List.map(fun a->(start_box_set setList a))exp_lss in
                  Or'(new_exps)

    |LambdaSimple'(paramls,bdy)-> 
    (let filtered_ls= List.filter (not_member paramls) setList in
      let need_box_params= filter_lambda_params paramls bdy in
          let concat_lss=(need_box_params@filtered_ls) in 
          let boxed_params= new_body paramls need_box_params in
          let boxed_body= start_box_set concat_lss  bdy in
            let final_bdy = boxed_params@[boxed_body] in
            (match final_bdy= [] with
            |false-> 
            (match final_bdy with
              |hd::[]->LambdaSimple'(paramls,hd)
              |hd->LambdaSimple'(paramls,Seq' hd)
            )
            |_-> LambdaSimple'(paramls,Const' Void) 
            )
    )

  |LambdaOpt' (paramls,last_var,bdy)->
    (let filtered_ls= List.filter (not_member paramls) setList in
      let all_params=(last_var::paramls) in
      let need_box_params= filter_lambda_params all_params bdy in
        let all_params2=(paramls@[last_var]) in 
        let concat_lss=(need_box_params@filtered_ls) in 
        let boxed_params= new_body all_params2 need_box_params in
          let boxed_body= start_box_set concat_lss bdy in
          let final_bdy = boxed_params@[boxed_body] in 
            (match final_bdy= [] with 
            |false->(match final_bdy with 
                    |hd::[]->LambdaOpt'(paramls,last_var,hd)
                    |hd->LambdaOpt'(paramls,last_var,Seq' hd)
                    )
            |_-> LambdaOpt'(paramls,last_var,Const' Void)    
            )
    )

  |Applic'(exp,exp_ls) ->let box_ls= (List.map (fun a->(start_box_set setList a))exp_ls) in 
                         let new_exp=start_box_set setList exp in
                         Applic'((new_exp),box_ls) 

  |ApplicTP'(exp,exp_ls)->let box_ls= (List.map (fun a->(start_box_set setList a))exp_ls) in
                          let new_exp=start_box_set setList exp in 
                          ApplicTP'((new_exp),box_ls)

  |_-> raise  X_syntax_error;;

let box_set e = start_box_set [] e;;

let run_semantics expr =
 box_set
    ( annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)
