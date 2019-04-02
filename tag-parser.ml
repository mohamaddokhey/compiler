(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;
open Reader;;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;        
exception X_pair_of_list;;
exception X_error_expand_cond


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  
(*********************************************help functions***************************************************)
let rec get_lambda_args x =
   match x with  
  |Pair   (Pair (Symbol(v), Pair (b, Nil)), Nil)->Pair(Symbol(v),Nil)
  |Pair   (Pair (Symbol(v), Pair (b, Nil)), rest)->Pair(Symbol(v),(get_lambda_args rest))
  |Nil->Nil
  |_-> raise X_pair_of_list
  ;;
  
  let rec get_lambda_vals x= 
   match x with  
  |Pair(Pair (Symbol(v), Pair (b, Nil)), Nil) ->Pair(b,Nil)
  |Pair(Pair (Symbol(v), Pair (b, Nil)), rest)->Pair(b,(get_lambda_vals rest))
  |Nil->Nil
  |_-> raise X_pair_of_list;;

 let rec check_prop x= 
  (match x with 
    |Nil        -> true
    |Pair(_,Nil)-> true 
    |Pair(_,Pair(x,y)) -> check_prop (Pair (x,y))
    |_ -> false
  )

and list_of_pair x = 
  (match x with     
  |Pair(expr,Pair(car,cdr))->expr::list_of_pair(Pair(car,cdr))
  |Pair(expr,Nil)->[expr]
  |Nil->[]
  |_->raise X_syntax_error
  ) 
   

 and list_of_pair_cond x = 
  (match x with     
  |Pair(first,second)->(first::list_of_pair_cond second)
  |Nil->[]
  |_->raise X_syntax_error
  ) ;;

 let getSeqOrvar ls = 
  (match ls with
      |[hd] -> hd
      |hd::tl -> Seq ls 
      |[]->Const Void 
  );; 

let rec list_of_pair_lambda_body x= 
  match x with  
      |Pair(Pair(Symbol"begin",Pair(car,cdr)),Nil)->(list_of_pair(Pair(car,cdr)))
      |Pair(expr,Pair(car,cdr))->expr::(list_of_pair(Pair(car,cdr)))
      |Pair(expr,Nil)->[expr] 
      |Nil->[]
      |_ -> raise X_syntax_error


  and  list_of_pair_improper x= 
  match x with 
      |Pair(exp,Pair(a,b))-> exp::(list_of_pair_improper(Pair (a,b)))
      |Pair(Symbol(exp1),Symbol(exp2))->[Symbol (exp1);Symbol(exp2)]
      |_-> raise X_syntax_error

;;

let make_pair=(fun one two->Pair(one,two));;
  
  let rec arg_to_str x= 
  match x with
  |[Symbol(a)]->[a]
  |Symbol(a)::left->[a]@(arg_to_str left) 
  |[]->[]
  |_-> raise X_no_match 


  and handle_ls left emptyls packit id =
    (match left with
      |Pair(first,rest)->
            let curry=(fun ()->packit first) and
            untaged  =(fun rest->id(first::rest)) and
            taged    =(fun tag ->id[first;tag]) in 
            (handle_ls rest curry taged untaged)
      |Nil->emptyls ()
      |_->raise X_syntax_error
    );;

            let get_var x = (match x with 
                              |(Pair(var,(Pair(value,Nil))))->var
                              |_ ->raise X_syntax_error
                            )

            and get_val x = (match x with
                              |(Pair(var,(Pair(value,Nil))))->value
                              |_ ->raise X_syntax_error
                            )       
            and get_we x = (match x with
                              |(Pair(name,(Pair(expr,Nil))))->
                                        (Pair(name,(Pair((Pair(Symbol("quote"),Pair(Symbol("whatever"),Nil))),Nil))))
                              |_ ->raise X_syntax_error
                           )
            and make_set= (fun var expr ->
                          (Pair((Symbol("set!")),
                          (Pair(var,(Pair(expr, Nil))))))
                          )
            and packit=(fun x->[x])
            and id = (fun x->x)
            and emptyls=(fun ()->[]);;
(**********************************expanders*********************************)
let rec expand_Qqoute x =  
match x with
|Pair(Symbol("unquote"),(Pair(y,Nil)))-> y

|Pair(Symbol("unquote-splicing"),a)-> raise X_syntax_error

|Symbol(a)->Pair(Symbol("quote"),(Pair(Symbol(a),Nil)))

|Nil->(Pair(Symbol("quote"),(Pair(Nil,Nil))))

|(Vector ls)->
                let result= (List.map expand_Qqoute ls) in  
                let exps_pairs=(List.fold_right make_pair result Nil) in  
                Pair(Symbol("vector"),exps_pairs)
|Pair(x_A,x_B)->
                  (match(x_A,x_B)with
                  |Pair(Symbol("unquote-splicing"),(Pair(head,Nil))),x_B->
                          Pair(Symbol("append"),(Pair(head,(Pair((expand_Qqoute x_B),Nil)))))

                  |x_A,Pair(Symbol("unquote-splicing"),tail)->
                          Pair(Symbol("cons"),(Pair((expand_Qqoute x_A),tail)))

                  |_->
                          Pair(Symbol("cons"),Pair((expand_Qqoute x_A),Pair((expand_Qqoute x_B),Nil)))
                  ) 
|exp->exp;; 


let rec expand_and x = 
  (match x with 

    |first::second::[]->(Pair(Symbol("if"),Pair(first,Pair(second,Pair(Bool false,Nil)))))
    |first::[]->first
    |first::rest ->
            let expanded=(expand_and rest)in
            (Pair(Symbol("if"),Pair(first,Pair(expanded,Pair(Bool false,Nil)))))
    |_-> raise X_syntax_error
  )
(***********************************EXPAND COND************************************************)
 and expand_cond x= 
  (match x with
  
  |[Pair(Symbol("else"),expr_i)]->Pair(Symbol("begin"),expr_i) 

  |[Pair(testk,Pair(Symbol "=>",Pair (thenk,Nil)))] ->
    
            Pair (Symbol "let",
            Pair(Pair(Pair(Symbol "value",Pair(testk, Nil)),
            Pair(Pair(Symbol "f",Pair(Pair(Symbol "lambda",Pair(Nil,Pair(thenk, Nil))),Nil)),Nil)),
            Pair(Pair(Symbol "if", Pair(Symbol "value",Pair(Pair(Pair(Symbol "f",Nil),
            Pair (Symbol "value",Nil)),Nil))),Nil)))

  |[Pair(test,expr_i)]->Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),expr_i),Nil)))

  |Pair(testk,Pair(Symbol "=>",Pair(thenk,Nil)))::rest->
     let expanded=(expand_cond rest) in
              
            Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(testk, Nil)), 
            Pair(Pair(Symbol "f", 
            Pair(Pair(Symbol "lambda", Pair(Nil, Pair(thenk, Nil))), Nil)), 
            Pair(Pair(Symbol "rest", 
            Pair(Pair(Symbol "lambda", Pair(Nil, 
            Pair(expanded, Nil))), Nil)), Nil))), Pair(Pair(Symbol "if",
            Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), 
            Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))


  |Pair(test,Pair(expr_i,Nil))::rest -> 
              let expanded=(expand_cond rest) in
              Pair(Symbol("if"),Pair(test,Pair(expr_i,Pair(expanded,Nil)))) 
  
  |Pair(test,expr_i)::rest ->    
              let expanded=(expand_cond rest) in         
              Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),expr_i),Pair(expanded,Nil))))

  |_-> raise X_error_expand_cond
  )


  let expand_letrec claws data =
        let parts = handle_ls claws emptyls packit id in
        let pars  = (List.map get_var parts) 
        and vals  = (List.map get_val parts) in
        let body  = (List.fold_right make_pair(List.map2 make_set pars vals)data) 
        and parts = (List.map get_we parts) in
        let parts = (List.fold_right make_pair parts Nil) in
        Pair((Symbol("let")),(Pair(parts,body)));;

(******************************************parsers*************************************)
let nt_parse_var x = match x with 

    |Symbol(x)->
      (match (List.mem x reserved_word_list ) with  
      |true ->raise X_no_match 
      |_-> (Var x)
      )
    |_->raise X_syntax_error
;;


let rec nt_parse_and x = match x with

    |Pair(Symbol"and",rest)->
        (match rest with 
            |Nil ->tag_parse(Bool true)
            |_   ->tag_parse(expand_and(list_of_pair rest))
        )
    |_->raise X_no_match


and nt_parse_const x = match x with 

    |Bool(x)-> Const (Sexpr (Bool(x)))
    |Char(x) -> Const(Sexpr(Char(x)))
    |Number(x)-> Const(Sexpr(Number(x)))
    |String(x)-> Const(Sexpr(String(x)))
    |Nil -> Const (Void)
    |_-> raise X_no_match

and nt_parse_quote x = match x with 

    |Pair(Symbol("quote"),Pair(sexpr1, Nil))-> Const(Sexpr(sexpr1))
    |Pair(Symbol("unquote"),Pair(_sexpr, Nil))-> Const(Sexpr(_sexpr))
    |Pair(Symbol("unquote-splicing"),Pair(_sexpr, Nil))-> raise X_syntax_error
    |Pair(Symbol("quasiquote"), Pair(_sexpr, Nil)) -> 
                          (tag_parse (expand_Qqoute _sexpr))
    
    | _-> raise X_no_match

and nt_parse_if  x= match x with 
    
    |Pair((Symbol("if")),(Pair(test,(Pair(dit,Nil))))) ->
              If((tag_parse test),(tag_parse dit),(tag_parse Nil))

    |Pair((Symbol("if")),(Pair(test,(Pair(dit,(Pair(dif,Nil))))))) ->
              If((tag_parse test),(tag_parse dit),(tag_parse dif)) 
    
    | _-> raise X_no_match


and nt_parse_or x = match x with    

    |Pair(Symbol("or"),exprs) ->
    (match exprs with 
        |Nil -> tag_parse (Bool false)
        |_-> 
          let exprs=(list_of_pair exprs) in 
        ( match (List.map tag_parse exprs) with
            |[one]->one
            |_ -> Or(List.map tag_parse exprs)
        )
    )
    |_-> raise X_no_match


and nt_parse_define  x =
 match x with 

 |Pair(Symbol("define"),Pair(Pair(proc,vars),body))-> 
            (nt_parse_define(Pair(Symbol"define",Pair(proc,Pair(Pair(Symbol"lambda",Pair(vars,body)),Nil)))))

 |Pair((Symbol("define")),(Pair(var,(Pair(value,Nil)))))->Def((nt_parse_var var),(tag_parse value))
 | _ -> raise X_no_match

 and nt_parse_set x = 
 match x with 
 |Pair (Symbol "set!",rest)-> 
   (match rest with 
       |Pair (Symbol(a),Pair(y,Nil))->(Set((tag_parse(Symbol(a))),tag_parse y))
       |_-> raise X_syntax_error )
 |_-> raise X_no_match


 and nt_parse_applic x= match x with 
 |Pair(proc,exprs)->
        let argls =(list_of_pair exprs) in  
        let exprs= (List.map tag_parse argls) in 
        let proc= (tag_parse proc) in 
        Applic(proc,exprs)
 |_-> raise X_no_match 


 and nt_parse_lambda x = match x with 
 (*variadic *)
   |Pair (Symbol "lambda" ,Pair (Symbol (a),body))   ->
  (
     let bodylst=(list_of_pair_lambda_body body) in 
     match bodylst with 
     |[] -> raise X_syntax_error
     |_->
     let parsedbody= (List.map tag_parse  bodylst) in
     let bodyfinal = (getSeqOrvar parsedbody)in
     LambdaOpt ([],a , bodyfinal))

 (*not variadic *)
   |Pair (Symbol "lambda", Pair (arglst,body))-> 
      
      (let bodylst= (list_of_pair_lambda_body body) in
      match bodylst with 
     |[]-> raise X_syntax_error
     |_->
      let parsedbody= (List.map tag_parse  bodylst) in
      let bodyfinal = (getSeqOrvar parsedbody)in
      if(check_prop arglst) then
        (
        (*proper *)
            let ls=(list_of_pair arglst) in 
            let string_args= (arg_to_str ls) in
            (
                (LambdaSimple(string_args, bodyfinal)))
        ) 
        (*improper *)
      else (
            let ls=(list_of_pair_improper arglst) in 
            let string_args= (arg_to_str ls) in
             (
            let rev = (List.rev string_args )in (*getting the last element in arglst*)
            let last = (List.hd rev ) in 
            let args= (List.rev (List.tl rev))in
                LambdaOpt (args,last, bodyfinal))
            )
      )
   |_->raise X_no_match


   and nt_parse_begin x= 
   match x with  
    |Pair (Symbol "begin", Pair (a,b))-> 
        let ls = (list_of_pair (Pair (a,b))) in
        let parsedbody= (List.map tag_parse ls) in
          (getSeqOrvar parsedbody)

    | Pair (Symbol "begin",Nil)-> tag_parse Nil    
    |_-> raise X_no_match



 and nt_parse_cond x = match x with 
 |Pair (Symbol "cond", ls) -> 
                            let ribs =(list_of_pair ls) in 
                            (tag_parse (expand_cond ribs))

 |_ -> raise X_no_match
 

 and nt_parse_let x = match x with 
 |Pair (Symbol "let", Pair(args_vals,body))->
          let args=(get_lambda_args(args_vals)) in 
          let values = (get_lambda_vals(args_vals))in
          (nt_parse_applic(Pair((Pair(Symbol "lambda",Pair(args,body))),values)))
  
 |_->raise X_no_match


 and nt_parse_let_star x = match x with
  |Pair (Symbol "let*", Pair (Nil, body))->
          nt_parse_let(Pair (Symbol "let", Pair(Nil,body)))

  |Pair (Symbol "let*", Pair (Pair(Pair( (Symbol x ),s1),Nil), body))->
          nt_parse_let((Pair (Symbol "let",
          Pair(Pair(Pair( (Symbol x ),s1),Nil),body))))

  |Pair (Symbol "let*", Pair (Pair(Pair( (Symbol x ),s1),rest), body))->
          nt_parse_let((Pair (Symbol "let",Pair(Pair(Pair( (Symbol x),s1),Nil),
          Pair(Pair(Symbol "let*",Pair(rest,body)),Nil)))))

  |_-> raise X_no_match

  and nt_parse_letrec x = match x with 
  |Pair(Symbol "letrec", Pair(vars,body))-> 
             let expanded=(expand_letrec vars body)in 
             (tag_parse expanded)
 | _ -> raise X_no_match

and tag_parse x =  disj_list [nt_parse_const;
                              nt_parse_quote;
                              nt_parse_define;
                              nt_parse_if;
                              nt_parse_lambda;
                              nt_parse_or;
                              nt_parse_cond;
                              nt_parse_let;
                              nt_parse_set;
                              nt_parse_begin;
                              nt_parse_and;
                              nt_parse_applic;
                              nt_parse_let_star;
                              nt_parse_letrec;
                              nt_parse_var;] x ;; 

let tag_parse_expression sexpr = (tag_parse sexpr);;
let tag_parse_expressions sexpr = List.map tag_parse sexpr;;
end;;

 (* struct Tag_Parser *)
