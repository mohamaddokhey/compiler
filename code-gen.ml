#use "semantic-analyser.ml";;

module type CODE_GEN = sig

  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"
   ;"apply","apply";"car","car";"cdr","cdr";"cons","cons";"set-car!","set_car";"set-cdr!","set_cdr";
(* you can add yours here *)];;
(****************************HELP FUNCTIONS FOR THE TABLES!!*******************************************)
let rec remove_dups1 ls= 
    match ls with
    |[]->[]
    |x::xs-> if (List.mem x xs) 
             then (remove_dups1 xs) 
             else x::(remove_dups1 xs);;

  let remove_dups ls =List.rev (remove_dups1 (List.rev ls));;

  let rec calc_off cons_exp consts =
    match consts with 
    |(exp,(off,asm))::others -> 
      if exp=cons_exp 
      then (string_of_int off)
      else (calc_off cons_exp others)
    |_->raise X_syntax_error
      ;;

  let rec get_index var vars =
    match vars with 
    |(exp,index)::others ->
 
     if   exp=var
     then (string_of_int index)
     else (get_index var others)
    |_->raise X_syntax_error
    ;;
(******************************************************CONSTANT TABLE*********************************************************)  
let rec fill_consts ast = 
  match ast with
  
    |Const' a ->[a]
    
    |If'(test,dit,dif)->(fill_consts test)@(fill_consts dit)@(fill_consts dif)
  
    |Seq' exprs |Or' exprs ->List.flatten(List.map (fun a ->(fill_consts a)) exprs) 
  
    |Applic'(proc,exprs)->(fill_consts proc)@(List.flatten(List.map (fun a ->(fill_consts a)) exprs))
    |ApplicTP'(proc,exprs)->(fill_consts proc)@(List.flatten(List.map (fun a ->(fill_consts a)) exprs))
  
    |Set'(_,value)|Def'(_,value)->(fill_consts value)
  
    |BoxSet'(_,value)->(fill_consts value)
  
    |LambdaSimple'(_,body)|LambdaOpt'(_,_,body)->(fill_consts body)
  
    |_ -> [];;

let rec add_sub_cons con = 
  match con with
  |Sexpr (Pair(head,tail))->
  let car=(add_sub_cons (Sexpr head))in
  let cdr=(add_sub_cons (Sexpr tail))in 
  car@cdr@[Sexpr(Pair(head,tail))]

  |Sexpr(Vector exprs)->(List.flatten(List.map (fun x ->(add_sub_cons (Sexpr x)))exprs))@[Sexpr(Vector exprs)]  

  |Sexpr(Symbol s)->[Sexpr(String s)]@[Sexpr(Symbol s)]

  |something ->[something] ;;

let rec concat1 str ls = 
      match ls with 
      |[]->""
      |[final]->str^"const_tbl+"^final
      |head::tail->
      let str = str^"const_tbl+"^head^"," in
      concat1 str tail;;
let addrs_to_str addrs = concat1 "" addrs;;
 
let rec concat2 str ls = 
  match ls with 
  |[]->""
  |[final]->str^(string_of_int(Char.code final))
  |head::tail->
  let str = str^(string_of_int(Char.code head))^"," in
  concat2 str tail;;
let char_to_str chars = concat2 "" chars;;

let rec update_table table off rest=
  match rest with 
  |Sexpr(Number(Int n))::others-> 
      let new_off=(off+9) in
      let asm="MAKE_LITERAL_INT("^(string_of_int n)^")" in
      (update_table (((Sexpr(Number(Int n))),(off,asm))::table) new_off others)
    
  |Sexpr(Number (Float f))::others ->
      let new_off=(off+9) in
      let asm="MAKE_LITERAL_FLOAT("^(string_of_float f)^")" in
      (update_table (((Sexpr(Number(Float f))),(off,asm))::table) new_off others)
    
  |Sexpr(Char(c))::others ->
    let new_off=(off+2) in
    let asm= "MAKE_LITERAL_CHAR("^(string_of_int (Char.code c))^")" in
    (update_table ((Sexpr(Char(c)),(off,asm))::table) new_off others)

  |Sexpr(String(s))::others ->
    let new_off=(off+9+(String.length(s))) in
    let ls=(string_to_list s) in
    let asm="MAKE_LITERAL_STRING "^(char_to_str ls) in
    (update_table ((Sexpr(String(s)),(off,asm))::table) new_off others)

  |Sexpr(Symbol(s))::others ->
    let new_off=(off+9) in
    let str_off= (calc_off (Sexpr(String(s))) table)in
    let asm= "MAKE_LITERAL_SYMBOL(const_tbl+"^str_off^")" in
    (update_table ((Sexpr(Symbol(s)),(off,asm))::table) new_off others)
  
  |Sexpr(Pair(car,cdr))::others -> 
    let new_off =(off+17) in
    let car_off =(calc_off (Sexpr(car)) table) in
    let cdr_off =(calc_off (Sexpr(cdr)) table) in
    let asm="MAKE_LITERAL_PAIR(const_tbl+"^car_off^",const_tbl+"^cdr_off^")" in
    (update_table ((Sexpr(Pair(car,cdr)),(off,asm))::table) new_off others)          

   |Sexpr(Vector exprs)::others ->
    let new_off=(off +(List.length exprs)*8+9) in
    let off_lst = List.map (fun a->calc_off (Sexpr(a)) table) exprs in
    let addrs_str = addrs_to_str off_lst in
    let asm="MAKE_LITERAL_VECTOR "^addrs_str in 
    (update_table ((Sexpr(Vector exprs),(off,asm))::table) new_off others)

  |something::others ->(update_table table off others)

  |[]->table;; 
let create_cons_tbl const =
    let basics =
    [(Void, (0, "MAKE_VOID")); (Sexpr Nil, (1, "MAKE_NIL"));
    (Sexpr (Bool false), (2, "MAKE_BOOL(0)"));
    (Sexpr (Bool true), (4, "MAKE_BOOL(1)"))]in
    let basics= (List.rev basics) in
    List.rev(update_table basics 6 const);;

let make_consts_tbl asts =
    let all_consts= List.flatten(List.map (fun a ->(fill_consts a))asts) in
    let with_basics= [Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true));]@all_consts in
    let without_dups= (remove_dups with_basics) in
    let with_subs= List.flatten(List.map (fun a ->(add_sub_cons a))without_dups) in
    let without_dups = (remove_dups with_subs) in
    let consts_table = create_cons_tbl without_dups in
    consts_table;;
(***********************************************FREE VAR TABLE***********************************************************************)
let rec fill_vars ast =
  match ast with 
|Var'(VarFree(v))->[v]  

|If'(test,dit,dif)->(fill_vars test)@(fill_vars dit)@(fill_vars dif)

|Seq' exprs|Or' exprs->(List.flatten(List.map (fun(x)->fill_vars x) exprs))
  
|Def'(variable,value)|Set'(variable,value)->(fill_vars variable)@(fill_vars value)

|BoxSet'(_,value)->(fill_vars value)

|LambdaSimple'(_,body)|LambdaOpt'(_,_,body)->(fill_vars body)

|Applic'(proc,expr_ls)|ApplicTP'(proc,expr_ls)->(fill_vars proc)@(List.flatten(List.map (fun(x)->fill_vars x) expr_ls))
| _->[] ;;

let add_index = 
  let index =ref (-1) in 
  fun ()->(index:=!index+1);
          !index;; 

let make_fvars_tbl asts = 
  let with_dups=List.flatten(List.map (fun x->fill_vars x) asts) in 
  let with_basics= (List.map(fun (a,b)-> a) primitive_names_to_labels)@with_dups in
  let no_dups = remove_dups with_basics in
  let with_index=(List.map(fun x->(x,add_index())) no_dups) in
  with_index;;
(*************************************GENERATE !!**********************************************************************)
let unique_generate = 
  let count =ref (-1) in 
  fun ()->(count:=!count+1);
        (string_of_int  !count);;  

let addressInConstTable consts const ="const_tbl+"^ (calc_off const consts) ;;
let labelInFVarTable fvars const ="fvar_tbl+"^(get_index const fvars)^"*8" ;;

let rec concat3 str ls = 
  match ls with 
  |[]->""
  |[final]->str^final
  |head::tail->
  let str = str^head in
  concat3 str tail;;
let exp_to_gen gen_ls = concat3 "" gen_ls;;

let rec concat4 num str ls = 
  let cmp_str = "cmp rax, SOB_FALSE
                 jne Lexit"^num^"\n" in
  match ls with 
  |[]->""
  |[final]->str^final^"\n Lexit"^num^":\n"
  |head::tail->
  let str = str^head^cmp_str in
  concat4 num str tail;;
let or_to_gen  gen_ls = (concat4 (unique_generate()) "" gen_ls);;


let rec concat5 len ls = 
  match ls with
  
  |[final]-> final^"push rax
                    push "^len^"\n"
  
  |car::cdr->car^"push rax
                 "^(concat5 len cdr)
  |_-> "push 0\n";;
let app_to_gen gen_ls= "push SOB_NIL\n"^(concat5 (string_of_int(List.length gen_ls))(List.rev gen_ls)) ;;
  
let rec rec_gen consts fvars e depth params =
  let apply_gen =(fun exp ->(rec_gen consts fvars exp depth params)) in
  let gen = rec_gen consts fvars in
  (match e with 

  |Const'(c)-> "mov rax,"^(addressInConstTable consts c)^"
               "

  |Seq'(exp_ls)-> exp_to_gen (List.map apply_gen exp_ls)

  |Var'(VarParam(_, minor))-> let minor=(string_of_int minor) in
                              "mov rax,qword[rbp+8*(4+"^minor^")]
                              "    
  
  |Set'(Var'(VarParam(_, minor)),epsilon)->
                                        let minor=(string_of_int minor) in
                                        (gen epsilon depth params)^"
                                         mov qword [rbp+8*(4+"^minor^")],rax 
                                         mov rax,SOB_VOID
                                         "

  |Var'(VarBound(_, major, minor))->let major=(string_of_int major) in
                                    let minor=(string_of_int minor) in
                                    "    mov rax, qword [rbp +8*2]
                                         mov rax, qword [rax +8*"^major^"]
                                         mov rax, qword [rax +8*"^minor^"]
                                         "

  |Set'(Var'(VarBound(_, major, minor)),epsilon)->
                                    let major=(string_of_int major) in
                                    let minor=(string_of_int minor) in
                                        (gen epsilon depth params)^
                                    "    mov rbx, qword[rbp+8*2] 
                                         mov rbx, qword[rbx+8*"^major^"]
                                         mov qword[rbx+8*"^minor^"],rax 
                                         mov rax, SOB_VOID
                                         "

  |Var'(VarFree(v))->"mov rax, qword["^(labelInFVarTable fvars v)^"]
                     "

  |Set'(Var'(VarFree(v)),epsilon)->     (gen epsilon depth params)^
                                     "   mov qword["^(labelInFVarTable fvars v)^"],rax 
                                         mov rax, SOB_VOID
                                         "                                       
               
  |Or' (expr_ls)-> (or_to_gen  (List.map apply_gen expr_ls))

  |If'(test,dit,dif)->  
      let un_num= unique_generate() in                         
      (gen test depth params)^"
      cmp rax,SOB_FALSE
      je ELSE"^un_num^"\n"^
      (gen dit depth params)^
      "jmp Exit"^un_num^" 
       ELSE"^un_num^":\n"^  
      (gen dif depth params)^
      "Exit"^un_num^":
      "

  |BoxGet'(v)-> (gen (Var'(v)) depth params)^
                 "mov rax, qword [rax]
                 "

  |BoxSet'(v,epsilon)-> (gen epsilon depth params)^
                        "push rax\n"^
                        (gen (Var'(v)) depth params)^
                        "pop qword[rax]
                         mov rax, SOB_VOID
                         "

  |Box'(VarParam(name,index))->  let index=(string_of_int index) in
                                "MALLOC rax,WORD_SIZE
                                 mov rbx,PVAR("^index^")
                                 mov [rax],rbx
                                 "

  |Def'(Var'(VarFree(v)), val1)->       (gen val1 depth params)^
                                    "    mov qword["^(labelInFVarTable fvars v)^"],rax 
                                         mov rax,SOB_VOID
                                         "
  
|LambdaSimple'(lparams,body)->
   let new_d=(depth+1)in
   let cparams=(List.length lparams)in
   let unum=unique_generate() in
   let dep=(string_of_int (depth*8)) in 
   let pcount= (string_of_int params) in
  "    mov rbx,"^dep^"
       mov r14,rbx  
       mov r13,"^pcount^"             
       cmp rbx,0 
       jne .cont1
       jmp first_frame"^unum^"
  .cont1:
       MALLOC rbx,rbx
       mov r8,rbx                   
       mov rcx,8 
       jmp add_prev_params"^unum^"
       
   loop"^unum^": 
       cmp rcx,r14
       jne .cont2
       jmp .exit
  .cont2:
       sub rcx,8  
       mov r9,[rax + rcx]
       add rcx,8
       mov [r8+rcx],r9 
       add rcx,8 
       jmp loop"^unum^" 
  .exit:
       MAKE_CLOSURE(rax ,rbx ,Lcode"^unum^") 
       jmp Lcont"^unum^" 
   Lcode"^unum^": 
       push rbp 
       mov rbp, rsp 
      "^
  (gen body new_d cparams)^" 
       leave 
       ret 
    add_prev_params"^unum^": 
       mov rax,qword[rbp+2*8]"^"
       mov r10,rbp
       add r10,32         
       mov r11,r13 
       shl r13,3
       mov r12,r13
       MALLOC r12,r12 
       mov [r8],r12 
       mov r13,0  
  second_loop"^unum^":
       cmp r13,r11
       jne .cont3
       jmp  loop"^unum^" 
 .cont3:
       mov r9,qword[r10] 
       mov [r12],r9 
       add r10,8 
       add r12,8 
       add r13,1 
       jmp second_loop"^unum^" 
   first_frame"^unum^": 
       MAKE_CLOSURE(rax ,SOB_NIL ,Lcode"^unum^") 
   Lcont"^unum^":\n"        

  |LambdaOpt'(lparams,_,body)->
    let new_d=(depth+1)in
    let cparams=((List.length lparams)+1) in 
    let unum=(unique_generate()) in
    let plen= (string_of_int (List.length lparams)) in
    let dep=(string_of_int (depth*8)) in
    let pcount= (string_of_int params) in
  "    mov rbx,"^dep^"
       mov r14,rbx
       mov r13,"^pcount^"               
       cmp rbx,0 
       jne .cont1
       jmp first_frame"^unum^"
  .cont1:
       MALLOC rbx,rbx
       mov r8,rbx                     
       mov rcx,8
       jmp add_prev_params"^unum^" 

   loop"^unum^": 
       cmp rcx,r14
       jne .cont2
       jmp .exit
  .cont2:
       sub rcx,8   
       mov r9,[rax + rcx]
       add rcx,8
       mov [r8+rcx],r9 
       add rcx,8 
       jmp loop"^unum^"
                                          
  .exit:
  MAKE_CLOSURE(rax ,rbx ,Lcode"^unum^") 
       jmp Lcont"^unum^" 
 Lcode"^unum^": 
     mov r9,"^plen^" 
     mov r12,[rsp+16]  
     cmp  r9,r12
     jl  adjuct_frame"^unum^" 
 adjucted"^unum^": 
     push rbp 
     mov rbp, rsp\n"^
(gen body new_d cparams)^" 
     leave 
     ret 
 adjuct_frame"^unum^":
    shl r9,3 
    add r9,24
    mov r8,rsp
    add r8,r9
    shl r12,3
    add r12,24
    mov r11,rsp
    add r11,r12
.loop:
    cmp r8,r11
    je .exit    
    mov r9,[r11]
    sub r11,8
    mov r10,[r11]
    MAKE_PAIR(r12,r10,r9)
    mov [r11],r12 
    jmp .loop
.exit:
      jmp adjucted"^unum^" 
add_prev_params"^unum^":
       mov rax,qword[rbp+2*8]
       mov r10,rbp
       add r10,32 
       mov r11,r13 
       shl r13,3
       mov r12,r13 
       MALLOC r12,r12  
       mov [r8],r12  
       mov r13,0  
  second_loop"^unum^": 
       cmp r13,r11 
       jne .cont3
       jmp  loop"^unum^" 
 .cont3:  
       mov r9,qword[r10] 
       mov [r12],r9 
       add r10,8 
       add r12,8 
       add r13,1 
       jmp second_loop"^unum^"
 first_frame"^unum^": 
     MAKE_CLOSURE(rax ,SOB_NIL ,Lcode"^unum^") 
 Lcont"^unum^":\n" 

  |Applic'(proc,exprs) ->
  (app_to_gen (List.map apply_gen exprs))^
  (gen proc depth params)^"
    CLOSURE_ENV rbx,rax
    CLOSURE_CODE rcx,rax
    push rbx
    call rcx 
    add rsp, 8*1 
    pop rbx   
    shl rbx, 3
    add rbx,8  
    add rsp, rbx
    "

  |ApplicTP'(proc,exprs) ->
  let len =(string_of_int ((List.length exprs)+5)) in 
     (app_to_gen (List.map apply_gen exprs))^
     (gen proc depth params)^"
     CLOSURE_ENV  rbx,rax
     CLOSURE_CODE rcx,rax
     push rbx
     push qword[rbp+8*1]
     mov rax,qword[rbp]
     SHIFT_FRAME("^len^")
     mov rbp,rax 
     jmp rcx 
     "
                   
  |_ -> ""

  );;
  let generate consts fvars e = rec_gen consts fvars e 0 0;;
end;;

