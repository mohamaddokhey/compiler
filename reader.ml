
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)


#use "pc.ml";;
open PC;;
exception X_this_should_not_happen;;

type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;
 
let nt_left_paren = char '(' ;;
let nt_right_paren = char ')' ;;
let nt_left_square = char '[' ;;
let nt_right_square = char ']' ;;
let nt_left_space = (pack (caten nt_left_paren (star nt_whitespace))  (fun (a,b)->a))
let nt_lefts_space = (pack (caten nt_left_square (star nt_whitespace))  (fun (a,b)->a))
(*****************************************************THREE DOTS!*****************************************************************)
let nt_close = (disj nt_right_square nt_right_paren);;
let nt_open  = (disj nt_left_paren nt_left_square);;
let nt_close_all = (word "...");;
let nt_prefix1 = (word "#(");;
let nt_prefix2 = (word "#[");;
(*********************************************************************************************************************************)
let nt_1dot=(char '.');;
let nt_spaces = star nt_whitespace;;
let nt_whitespace1=  pack  (nt_whitespace) (fun  a->[] );;
let nt_not_whitespace = const (fun ch -> ch > ' ');;
let nt_semi= (char ';');;
let nt_notnl=((star (disj(range '0' '9')(range (char_of_int 11) (char_of_int 127)))));;
let nt_comment =(pack 
(pack 
(pack (caten  
(pack (caten nt_semi nt_notnl)
(fun (a,b)->a::b) )(disj (char (char_of_int 10)) (pack nt_end_of_input (fun _ -> '\n'))))
(fun (a,b)->a@[b]))
(fun (ls)-> (list_to_string ls)))
(fun (string)-> ' ' ));;


let nt_comment1 =(pack 
(pack 
(pack (caten  
(pack (caten nt_semi nt_notnl)
(fun (a,b)->a::b) )(disj (char (char_of_int 10)) (pack nt_end_of_input (fun _ -> '\n'))))
(fun (a,b)->a@[b]))
(fun (ls)-> (list_to_string ls)))
(fun (string)-> [] ));;

let nt_junk =pack (star (disj nt_comment nt_whitespace)) (fun a->' ');;

let nt_boolean = pack(caten (char '#') (disj (char_ci 't') (char_ci 'f'))) 
(
  fun (hashtag,t_or_f) -> match (Char.lowercase_ascii t_or_f) with
| 't' ->  Bool true
| 'T' ->  Bool true
| 'f' ->  Bool false
| 'F' ->  Bool false
|   _ ->  raise X_this_should_not_happen);;

let nt_SymbolChar= (disj_list [
(range (char_of_int 48)(char_of_int 57));
(range (char_of_int 65)(char_of_int 90));
(range (char_of_int 97)(char_of_int 122));
(char '!');(char '$');(char '^');(char '*');(char '-');(char '_');(char '=');(char '+');(char '<');(char '>');(char '?');(char '/');(char ':');]);;
let nt_VisibleSimpleChar=(range (char_of_int 33)(char_of_int 126));;

let nt_Symbol= (pack (plus (nt_SymbolChar)) (fun ls -> (String.lowercase_ascii(list_to_string ls))));;

let nt_digit = (range '0' '9');;
let nt_natural = let nt = (plus  nt_digit) in 
let nt =(pack nt (fun ls -> (list_to_string ls) ))in
(pack nt (fun st-> (int_of_string st)))
;;

let nt_plus_Integer = (pack(caten(disj (char '+') (char '-') ) nt_natural)  
(fun (plus_minus,number)-> match plus_minus with 
| '-' ->  (~-)number
| '+' ->  number
| _ -> raise X_this_should_not_happen
));;

let nt_Integer = (disj nt_plus_Integer nt_natural ) ;;

let nt_sci_integer= (pack(caten (pack (caten nt_Integer (char_ci 'e')) (fun (a,b)->a)) nt_Integer)  (fun (a,b)-> (10.0**(float_of_int b)*.(float_of_int a)  ) )
 );;

let nt_A_to_F = (range 'A' 'F');;
let nt_a_to_f = (range 'a' 'f');;

let nt_HexDigit = (disj_list [nt_digit;nt_a_to_f;nt_A_to_F;]);;
let nt_HexNatural = (plus(nt_HexDigit));;

let nt_HexChar =(pack(pack (pack(pack(pack (caten (char_ci 'x')(plus nt_HexDigit)) 
(fun (h,t)->h::t)) 
(fun ls-> ['0']@ls)) 
(fun ls->(list_to_string ls)))  
(fun st->(int_of_string st))) 
(fun (num)-> (Char.chr(num)))) ;;
let nt_HexPrefix=(disj (word "#x")(word "#X")) ;;

let nt_plus_Hex_Integer = (pack(caten(disj (char '+') (char '-') )nt_HexNatural) 
(
fun (plus_minus,number)-> match plus_minus with 
| '-' ->  (~-)(int_of_string (list_to_string (['0';'x';] @ number)))
| '+' ->  (int_of_string (list_to_string (['0';'x';] @ number)))
| _ -> raise X_this_should_not_happen
));; 

let nt_Hex_no_sign_Integer = (pack (pack (pack  nt_HexNatural
(fun ls-> (['0';'x';] @ ls)))  
(fun ls->  (list_to_string ls))) 
(fun st-> (int_of_string st)  
));; 
let nt_HexInteger = (pack(caten (pack nt_HexPrefix 
(fun ls-> ' ')) (disj nt_plus_Hex_Integer nt_Hex_no_sign_Integer)) 
(fun (_,num)-> num)  
);; 

let nt_plus_float = pack (caten(disj (char '+') (char '-')) (plus nt_digit))
(fun (head,tail)-> (head::tail));;
let nt_normal_float=(plus nt_digit);;

let nt_float_normal = (pack(pack(caten(pack(caten(disj nt_plus_float nt_normal_float) (char '.') )
(fun (h,t)->h@[t])) (plus nt_digit)) 
(fun (h,t)->h@t))
(fun (ls)-> match (List.hd ls) with 
| '-' ->  (~-.)(float_of_string (list_to_string (List.tl ls)))
| '+' ->  (float_of_string(list_to_string (List.tl ls)))
| _ ->  (float_of_string(list_to_string ls))
));;

let nt_sci_float = (pack (caten (pack (caten nt_float_normal (char_ci 'e'))  (fun (a,b)->a)) nt_Integer) (fun (a,b)->(10.0**(float_of_int b)*.a)))
;;
let nt_float= (disj_list [nt_sci_float; nt_float_normal; nt_sci_integer;] );;
let nt_ignorethreedots=(word "...");;

let nt_plus_minus_hexfloat= (pack (pack (caten (pack (caten (pack (caten (disj (char '+') (char '-')) nt_HexNatural)  
(fun (head,tail)-> (head::tail)))(char '.')) 
(fun (head,tail)-> (head @[tail]))) nt_HexNatural)
(fun (head,tail)-> (head@tail)))
(fun (ls)-> match (List.hd ls) with 
| '-' ->  (~-.)(float_of_string (list_to_string (['0';'x';]@(List.tl ls))))
| '+' ->  (float_of_string(list_to_string (['0';'x';]@(List.tl ls))))
| _ ->  raise X_this_should_not_happen));;

let nt_noraml_hexfloat = (pack (pack (caten (pack ( caten nt_HexNatural (char '.')) 
(fun (head,tail)-> (head @[tail]))) nt_HexNatural)  
(fun (head,tail)-> (head@tail))) 
(fun (ls)->   (float_of_string(list_to_string (['0';'x';]@(ls)))) ) )
;;
let nt_HexFloat = (pack (caten nt_HexPrefix  (disj nt_plus_minus_hexfloat  nt_noraml_hexfloat )) 
(fun (_,num)-> num));;

let nt_number = (  not_followed_by   (disj_list [
  (pack nt_HexFloat     (fun a->   Number( Float (a))));
  (pack nt_float        (fun a->   Number( Float (a))));
  (pack  nt_HexInteger (fun a->    Number( Int (a))));
  (pack nt_Integer      (fun a->   Number( Int (a))));
  ])    nt_Symbol  );;

let nt_tab=(word_ci "tab");;
let nt_return=(word_ci "return");;
let nt_nul=(word_ci "nul" );;
let nt_page=(word_ci "page");;
let nt_space=(word_ci "space");;
let nt_newline=(word_ci "newline");;

let nt_NamedChar= (pack (pack (pack (disj_list [ nt_tab;nt_return;nt_nul;nt_page;nt_space;nt_newline;])
(fun (ls)-> list_to_string ls) )
(fun (str)-> ( String.lowercase_ascii str)))
(fun (str) -> match (str) with 
| "nul" ->     (Char.chr 0)
| "return" ->  (Char.chr 13)  
| "tab" ->     (Char.chr 9)
| "page" ->    (Char.chr 12)
| "newline" -> (Char.chr 10)
| "space" ->   (Char.chr  32) 
| _ ->  raise X_this_should_not_happen ));;

let nt_StringLiteralChar = (disj_list [ 
  (range (char_of_int 11) (char_of_int 33)) 
;(range (char_of_int 35) (char_of_int 91))
;(range (char_of_int 93) (char_of_int 127));]);;

let nt_CharPrefix= (word_ci "#\\");;

let nt_StringMetaChar =  (pack (caten (char '\\') (disj_list [ (char '\\');(char '\"');(char 'f');(char 't');(char 'n');(char 'r');]))
(fun(  a, b )-> match b with 
| '\\' -> '\\'
| '\"'-> '\"'
| 'f'-> '\012' 
|'t'-> '\t'
| 'n'-> '\n'
|'r'-> '\r' 
| _ -> raise X_this_should_not_happen)) ;;

let nt_StringHexChar=(pack (caten (pack (pack (pack (pack (pack(pack(pack (caten (word_ci "\\x") (plus nt_HexDigit)) 
(fun (h,t)->h@t)) 
(fun ls->  ( List.tl ls))  ) 
(fun ls->  ( List.tl ls))) 
(fun ls->  (['0';'x';]@ls))) 
(fun ls-> (list_to_string ls)))
(fun st-> (int_of_string st)  )) 
(fun num -> (char_of_int num )))(char ';'))(fun (a,b)-> a))
;;

let nt_1=(disj nt_StringHexChar nt_StringLiteralChar);;
let nt_StringChar=(disj nt_1 nt_StringMetaChar);;
let oneDot= (pack (caten (pack (caten nt_spaces nt_1dot)(fun (a,b)-> b)) nt_spaces)(fun(a,b)->b));;
let nt_charslash=(pack (char '\"') (fun ch-> [ch]));;
let nt_star_string= (star nt_StringChar);;
let nt_String =(pack (pack (pack (caten (pack (caten nt_charslash nt_star_string)
(fun (a,b)->b))nt_charslash) 
(fun (a,b)->a))(fun ls->(list_to_string ls)))
(fun str-> (String str)));;

let nt_Char = (pack (pack ( caten nt_CharPrefix 
(disj_list 
[ nt_NamedChar;
  nt_HexChar;
  nt_VisibleSimpleChar;]))  
  (fun(h,t)-> h@[t] )) 
  (fun (ls)->(List.hd(List.tl(List.tl ls)))
  ));;

let nt_Nil= (pack (caten(caten(char(char_of_int 40))(star(disj nt_comment nt_whitespace)))(char (char_of_int 41)))  
(fun(a)->()));; 

let nt_solamet= (char '#');;
let nt_dottedcoma = (char ';');;
let nt_pre = pack   (caten nt_solamet nt_dottedcoma) (fun (a,b)->a)  ;;
 
let rec _list1_ s =
let nt_sexpr_list = (star _Sexpr_) in
let _packed_ =(pack (pack(caten(pack(caten nt_left_paren nt_sexpr_list)
(fun (a,b)->b)) nt_right_paren)
(fun (a,b)->a))  
(fun ls->List.fold_right 
(fun a b -> Pair(a,b)) ls Nil)) in 
_packed_ s

and  _list2_ s =
let nt_sexpr_list = (star _Sexpr_) in
let _packed_ =(pack (pack(caten(pack(caten nt_left_square nt_sexpr_list)
(fun (a,b)->b)) nt_right_square)
(fun (a,b)->a))  
(fun ls->List.fold_right 
(fun a b -> Pair(a,b)) ls Nil)) in 
_packed_ s

and _Dotted1_ s =
let nt_plusList=(plus _Sexpr_) in 
let _packed_ = (pack  (pack(caten (caten (pack(caten(pack(caten nt_left_paren nt_plusList)
(fun (a,b)->b)) (char '.'))
(fun (a,b)->a))_Sexpr_) nt_right_paren)
(fun (a,b)->a)) 
(fun (ls,tl)->List.fold_right 
(fun a b -> Pair(a,b)) ls tl))   

in 
_packed_ s

and _Dotted2_ s =
let nt_plusList=(plus _Sexpr_) in 
let _packed_ = (pack  (pack(caten (caten (pack(caten(pack(caten nt_left_square nt_plusList)
(fun (a,b)->b)) (char '.'))
(fun (a,b)->a))_Sexpr_) nt_right_square)
(fun (a,b)->a)) 
(fun (ls,tl)->List.fold_right 
(fun a b -> Pair(a,b)) ls tl))   

in 
_packed_ s

and _vector_ s = 
let nt_sexpr_list = (star _Sexpr_) in
let _packed_ = (pack(caten  (pack (caten (pack (word "#(")
(fun ls->List.tl ls)) nt_sexpr_list )
(fun (a,b)->b))  nt_right_paren)  
(fun (a,b)->a)) in
_packed_ s

and _vector1_ s = 
let nt_sexpr_list = (star _Sexpr_) in
let _packed_ = (pack(caten  (pack (caten (pack (word "#[")
(fun ls->List.tl ls)) nt_sexpr_list )
(fun (a,b)->b))  nt_right_square)  
(fun (a,b)->a)) in
_packed_ s

and _empty_vector s=
(pack (word  "#()") (fun a-> Nil))

and _Quoted_ s = let _packed_=(pack (pack (caten (char (char_of_int 39)) _Sexpr_) 
(fun (a,b)->b ))
(fun a->   Pair(Symbol("quote"),Pair(a,Nil)))) in  _packed_ s


and _Qqouted_ s = let _packed_=(pack (caten (char (char_of_int 96)) _Sexpr_)
(fun(a,b)-> Pair(Symbol("quasiquote"),Pair(b,Nil)))) in 
_packed_ s

and _Unqouted_ s = let _packed_ =(pack (pack (caten (char (char_of_int 44)) _Sexpr_)
(fun (a,b)->b))
(fun x->Pair(Symbol("unquote"),Pair(x,Nil)))) in 
 _packed_ s

and _UnqoutedSpliced_ s =let _packed_ =(pack (pack  (caten (pack (caten (char (char_of_int 44)) (char (char_of_int 64)))
(fun(a,b)->b)) _Sexpr_) 
(fun(a,b)->b))
(fun x-> (Pair(Symbol("unquote-splicing"),Pair(x,Nil))))) in
_packed_ s


and iter list num= 
 match num with 
|0 ->([],list)
|_->let (exp,rest)= (_Sexpr_ list) in 
(iter rest (num-1))
    
and  _Sexprcomment_ s = 
let _reiter_ (cnum,charls) =(iter charls cnum) in
_reiter_((pack (plus (caten nt_pre (star (disj_list [nt_whitespace1;nt_comment1;_Sexprcomment_]))))(fun ls->List.length ls)) s)


and _D_ s=let _packed_=(disj (pack  (pack(caten (caten (pack(caten(pack(caten nt_left_space (plus _A_))
                        (fun (a,b)->b)) oneDot)
                        (fun (a,b)->a))_A_) (maybe nt_right_paren))
                        (fun (a,b)->a)) 
                        (fun (ls,tl)->List.fold_right 
                        (fun a b -> Pair(a,b)) ls tl)) 
                        (pack (pack(caten (caten (pack(caten(pack(caten nt_lefts_space (plus _A_))
                        (fun (a,b)->b)) oneDot)
                        (fun (a,b)->a))_A_) (maybe nt_right_square))
                        (fun (a,b)->a)) 
                        (fun (ls,tl)->List.fold_right 
                        (fun a b -> Pair(a,b)) ls tl)))  in _packed_ s

and  _L_ s=  let _packed_ =  (disj 
                        (pack (pack(caten(pack(caten nt_left_space (star _A_))
                        (fun (a,b)->b))(maybe nt_right_paren))
                        (fun (a,b)->a))  
                        (fun ls->List.fold_right 
                        (fun a b -> Pair(a,b)) ls Nil))
                        (pack (pack(caten(pack(caten nt_lefts_space (star _A_))
                        (fun (a,b)->b)) (maybe nt_right_square))
                        (fun (a,b)->a))  
                        (fun ls->List.fold_right 
                        (fun a b -> Pair(a,b)) ls Nil))) in _packed_ s 

and _V_ s =  let _packed_= 
                        (pack(caten(pack (caten (pack nt_prefix1
                        (fun ls->List.tl ls)) (star _A_) )
                        (fun (a,b)->b))  (maybe nt_right_paren))  
                        (fun (a,b)->a)) 
                        in  _packed_ s
and _S_ s= let _packed_ =(pack (caten (disj_list [_D_;_L_;(pack _V_ (fun a->(Vector a)))])(nt_close_all))(fun (a,b)->a)) in (*the vector *)
_packed_ s
and _A_ s=let _packed_= (disj_list [(diff _Sexpr_ _S_) ;_D_ ;_L_;(pack _V_ (fun a->(Vector a)))])  in _packed_ s

and  _Sexpr_ s =
let _packed_=
(pack (caten (pack 
(caten (star (disj_list [nt_comment1;_Sexprcomment_;nt_whitespace1;])) 
(disj_list[
(pack nt_Char(fun a-> (Char(a))));
(pack nt_String (fun a-> (a)));
(pack nt_Nil  (fun a-> Nil ));
(pack nt_boolean(fun a-> (a)));
(pack nt_number (fun a-> a));
(pack nt_Symbol (fun a-> (Symbol(a))));
_list1_;_list2_; _Dotted1_; _Dotted2_;
(pack  _vector_  (fun a-> (Vector a)));
(pack  _vector1_ (fun a-> (Vector a)));
_Quoted_;
_Qqouted_;
_Unqouted_ ;
_UnqoutedSpliced_;
_S_;
])) 
(fun (a,b)->b))(star (disj_list [nt_whitespace1;nt_comment1;_Sexprcomment_;])))(fun (a,b)->a))
 in _packed_ s ;;

let nt_Ignore s = 
  let(junk,s) = (star (disj_list [nt_whitespace1;nt_comment1;_Sexprcomment_;])) s in
    let (mdots,s) = nt_ignorethreedots s in
      (mdots,s);;

let nt_removextra s =
  let(junk,expr)= maybe(nt_Ignore) s in
  _Sexpr_ expr;;

let read_sexpr string = 
let parsedval=(not_followed_by _Sexpr_  _Sexpr_ (string_to_list string)) in 
match parsedval with (exp,a) -> exp 

let read_sexprs string = 
if (String.length string)==0 then [] else
let(exp,s) = plus(nt_removextra)
  (string_to_list string) in exp;;  

end;;
(* struct Reader *)