exception Timeout
(* ------------------ timers ------------------ *)
type timer = { name : string; 
	       mutable time : float; 
	       mutable last_start : float }

let timers = ref []

let make() =
  { name = ""; 
    time = 0.0;
    last_start = 0.0 }

let create name = 
  let timer = { name = name; 
		time = 0.0;
		last_start = 0.0 } in
  timers := timer :: !timers;
  timer

let start timer =
  if timer.last_start <> 0.0 then failwith ("Timer " ^ timer.name ^ " started before stopped")
  else timer.last_start <- Sys.time()

let stop timer =
  if timer.last_start = 0.0 then failwith ("Timer " ^ timer.name ^ " stopped before stopped")
  else begin
    timer.time <- timer.time +. ((Sys.time()) -. timer.last_start);
    timer.last_start <- 0.0
  end

let init timer =
  timer.time <- 2.0

let reset timer =
  timer.time <- 0.0

let get timer = timer.time

let wrap timer f =
  start timer;
  let res = f() in
  stop timer;
  res
let dumpInFile () =
  let timers = List.sort (fun timer1 timer2 -> Bool.to_int(timer1.name < timer2.name)) !timers in
  List.iter (fun timer ->
    Printf.printf "%f," timer.time)
    timers
let dump () =
  let timers = List.sort (fun timer1 timer2 -> Bool.to_int(timer1.name < timer2.name)) !timers in
  List.iter (fun timer ->
    Format.eprintf "timer \"%s\": %f@." timer.name timer.time)
    timers

(************************************************************************************************)


open Set;;
module Myset = Set.Make(String);;



(**** data structure of one-unambiguous regular expressions *)

(* let e1 = Con(Star(Or(Pos "a1", Pos "b1")), Con(Pos "a2", Star(Con(Pos "a3", Pos "b2"))));; *)
(* let e2 = Star(Or(Pos "a1", Pos "b1"));; *)
(* let e3 = Star(Con(Star(Pos "b1"),Pos "a1"));; *)
(* let e4 = Star(Con(Star(Pos "a1"), Star(Pos "b1")));; *)

type 'a expr = Epsilon
              | Pos of 'a                (*Position of character*)
              | Or of 'a expr * 'a expr  (* logic "|" *)
              | Con of 'a expr * 'a expr (* logic "." *)
              | Star of 'a expr;;        (* logic "*" *)
           (* | Plus of 'a expr          (* logic "+" *)  *) 
           (* | Que  of 'a expr          (* logic "?" *)  *)





(**** date structure Glushkov automata *)

(* 
type glushkov = {state    : Myset.t; 
                 alphabet : Myset.t; 
                 trans    : (string * string * string) list; 
                 s0       : string; 
                 final    : Myset.t};;
*)

type  glushkov = {state    : string list; 
                  alphabet : string list; 
                  trans    : (string * string * string) list; 
                  s0       : string; 
                  final    : string list};;





(**** convert one-unambiguous regular expression to Glushkov automata *)

(* isEpsilon \in L(E)*)

let rec isEpsilon rexp = match rexp with 
          Epsilon           -> true
        | Pos c             -> false     
        | Or(expr1, expr2)  -> (isEpsilon expr1) || (isEpsilon expr2)
        | Con(expr1, expr2) -> (isEpsilon expr1) && (isEpsilon expr2)
        | Star expr         -> true;;


(* convert exp to star normal form *)

let rec presnf rexp = match rexp with
          Epsilon           -> Epsilon
        | Pos c             -> Pos c     
        | Or(expr1, expr2)  -> Or((presnf expr1), (presnf expr2))
        | Con(expr1, expr2) -> if (not(isEpsilon expr1) && not(isEpsilon expr2)) then Con(expr1, expr2)
                               else if (not(isEpsilon expr1) && (isEpsilon expr2)) then Con((presnf expr1), expr2)
                               else if ((isEpsilon expr1) && not(isEpsilon expr2)) then Con(expr1, (presnf expr2))
                               else Or((presnf expr1), (presnf expr2))
        | Star expr         -> presnf expr;;


let rec snf rexp = match rexp with
          Epsilon           -> Epsilon
        | Pos c             -> Pos c     
        | Or(expr1, expr2)  -> Or((snf expr1), (snf expr2))
        | Con(expr1, expr2) -> Con((snf expr1), (snf expr2))
        | Star expr         -> Star (presnf (snf expr));;


(* pos(E) *)

let mypos = Myset.empty;;

let rec pos rexp = match rexp with
          Epsilon          -> mypos
        | Pos c            -> Myset.add c mypos
        | Or(expr1, expr2) -> Myset.union (pos expr1) (pos expr2)
        | Con(expr1, expr2)-> Myset.union (pos expr1) (pos expr2)
        | Star expr        -> pos expr;;

(* first(E) *) 

let myfirst = Myset.empty;;

let rec first rexp = match rexp with 
          Epsilon          -> myfirst
        | Pos c            -> Myset.add c myfirst
        | Or(expr1, expr2) -> Myset.union (first expr1) (first expr2)
        | Con(expr1, expr2)-> if (isEpsilon expr1) then Myset.union (first expr1) (first expr2)
                              else first expr1
        | Star expr        -> first expr;;


(* last(E) *)

let mylast = Myset.empty;;

let rec last rexp = match rexp with 
          Epsilon          -> mylast
        | Pos c            -> Myset.add c mylast
        | Or(expr1, expr2) -> Myset.union (last expr1) (last expr2)
        | Con(expr1, expr2)-> if (isEpsilon expr2) then Myset.union (last expr1) (last expr2)
                              else last expr2
        | Star expr        -> last expr;;    


(* follow(E, x) *)

(* let myfollow = Myset.empty;;*)
(* exception Error of string;; *)

let rec findfollowx x lst =
    match lst with
       hd::tl -> if (fst hd = x) then snd hd
                 else findfollowx x tl
     |[]-> Myset.empty (* raise (Error ("no"^x))*);;           
    
let rec rmx x lst =
    match lst with 
       hd::tl -> if (fst hd = x) then rmx x tl
                 else hd :: rmx x tl
      |[]->[]               
    
(*let rec follows rexp  = 
    let followset = ref [] in
    match rexp with 
          Epsilon          -> !followset
        | Pos c            -> (c,Myset.empty) :: !followset
        | Or(expr1, expr2) -> !followset
        | Con(expr1, expr2)-> followset := (follows expr1) @ (follows expr2);
                              let l1 = Myset.elements (last expr1) in
                              let n = List.length l1 in
                              for i = 0 to n-1 do
                                  let li = List.nth l1 i in
                                  let si = findfollowx li !followset in
                                  let si' = Myset.union si (first expr2) in
                                  followset := (li, si') :: (rmx li !followset) 
                              done;
                              !followset 
        | Star expr       ->  followset := follows expr;
                              let ss = last expr in
                              let ll = Myset.elements ss in
                              let n = List.length ll in
                              for i = 0 to n-1 do
                                  let lli = List.nth ll i in
                                  let ssi = findfollowx lli !followset in
                                  let ssi' = Myset.union ssi (first expr) in
                                  followset := (lli, ssi') :: (rmx lli !followset) 
                              done; 
                              !followset;; *)




(* postorder *)

let rec postorder rexp = match rexp with 
          Epsilon          -> [" "]
        | Pos c            -> [c]
        | Or(expr1, expr2) -> postorder expr1 @ postorder expr2 @ ["|"]
        | Con(expr1, expr2)-> postorder expr1 @ postorder expr2 @ ["."]
        | Star expr        -> postorder expr @ ["*"];;



(* (yi, er, san, si): isempty and three sets: first(set) last(set) follow(string*set list) *)
let deal rexp =
    let oplst = ["|"; "."; "*"] in 
    let e = postorder rexp in
    let myfst = Myset.empty in
    let mylst = Myset.empty in
    let myflw = Myset.empty in
    let sisk = Stack.create () in
    let sfst = Stack.create () in
    let slst = Stack.create () in
    let lflw = ref [] in
    let le = List.length e in
    for i = 0 to le-1 do
        let x = List.nth e i in
        if(not(List.mem x oplst)) 
          then if(not(x = " ")) then begin
                                         Stack.push false sisk;
                                         Stack.push (Myset.add x myfst) sfst;
                                         Stack.push (Myset.add x mylst) slst; 
                                         lflw := (x, myflw) :: !lflw;
                                         end   
               else begin
                    Stack.push true sisk;
                    Stack.push myfst sfst;
                    Stack.push mylst slst; 
                    end
        else if (x = "|") then begin
                               let risk = Stack.pop sisk in
                               let lisk = Stack.pop sisk in
                               let rfst = Stack.pop sfst in
                               let lfst = Stack.pop sfst in
                               let rlst = Stack.pop slst in
                               let llst = Stack.pop slst in
                               Stack.push (risk || lisk) sisk;
                               Stack.push (Myset.union rfst lfst) sfst;
                               Stack.push (Myset.union rlst llst) slst;
                               end
        else if (x = ".") then begin 
                               let risk = Stack.pop sisk in
                               let lisk = Stack.pop sisk in
                               let rfst = Stack.pop sfst in
                               let lfst = Stack.pop sfst in
                               let rlst = Stack.pop slst in
                               let llst = Stack.pop slst in                               
                               let ll = Myset.elements llst in
                               let len = List.length ll in
                               Stack.push (risk && lisk) sisk;                               
                               for j = 0 to len-1 do
                                   let xj= List.nth ll j in
                                   let fxj = findfollowx xj !lflw in
                                   lflw := rmx xj !lflw;
                                   lflw := (xj, (Myset.union fxj rfst)) :: !lflw; 
                               done;                               
                               if(lisk) then Stack.push (Myset.union rfst lfst) sfst
                               else Stack.push lfst sfst;                               
                               if(risk) then Stack.push (Myset.union rlst llst) slst
                               else Stack.push rlst slst;     
                               end                               
        else if (x = "*") then begin 
                               let _= Stack.pop sisk in
                               Stack.push true sisk;
                               let fst = Stack.top sfst in
                               let lst = Stack.top slst in
                               let ll = Myset.elements lst in
                               let lgt = List.length ll in
                               for k = 0 to lgt-1 do
                                   let xk= List.nth ll k in
                                   let fxk = findfollowx xk !lflw in
                                   lflw := rmx xk !lflw;
                                   lflw := (xk, (Myset.union fxk fst)) :: !lflw; 
                               done;                                
                               end                         
    done;     
    (Stack.pop sisk, Stack.pop sfst, Stack.pop slst, !lflw);; 




(* unmark(x) *)

(* let unmark str = String.sub str 0 (String.length str -1);; *)
let unmark str = String.sub str 0 (String.index str '-');;

(* let unsym str = String.sub str (String.index str '-') (String.length str);; *)
let unsym str =
  let start_index = String.index str '-' + 1 in
  let sub_length = String.length str - start_index in
  String.sub str start_index sub_length

let mysym = Myset.empty;;

let rec sym rexp = match rexp with
          Epsilon           -> mysym
        | Pos c             -> Myset.add (unmark c) mysym     
        | Or(expr1, expr2)  -> Myset.union (sym expr1) (sym expr2)
        | Con(expr1, expr2) -> Myset.union (sym expr1) (sym expr2)
        | Star expr         -> sym expr;;


(******************************** derivative based method **********************************)

let rec isnull rexp = 
  match rexp with 
          Epsilon           -> false
        | Pos c             -> if (c = "null") then true 
                               else false     
        | Or(expr1, expr2)  -> if (isnull expr1) then isnull expr2
                               else true
        | Con(expr1, expr2) -> isnull expr1
        | Star expr         -> isnull expr;;

(* derivative of the expression *)

let rec der rexp a =
    let null = Pos "null" in 
    match rexp with
          Epsilon           -> null
        | Pos c             -> if c = "null" then null
                                else if a = c then Epsilon 
                               else null
        | Or(expr1, expr2)  -> if (not(isnull (der expr1 a)))
                                  then der expr1 a
                               else der expr2 a
        | Con(expr1, expr2) -> if (not(isnull (der expr1 a)))
                                  then Con((der expr1 a), expr2) 
                               else der expr2 a
        | Star expr         -> Con((der expr a), Star expr) 

(* leading name of E *)

let ldn rexp = 
    let rec isnull e = 
        match e with 
          Epsilon           -> false
        | Pos c             -> if (c = "null") then true 
                               else false     
        | Or(expr1, expr2)  -> isnull expr1
        | Con(expr1, expr2) -> isnull expr1
        | Star expr         -> isnull expr 
    in
    let myldn = ref [] in
    let symlst = Myset.elements (pos rexp) in
    let numsymlst = List.length symlst in
    for i = 0 to numsymlst - 1 do
       let a = List.nth symlst i in
       if(not(isnull(der rexp a)))
         then myldn := a :: !myldn
    done;
    !myldn
    


let interset (l1:string list) (l2:string list) : string list=
  let hash_table = Hashtbl.create (List.length l1) in
  List.iter (fun x -> Hashtbl.add hash_table (unmark x) ()) l1;
  let result_set = ref [] in
  List.iter (fun x -> if Hashtbl.mem hash_table (unmark x) then result_set := (unmark x) :: !result_set) l2;
  List.rev !result_set

let find_pos c l = 
  List.filter (fun x -> (unmark x) = c) l
  
(********************************* Brzozowski Automata ************************************) 

(* Md(E) = (D(E), alphabet, dd, E, {p \in D(E) | epsilon \in L(p)}) *) 
let rec e2s rexp = 
  match rexp with
        Epsilon           -> "epsilon"
      | Pos c             -> c
      | Or(expr1, expr2)  -> "(" ^ e2s expr1 ^ "|" ^ e2s expr2 ^ ")"
      | Con(expr1, expr2) -> e2s expr1 ^ e2s expr2 
      | Star expr         -> "(" ^ e2s expr ^ ")*" ;;
let rec e2nat rexp =
    match rexp with
        Epsilon           -> "epsilon"
      | Pos c             -> unmark c
      | Or(expr1, expr2)  -> "(" ^ e2nat expr1 ^ "|" ^ e2nat expr2 ^ ")"
      | Con(expr1, expr2) -> e2nat expr1 ^ e2nat expr2 
      | Star expr         -> "(" ^ e2nat expr ^ ")*" ;;

let rec e2natinline rexp =
    match rexp with
        Epsilon           -> ""
      | Pos c             -> unmark c
      | Or(expr1, expr2)  -> "(" ^ e2natinline expr1 ^ "|" ^ e2natinline expr2 ^ ")"
      | Con(expr1, expr2) -> e2natinline expr1 ^ e2natinline expr2 
      | Star expr         -> "(" ^ e2natinline expr ^ ")*" ;;

let getba rexp = 
    let translst = ref [] in
    let final = ref [] in
    let bs = ref [e2s rexp] in
    let temps = ref [rexp] in
    let newstates = ref [e2s rexp] in
    while(not(List.length !newstates = 0)) do
         newstates := [];
         let newtp = ref [] in
         let lentps = List.length !temps in
         for i = 0 to lentps-1 do
             let tempi = List.nth !temps i in
             if (isEpsilon tempi) then final := (e2s tempi) :: !final; 
             let ldnlst = ldn tempi in
             let lengthldn = List.length ldnlst in
             for j = 0 to lengthldn-1 do
                 let ldnj = List.nth ldnlst j in
                 let derij = der tempi ldnj in
                 let sij = e2s derij in
                 if(not(List.mem sij !bs)) 
                   then begin
                        newstates := sij :: !newstates;
                        newtp := derij :: !newtp; 
                        end;
                 translst := !translst @ [(e2s tempi, unmark ldnj, sij)];         
             done; 
         done;
         bs := !bs @ !newstates;
         temps := !newtp;
    done;
    (!bs, (!translst, !final));;
(* let s = "(a1.b2.c3?)*";; *)    
    


let brzoauto rexp = 
    let ba = getba rexp in
    { state   = fst ba;
     alphabet = Myset.elements (sym rexp);
     trans    = fst(snd ba);
     s0       = e2s rexp;                
     final    = snd (snd ba);
    };;
    
(*******************************************************************************************)


let getyi = function (yi, er, sa, si) -> yi
   
let geter = function (yi, er, sa, si) -> er 

let getsa = function (yi, er, sa, si) -> sa 

let getsi = function (yi, er, sa, si) -> si

let follow x s = findfollowx x (getsi s)

(* a \in alphabet, (qI, a, {x | x \in first(E),unmark(x) =a}) *)

let gettrans1 rexp sets = 
    let translist = ref [] in
    let listsym = Myset.elements (sym rexp) in
    let listfirst = Myset.elements (geter sets) in
    let numsym = List.length listsym in
    let numfirst = List.length listfirst in
    for i = 0 to numsym - 1 do
        let a = List.nth listsym i in
        for j = 0 to numfirst - 1 do 
            let x = List.nth listfirst j in
            if (unmark x = a)
                then  translist := ("qI", a, x )::!translist
            else () 
        done; 
    done;
    !translist;;    


(* x \in pos(E), a \in alphabet, (x, a, {y | y \in follow(E, x),unmark(y) =a}) *)
     
let gettrans2 rexp sets = 
    let translist = ref [] in
    let listpos = Myset.elements (pos rexp) in
    let listsym = Myset.elements (sym rexp) in
    let numpos = List.length listpos in
    let numsym = List.length listsym in
    for i = 0 to numpos - 1 do
        let x = List.nth listpos i in
        let fx = follow x sets in
        for j = 0 to numsym - 1 do 
            let a = List.nth listsym j in
            let listfollow = Myset.elements fx in
            let numfollow = Myset.cardinal fx in
            for k = 0 to numfollow - 1 do 
                let y = List.nth listfollow k in
                if (unmark y = a)
                   then translist := (x, a, y )::!translist
                else ()
            done; 
        done; 
     done;
     !translist;;
 
  
(* is rexp determined *)
 
(* first *) 
let isDet1 rexp = 
    let result = ref true in
    let mytemp = Myset.empty in
    let mt = ref mytemp in
    let ft = first rexp in
    let listft = Myset.elements ft in
    let numft = List.length listft in
    for i = 0 to numft -1 do
        let y = List.nth listft i in
        mt := Myset.add (unmark y) !mt;
    done;
    if ((Myset.cardinal !mt) < numft) then result := false;
    !result;;

    
(* follow *)    
let isDet2 rexp sets = 
    let result = ref true in
    let mytemp = Myset.empty in
    let listpos = Myset.elements (pos rexp) in
    let numpos = List.length listpos in
    for i = 0 to numpos - 1 do
        let x = List.nth listpos i in
        let fx = follow x sets in
        let listfollow = Myset.elements fx in
        let numfollow = Myset.cardinal fx in
        let mt = ref mytemp in
        for k = 0 to numfollow - 1 do 
            let y = List.nth listfollow k in
            mt := Myset.add (unmark y) !mt;
        done;
        if ((Myset.cardinal !mt) < numfollow) then result := false; 
    done;
    !result;;
    
let isDet rexp sets = (isDet1 rexp) && (isDet2 rexp sets);;
    
   
(* convert the expression to automata *)       

let automata rexp sets = 
                    {state   = Myset.elements (Myset.add "qI" (pos rexp));
                    alphabet = Myset.elements (sym rexp);
                    trans    = (gettrans1 rexp sets) @ (gettrans2 rexp sets);
                    s0       = "qI";                
                    final    = let lastrexp = getsa sets in
                               if (getyi sets) then Myset.elements (Myset.add "qI" lastrexp)
                               else Myset.elements lastrexp
                    };;




(**** M': the complement of automata M *)

(* add trans to trap *)

(*
let getonetwo tr = match tr with 
    (one, two, three) -> (one, two)
   | _                -> raise (Failure "Error");; 
*)

let getonetwo = function (one,two,_) -> (one, two);;

let addtrap ltrans lstate lalpha = 
    let b = ref true in
    let temptrans =ref ltrans in
    let numlstate = List.length lstate in
    let numlalpha = List.length lalpha in
    let onetwotr = List.map getonetwo ltrans in
    for i = 0 to numlstate - 1 do
        let s = List.nth lstate i in
        for j = 0 to numlalpha - 1 do
            let a = List.nth lalpha j in
            if (List.mem (s, a) onetwotr) then ()
            else begin 
                 temptrans :=  (s, a , "trap"):: !temptrans;
                 b := false;
                 end;               
        done;
    done;    
    if (not(!b)) then 
       for j = 0 to numlalpha - 1 do
           let a = List.nth lalpha j in
           temptrans := ("trap", a, "trap"):: !temptrans;
       done;
    !temptrans;;
   
(* final state of the complement of automate *)

let finalcom auto = 
    let tempfinal = ref [] in
    let lstate = auto.state in
    let lfinal = auto.final in
    let numlstate = List.length lstate in
    for i = 0 to numlstate - 1 do
        let s = List.nth lstate i in
        if (List.mem s lfinal) then ()
        else tempfinal := s :: !tempfinal
    done;
    !tempfinal;;

(**** M_12: the intersection M_1 and M_2 *)

(*
let conc interstate = match interstate with
    (one, two) -> one ^ two
   | _         -> raise (Failure "Error");; 
*)

(*
let conc = function (one, two) -> one ^ two;;
*)


(* S = S1 ＊ S2, F = F1 ＊ F2*)

let interstate lst1 lst2 = 
    let rec map1 x ls = match ls with 
            []       -> []
          | hd :: tl -> (x ^ hd) :: (map1 x tl) 
    in
    let rec map2 ls1 ls2 = match ls1 with
            []       -> []
          | hd :: tl -> (map1 hd ls2) @ (map2 tl ls2) 
    in 
    map2 lst1 lst2;;


(* trans((t1, t2), a) = (trans1(t1, a), trans2(t2, a)) *)    
(*
let intertrans trs1 trs2 =
    let get1 = function (one, two, three) -> one in
    let get2 = function (one, two, three) -> two in
    let get3 = function (one, two, three) -> three in 
    let rec trmap1 x tr = match tr with
            []       -> []
          | hd :: tl -> if (get2 x = get2 hd) 
                           then ((get1 x)^(get1 hd), get2 x, (get3 x)^(get3 hd)) :: (trmap1 x tl)
                        else trmap1 x tl
    in 
    let rec trmap2 tr1 tr2 = match tr1 with
           []       -> []
         | hd :: tl -> (trmap1 hd tr2) @ (trmap2 tl tr2)  
    in
    trmap2 trs1 trs2;;
*)
           
                        
let intertrans trs1 trs2 =
    let q = Queue.create () in
    (*let t = ref [] in*)
    let temq = ref [] in
    let inttrans = ref [] in
    Queue.add ("qI","qI") q;
    let get1 = function (one, two, three) -> one in
    let get2 = function (one, two, three) -> two in
    let get3 = function (one, two, three) -> three in 
    (* find trs1 start from fst q.top *)
    let rec finds q1 tr = match tr with
            []       -> []
          | hd :: tl -> if(q1 = get1 hd) 
                          then [hd] @ finds q1 tl
                          else finds q1 tl
    in  
    let rec findrs q2 tr trs = match trs with
            []       -> []
          | hd :: tl -> if((q2 = get1 hd) && (get2 tr = get2 hd)) 
                          then [((get1 tr)^q2, (get2 tr), (get3 tr, get3 hd))] @ findrs q2 tr tl
                          else findrs q2 tr tl
    in   
    let rec deal ts = match ts with 
            []       -> []
          | hd :: tl -> [(get1 hd), (get2 hd), (fst(get3 hd))^(snd(get3 hd))] @ deal tl
    in             
    while(not(Queue.is_empty q)) do
       (* find trs1 start from fst q.top *)
       let states = finds (fst (Queue.top q)) trs1 in  
         (* for each find trs2 from snd q.top ; push q states *)
       let l = List.length states in
       for i = 0 to l - 1 do
           let s = List.nth states i in
           let ts = findrs (snd (Queue.top q)) s trs2 in
           let lts = List.length ts in
           for j = 0 to lts -1 do
               let tq = get3(List.nth ts j) in
               if (not(List.mem tq !temq)) then 
               begin Queue.add tq q; temq := tq :: !temq; end   
           done;
           inttrans := !inttrans @ (deal ts);
       done;
      (* pop top*)
      let pq = Queue.pop q in
      (*t := pq :: !t ;*)
      temq := pq :: !temq;
    done;
    !inttrans;;

(* intersection of alphabets *)    

let interalpha alp1 alp2 = 
    let lsset = Myset.empty in
    let rec ls2set ls =
            match ls with 
                  []       -> lsset
	        | hd :: tl -> Myset.union (Myset.add hd lsset) (ls2set tl) 
    in
    Myset.elements (Myset.union (ls2set alp1) (ls2set alp2));; 
    

(* intersection of two automata *)

let intersection auto1 auto2 = { state    = interstate auto1.state auto2.state;
                                 alphabet = interalpha auto1.alphabet auto2.alphabet;           
                                 trans    = intertrans auto1.trans auto2.trans;
                                 s0       = auto1.s0 ^ auto2.s0;
                                 final    = interstate auto1.final auto2.final;
                               };;





(**** isEmpty of M *)

(* find next states *)

let rec findns s tr = 
        let get1 = function (one, two, three) -> one in
        let get3 = function (one, two, three) -> three in
        match tr with 
              []       -> []
            | hd :: tl -> if(s = get1 hd) then [get3 hd] @ findns s tl
                          else findns s tl;;

      
(* is a list1 element in the list2 *)

let rec infinal lst1 lst2 = match lst1 with
        []       -> false 
      | hd :: tl -> List.mem hd lst2 || infinal tl lst2;; 
      

(* get the set of reached states *)

let rec findrs tr =  
    let setrs = Myset.empty in
    let get3 = function (one, two, three) -> three in
    match tr with 
              []       -> setrs
            | hd :: tl -> Myset.add (get3 hd) (findrs tl);;                         


(* is the automata Empty *)                           
(*
let isEmpty auto = 
    if List.mem auto.s0 auto.final then false              
    else if((List.length auto.trans) = 0) then false       
    else
       let b = ref true inNode of 'a * 'a btree * 'a btree;;

(* op list *)

let oplst = ["("; ")"; "|"; "."; "*"; "?"; "+"];;



(* find op value *)
       let visit = ref [auto.s0] in                         
       let qtrans = ref (Queue.create ()) in
       Queue.add auto.s0 !qtrans;
       while (not(Queue.is_empty !qtrans) && !b) do
             let qi = Queue.take !qtrans in
             if (infinal (findns qi auto.trans) auto.final) 
                then b := false  
             else 
             let ns = ref (findns qi auto.trans) in
             while (List.length !ns > 0) do                 
                 if (not(List.mem (List.hd !ns) !visit)) then 
                    begin
                    Queue.add (List.hd !ns) !qtrans;
                    visit := (List.hd !ns):: !visit;        
                    end
                 else ();
                 ns := List.tl !ns;
             done;   
       done;
       !b;;  

let isEmpty auto = if (infinal (Myset.elements (findrs auto.trans)) auto.final) 
                      then false
                   else true;;
*)

let isEmpty trans fs = if (infinal ("qIqI"::(Myset.elements (findrs trans))) fs) 
                          then true
                       else false;;
(* GA inclusion *)                       
                       
let gainc e1 e2 =
  let s1 = deal e1 in
  let s2 = deal e2 in
  let a1 = automata e1 s1 in
  let a2 = automata e2 s2 in
  let trans12 = intertrans a1.trans a2.trans in
  let fs12 = interstate a1.final a2.final in
  isEmpty trans12 fs12;;                       

(**** convert the input string to the type expr *)

(* deal with while after 'P' *)

let readin inchan = 
        let ps = ref "" in
        let ch = ref (input_char inchan) in
        while(not(!ch = 'C') &&  
              not(!ch = 'P') && 
              not(!ch = 'E') && 
              not(!ch = 'S') && 
              not(!ch = 'O') && 
              (in_channel_length inchan <> pos_in inchan) ) do
              ps := !ps ^ (String.make 1 !ch);
              ch := input_char inchan;
        done;
        seek_in inchan (pos_in inchan - 1);
        !ps;;


(* read expr from file  *)

let rec change in_chan  = match input_char in_chan with 
         'C' -> Con(change in_chan, change in_chan)
        |'P' -> Pos(readin in_chan)
        |'E' -> Epsilon
        |'S' -> Star(change in_chan)
        |'O' -> Or(change in_chan, change in_chan)
        | _  -> raise (Failure "empty");; 


(* modify the expr *)

let rec change2 rexp = match rexp with 
          Epsilon          -> Epsilon
        | Pos c            -> Pos c
        | Or(expr1, expr2) -> Or(change2 expr2, change2 expr1)
        | Con(expr1, expr2)-> Con(change2 expr2, change2 expr1)
        | Star expr        -> Star(change2 expr);;




(**** print the automata *)

(* print string list *)

let rec print_list lst = match lst with 
        []       -> ()
      | hd :: tl -> print_string (hd ^ " ") ; print_list tl;;
  

(* print trans (string * string * string list) *)
     
let rec print_trans trs = 
        let print_one = function (one, two, three) -> print_string one in 
        let print_two = function (one, two, three) -> print_string two in 
        let print_three = function (one, two, three) -> print_string three in 
        match trs with 
        []       -> ()
      | hd :: tl -> print_string "("; print_one hd; print_string ", "; 
                                      print_two hd; print_string ", ";
                                      print_three hd; print_string ")\n  ";
                      print_trans tl;;  


(* print automata *)

let print_auto  auto = (*print_string "\nGlushkov automata: \n";*)
                       print_string "state:\n  "; print_list auto.state; print_string "\n";
                       print_string "alphabet:\n  "; print_list auto.alphabet; print_string "\n";
                       print_string "trans:\n  "; print_trans auto.trans; print_string "\n";
                       print_string "s0:\n  "; print_string auto.s0; print_string "\n";
                       print_string "final:\n  "; print_list auto.final;
                       print_string "\n";;


let rec print_expr rexp = match rexp with
          Epsilon          -> print_string "epsilon"
        | Pos c            -> print_string ("Pos \""^ c ^ "\"")
        | Or(expr1, expr2) -> print_string "Or(";print_expr expr1; print_string ", ";print_expr expr2; print_string ")"
        | Con(expr1, expr2)-> print_string "Con(";print_expr expr1; print_string ", ";print_expr expr2; print_string ")"
        | Star expr        -> print_string "Star(";print_expr expr;print_string ")";;

(**** convert the input string to expr *)

(* let s1 = "(a1|b1)*.a2.(a3.b2)*";; *) 
(* let s2 = "(a1|b1)*";; *)  
(* let s3 = "(b1*.a1)*";; *) 
(* let s4 = "(a1*.b1* )*";; *)


(* binary tree *)

type  'a btree = Empty
                |Node of 'a * 'a btree * 'a btree;;

(* op list *)

let oplst = ["("; ")"; "|"; "."; "*"; "?"; "+"];;



(* find op value *)

let rec findov str k = 
    let ov = ref "" in
    let substr = (String.sub str k 1) in 
    if (not(List.mem substr oplst)) 
       then if (k < String.length str - 1 )
               then ov := !ov ^ substr ^ (findov str (k + 1))
            else ov := !ov ^ substr;
    !ov;;  


(* convert string(infix) to list(op and ov) *)

let str2lst str = 
        let i = ref 0 in
        let lst = ref [] in
        while (!i < String.length str) do
              let substr = String.sub str !i 1 in
              (* print_endline substr; *)
              if (List.mem substr oplst) 
                 then begin  
                      (* print_endline "op"; *)
                      lst := !lst @ [substr];
                      i := !i + 1;
                      end
              else begin
                    (* print_endline "ov"; *)
                   let ov = findov str !i in
                   lst := !lst @ [ov]; 
                   i := !i + String.length ov;
                   end 
        done;
        !lst;;

(* convert btree to rexp *) 

let rec btree2exp btr = match btr with 
        Empty -> Epsilon
      | Node(node, left, right) -> if (node = "|") then Or( (btree2exp left) , (btree2exp right))
                                   else if (node = ".") then Con( (btree2exp left) , (btree2exp right))  
                                   else if (node = "*") then Star (btree2exp right)
                                   else Pos node;;

let print_stack stk = 
        let print_one = function (one) -> print_string one in 
        Stack.iter print_one stk;;

let print_btreeStack stk = 
        let print_one = function (one) -> print_expr (btree2exp one) in
        Stack.iter print_one stk;;

(* construct btree from list *)

let rec lst2btree lst = 
        (* print_list lst; *)
        let btr = ref Empty in
        let sop = Stack.create ()in
        let sbtr = Stack.create ()in
        let i = ref 0 in
        let lp = ref "" in
        Stack.push "#" sop;
        if (List.length lst = 0) then ()
        else begin
             while(!i < (List.length lst)) do
                  let ch = List.nth lst !i in
                  (* print_endline "\nch: ";
                  print_string ch; *)
                  if (not(List.mem ch oplst) && ch = "@") then        (* input is ov *)
                     let cht = Empty in 
                     Stack.push cht sbtr;               
                     (* print_endline "\nin @"; *)
                  else if (not(List.mem ch oplst) && ch != "@") then        (* input is ov *)
                     let cht = Node(ch, Empty, Empty) in 
                     Stack.push cht sbtr;
                     (* print_endline "\nin ov"; *)
                     (* print_endline "cht: ";
                     print_expr (btree2exp cht); *)
                  else    (* input is op *)
                      if (ch = "(") then 
                        begin
                        Stack.push ch sop; (* push "(" *)
                        (* print_endline "\nin ("; *)
                        end
                      else if (ch = ")") then 
                           begin
                           (* print_endline "\nin )"; *)
                           while(not(Stack.top sop = "(")) do                                
                                let right = Stack.pop sbtr in (* stack pop do right first *)
                                let left = Stack.pop sbtr in
                                let root = Stack.pop sop in
                                btr := Node(root, left, right); 
                                Stack.push !btr sbtr; (* push the result *)           
                           done;
                           lp := Stack.pop sop;   (* pop "(" *)
                           end
                      else if (ch = "*") then 
                           begin
                            (* print_endline "\nin *"; *)
                           let right = Stack.pop sbtr in
                           btr := Node("*", Empty, right);
                           Stack.push !btr sbtr; (* push the result *)
                           end
                      else if (ch = "+") then
                           begin     
                            (* print_endline "\nin +"; *)
                           let right = Stack.pop sbtr in
                           btr := Node(".", right, Node("*", Empty, right));
                           Stack.push !btr sbtr; (* push the result *)
                           end
                      else if (ch = "?") then
                           begin     
                            (* print_endline "\nin ?"; *)
                           let left = Stack.pop sbtr in
                           btr := Node("|", left, Empty);
                           Stack.push !btr sbtr; (* push the result *)
                           end     
                      else if ((Stack.top sop) = "|" || (Stack.top sop) = ".") then 
                           begin 
                            (* print_endline "\nin | or ."; *)
                           let right = Stack.pop sbtr in 
                           let left = Stack.pop sbtr in
                           let root = Stack.pop sop in
                           btr := Node(root, left, right);
                           Stack.push !btr sbtr; (* push the result *)
                           Stack.push ch sop;   (* push "|" or "." *)
                           end
                      else begin
                        (* print_endline "\nin else"; *)
                        Stack.push ch sop; (* push "|" or "." *)
                        end;
                  i := !i + 1;    
                  (* print_endline "\nsop:";
                  print_stack sop;
                  print_endline "\nsbtr:";
                  print_btreeStack sbtr;
                  print_endline "\n"; *)
             done;
             (* print_endline "\nsop:";
             print_stack sop;
             print_endline "\nsbtr:";
             print_btreeStack sbtr;
             print_endline "\n"; *)
             while(not(Stack.top sop = "#")) do
                  (* print_endline "\n(inside while:"; *)
                  let right = Stack.pop sbtr in 
                  let left = Stack.pop sbtr in
                  let root = Stack.pop sop in
                  btr := Node(root, left, right);
                  Stack.push !btr sbtr; (* push the result *)
                  (* print_endline "\nsop:";
                  print_stack sop;
                  print_endline "\nsbtr:";
                  print_btreeStack sbtr; *)
             done;
             end;
        Stack.top sbtr;; (* !btr;; *)          
        

let s2e x= btree2exp(lst2btree(str2lst x));;

(* print Myset *)
let print_myset set = 
  let print_one = function (one) -> (print_string one; print_string " ") in 
  Myset.iter print_one set;;

(* int to string *)

let set2s set1 set2 =
  (* print_string "in set2s\nset1: ";
  print_myset set1;
  print_string "\nset2: ";
  print_myset set2;
  print_string "\n"; *)
  let s1 = ref "" in
  let s2 = ref "" in
  if Myset.is_empty set1 then 
    begin
      (* print_string "set1 is empty\n"; *)
      s1 := "null"
    end
  else 
    begin
      (* print_string  "set1 is not empty\n"; *)

      s1 := String.concat " " (Myset.fold (fun s acc -> unsym s :: acc) set1 []);
      (* print_string "s1: ";
      print_string !s1;
      print_string "\n"; *)
    end;
  if Myset.is_empty set2 then 
    begin
      (* print_string "set2 is empty\n"; *)
      s2 := "null"
    end
  else 
    begin
      (* print_string  "set2 is not empty\n"; *)
      s2 := String.concat " " (Myset.fold (fun s acc -> unsym s :: acc) set2 []);
    end;
!s1 ^ "@" ^ !s2;;

let intermyset (l1:Myset.t) (l2:Myset.t) : Myset.t =
  let hash_table = Hashtbl.create (Myset.cardinal l1) in
  Myset.iter (fun x -> Hashtbl.add hash_table (unmark x) ()) l1;
  let result_set = ref Myset.empty in
  Myset.iter (fun x -> if Hashtbl.mem hash_table (unmark x) then result_set := Myset.add (unmark x) !result_set) l2;
  !result_set

let find_pos_myset c l = 
  Myset.filter (fun x -> unmark x = c) l

let rec natural rexp = match rexp with
          Epsilon           -> Epsilon
        | Pos c             -> Pos(unmark c)
        | Or(expr1, expr2)  -> Or(natural expr1, natural expr2)
        | Con(expr1, expr2) -> Con(natural expr1, natural expr2)
        | Star expr         -> Star(natural expr);;

let ccon_intersect expr1 expr2 aa = 
  let last1 = last expr1 in
  let last2 = last expr2 in
  let rec ccon_recur ccon1 ccon2 aa =
    let first1 = first ccon1 in
    let first2 = first ccon2 in
    let commonfirst = intermyset first1 first2 in
    (*print_list commonfirst; print_string" ";*)
    if not (Myset.cardinal commonfirst = 0) then
      let cardcommon = Myset.cardinal commonfirst in
      let rec loop i =
        if i >= cardcommon then
          false
        else
          let a = List.nth (Myset.elements commonfirst) i in
          let p1 = Myset.elements(find_pos_myset a first1) in
          let p2 = Myset.elements(find_pos_myset a first2) in
          let rec loop1 j = 
            if j >= List.length p1 then
              loop(i+1)
            else
              let m = List.nth p1 j in
              let c1 = der ccon1 m in
              (*print_string m;*)
              let rec loop2 k =
                if k >= List.length p2 then
                  loop1(j+1)
                else
                  let n = List.nth p2 k in
                  let c2 = der ccon2 n in
                  if((Myset.mem m last1 && Myset.mem n last2)) then 
                    true
                  else
                    let nat1 = e2s c1 in
                    let nat2 = e2s c2 in
                    if(Myset.mem (nat1 ^","^ nat2) aa) then 
                    loop2(k+1)
                  else
                    let bb = Myset.add (nat1 ^","^ nat2) aa in
                    if (ccon_recur c1 c2 bb) then
                      true
                    else
                      loop2(k+1)
            in
              loop2 0
          in
            loop1 0
      in
      loop 0
    else
      false
  in

  if((isEpsilon expr1) && (isEpsilon expr2))
    then true
  else if (Myset.is_empty(intermyset last1 last2)) then false
    else ccon_recur expr1 expr2 (Myset.add (e2s expr1^","^e2s expr2) aa)

let equa_intersect expr1 expr2 aa = 
  let last1 = last expr1 in
  let last2 = last expr2 in
  let rec equa_recur ccon1 ccon2 aa =
    let first1 = first ccon1 in
    let first2 = first ccon2 in
    let commonfirst = intermyset first1 first2 in
    (*print_list commonfirst; print_string" ";*)
    if not (Myset.cardinal commonfirst = 0) then
      let cardcommon = Myset.cardinal commonfirst in
      let rec loop i =
        if i >= cardcommon then
          false
        else
          let a = List.nth (Myset.elements commonfirst) i in
          let p1 = Myset.elements(find_pos_myset a first1) in
          let p2 = Myset.elements(find_pos_myset a first2) in
          let rec loop1 j = 
            if j >= List.length p1 then
              loop(i+1)
            else
              let m = List.nth p1 j in
              let c1 = der ccon1 m in
              (*print_string m;*)
              let rec loop2 k =
                if k >= List.length p2 then
                  loop1(j+1)
                else
                  let n = List.nth p2 k in
                  let c2 = der ccon2 n in
                  if((Myset.mem m last1 && Myset.mem n last2)) then 
                    true
                  else
                    let nat1 = e2natinline c1 in
                    let nat2 = e2natinline c2 in
                    
                    if(Myset.mem (nat1 ^","^ nat2) aa) then 
                    loop2(k+1)
                  else
                    let bb = Myset.add (nat1 ^","^ nat2) aa in
                    if (equa_recur c1 c2 bb) then
                      true
                    else
                      loop2(k+1)
            in
              loop2 0
          in
            loop1 0
      in
      loop 0
    else
      false
  in

  if((isEpsilon expr1) && (isEpsilon expr2))
    then true
  else if (Myset.is_empty(intermyset last1 last2)) then false
    else equa_recur expr1 expr2 (Myset.add (e2natinline expr1^","^e2natinline expr2) aa)

let altfa_intersect expr1 expr2 aa = 
    (* print_string "altfa_intersect(\n\texpr1:"; print_string (e2s expr1); print_string "\n,\n\texpr2"; print_string (e2s expr2); print_string "\n,\n\taa:"; print_list (Myset.elements aa); print_string "\n)\n"; *)
    let last1 = last expr1 in
    let last2 = last expr2 in
    let rec fa_recur ccon1 ccon2 aa =
      (* print_string "fa_recur(\n\tccon1:"; print_string (e2s ccon1); print_string "\n,\n\tccon2"; print_string (e2s ccon2); print_string "\n,\n\taa:"; print_list (Myset.elements aa); print_string "\n)\n"; *)
      let first1 = first ccon1 in
      let first2 = first ccon2 in
      let commonfirst = intermyset first1 first2 in
      (* print_string "commonfirst:"; print_list (Myset.elements commonfirst); print_string "\n"; *)
      (*print_list commonfirst; print_string" ";*)
      if not (Myset.cardinal commonfirst = 0) then
        let cardcommon = Myset.cardinal commonfirst in
        let rec loop i =
          (* print_string "loop("; print_int i; print_string ")\n"; *)
          if i >= cardcommon then
            false
          else
            let a = List.nth (Myset.elements commonfirst) i in
            let p1 = Myset.elements(find_pos_myset a first1) in
            let p2 = Myset.elements(find_pos_myset a first2) in
            let rec loop1 j = 
              (* print_string "loop1("; print_int j; print_string ")\n"; *)
              if j >= List.length p1 then
                loop(i+1)
              else
                let m = List.nth p1 j in
                let c1 = der ccon1 m in
                (*print_string m;*)
                let rec loop2 k =
                  (* print_string "loop2("; print_int k; print_string ")\n"; *)
                  if k >= List.length p2 then
                    loop1(j+1)
                  else
                    let n = List.nth p2 k in
                    (* print_string "ready to der\n"; *)
                    let c2 = der ccon2 n in
                    (* print_string "der done\n"; *)
                    if((Myset.mem m last1 && Myset.mem n last2)) then 
                      begin
                        (* print_string "m in last1 and n in last2\n"; *)
                        true
                      end
                    else 
                      begin
                        (* print_string "m not in last1 or n not in last2\n"; *)
                        let tuple = (set2s first1 first2) in
                        (* print_string  "tuple:"; print_string tuple; print_string "\n"; *)
                        if(Myset.mem tuple aa) then 
                          begin
                            (* print_string "tuple in aa\n"; *)
                            loop2(k+1)
                          end
                        else begin
                          (* print_string "tuple not in aa\n"; *)
                          let bb = Myset.add tuple aa in
                          if (fa_recur c1 c2 bb) then
                            true
                          else
                            loop2(k+1)
                        end
                      end
              in
                loop2 0
            in
              loop1 0
        in
        loop 0
      else
        false
    in

    if((isEpsilon expr1) && (isEpsilon expr2))
      then true
    else if (Myset.is_empty(intermyset last1 last2)) then false
      else fa_recur expr1 expr2 aa

let altfo_intersect expr1 expr2 aa = 
    let last1 = last expr1 in
    let last2 = last expr2 in
    let rec fo_recur ccon1 ccon2 aa =
      let first1 = first ccon1 in
      let first2 = first ccon2 in
      let commonfirst = intermyset first1 first2 in
      (*print_list commonfirst; print_string" ";*)
      if not (Myset.cardinal commonfirst = 0) then
        let cardcommon = Myset.cardinal commonfirst in
        let rec loop i =
          if i >= cardcommon then
            false
          else
            let a = List.nth (Myset.elements commonfirst) i in
            let p1 = Myset.elements(find_pos_myset a first1) in
            let p2 = Myset.elements(find_pos_myset a first2) in
            let rec loop1 j = 
              if j >= List.length p1 then
                loop(i+1)
              else
                let m = List.nth p1 j in
                let c1 = der ccon1 (m) in
                (*print_string m;*)
                let rec loop2 k =
                  if k >= List.length p2 then
                    loop1(j+1)
                  else
                    let n = List.nth p2 k in
                    let c2 = der ccon2 n in
                    if((Myset.mem m last1 && Myset.mem n last2)) then 
                      true
                    else if(Myset.mem (m ^","^ n) aa) then 
                      loop2(k+1)
                    else
                      let bb = Myset.add (m ^","^ n) aa in
                      if (fo_recur c1 c2 bb) then
                        true
                      else
                        loop2(k+1)
              in
                loop2 0
            in
              loop1 0
        in
        loop 0
      else
        false
    in

    if((isEpsilon expr1) && (isEpsilon expr2))
      then true
    else if (Myset.is_empty(intermyset last1 last2)) then false
      else fo_recur expr1 expr2 aa
(* main program *)
let main() = 
let arglist = Array.to_list Sys.argv in

(* print_endline (List.nth arglist 1); *)

let ic = open_in (List.nth arglist 1) in

(* print_endline (input_line ic);
print_endline (input_line ic); *)

let e1 = s2e(input_line ic) in
print_endline "\ns2e1 is done";
(* print_expr e1; *)
(* print_endline "\n"; *)
print_endline (e2s e1);
print_endline "\n---------------------";
let e2 = s2e(input_line ic) in
print_endline "\ns2e2 is done";
(* print_expr e2; *)
(* print_endline "\n"; *)
print_endline (e2s e2);
print_endline "---------------------";
close_in ic;

(* print_string "e1: ";
print_endline (e2s e1);
print_string "e2: ";
print_endline (e2s e2); *)

begin


let time_cc = create "CC" in
start time_cc;
if (ccon_intersect (snf(e1)) (snf(e2)) Myset.empty) then print_endline "CC: true" else print_endline "CC: false";
stop time_cc;

let time_eq = create "EQ" in
start time_eq;
if (equa_intersect (snf(e1)) (snf(e2)) Myset.empty) then print_endline "EQ: true" else print_endline "EQ: false";
stop time_eq;

let time_fo = create "PO" in
start time_fo;
if (altfo_intersect (snf(e1)) (snf(e2)) Myset.empty) then print_endline "PO: true" else print_endline "PO: false";
stop time_fo;

let time_altfa = create "FO" in
start time_altfa;
if (altfa_intersect (snf(e1)) (snf(e2)) Myset.empty) then print_endline "FO: true" else print_endline "FO: false";
stop time_altfa;

let time_automata = create "GA" in
start time_automata;
if (gainc (snf(e1)) (snf(e2))) then print_endline "GA: true" else print_endline "GA: false";
stop time_automata;

dumpInFile ();
dump ();
end;;

(**** call the main program*)

main()
