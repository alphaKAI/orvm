open Core

type registers = {
  mutable a: int;
  mutable b: int;
  mutable c: int;
  mutable d: int;
  mutable e: int;
  mutable f: int
}

type register =
  | A
  | B
  | C
  | D
  | E
  | F
[@@deriving show]

type instruction =
  | Func    of int * instruction list
  | CallF   of int
  | CallFA  of int * int list
  | CallFAR of int * register list
  | HLT
  | Print of register
  | Eq    of register * register
  | Neq   of register * register
  | Leq   of register * register
  | Geq   of register * register
  | Lt    of register * register
  | Gt    of register * register
  | EqI   of register * int
  | NeqI  of register * int
  | LeqI  of register * int
  | GeqI  of register * int
  | LtI   of register * int
  | GtI   of register * int
  | If    of register * instruction list array
  | RetR  of register
  | RetI  of int
  | AddR  of register * register
  | AddI  of register * int
  | SubR  of register * register
  | SubI  of register * int
  | MulR  of register * register
  | MulI  of register * int
  | MovR  of register * register
  | MovI  of register * int
  | PopTo of register
  | PushR of register
  | PushI of int

let stack = Stack.create()
let registers = {a=0;b=0;c=0;d=0;e=0;f=0}
let functions = [|[];[];[];[];[];[]|]

let setRegister x v =
  match x with
  | A -> registers.a <- v
  | B -> registers.b <- v
  | C -> registers.c <- v
  | D -> registers.d <- v
  | E -> registers.e <- v
  | F -> registers.f <- v

let getRegister x =
  match x with
  | A -> registers.a
  | B -> registers.b
  | C -> registers.c
  | D -> registers.d
  | E -> registers.e
  | F -> registers.f

let popto stack r =
  let opt = Stack.pop stack in
  match opt with
  | None -> setRegister r 0
  | Some x -> setRegister r x

let rec reduceStack stack result f =
  let i = Stack.pop stack in
  match i with
  | None -> Stack.push stack result
  | Some x -> reduceStack stack (f result x) f

let saveFunction i l = functions.(i) <- l

let getFunction i = functions.(i)


(*
  関数を呼ぶ場合，
  F -> 第1引数
  E -> 第2引数
  D -> 第3引数
  C -> 第4引数
*)
let setArgs l =
  let rs: register array = [|F; E; D; C|] in
  List.iteri ~f:(fun i v -> setRegister rs.(i) v) l

let rec run = function
  | [] -> () (*printf "no more instruction\n"*)
  | HLT :: _ -> printf "execution stopped\n"
  | Func (i, l) :: rest -> saveFunction i l; run rest
  | CallF i :: rest -> getFunction i |> run ; run rest
  | CallFA  (i, l) :: rest -> setArgs l; getFunction i |> run ; run rest
  | CallFAR (i, r) :: rest -> List.map ~f:(fun x -> getRegister x) r |> setArgs; getFunction i |> run; run rest;
  | Print i :: rest -> Printf.printf "%s : %d\n" (show_register i) (getRegister i); run rest
  | Eq   (x, y) :: rest -> if (getRegister x) =  (getRegister y) then (setRegister B 1) else (setRegister B 0); run rest
  | Neq  (x, y) :: rest -> if (getRegister x) <> (getRegister y) then (setRegister B 1) else (setRegister B 0); run rest
  | Leq  (x, y) :: rest -> if (getRegister x) <= (getRegister y) then (setRegister B 1) else (setRegister B 0); run rest
  | Geq  (x, y) :: rest -> if (getRegister x) >= (getRegister y) then (setRegister B 1) else (setRegister B 0); run rest
  | Lt   (x, y) :: rest -> if (getRegister x) <  (getRegister y) then (setRegister B 1) else (setRegister B 0); run rest
  | Gt   (x, y) :: rest -> if (getRegister x) >  (getRegister y) then (setRegister B 1) else (setRegister B 0); run rest
  | EqI  (x, y) :: rest -> if (getRegister x) =  y then (setRegister B 1) else (setRegister B 0); run rest
  | NeqI (x, y) :: rest -> if (getRegister x) <> y then (setRegister B 1) else (setRegister B 0); run rest
  | LeqI (x, y) :: rest -> if (getRegister x) <= y then (setRegister B 1) else (setRegister B 0); run rest
  | GeqI (x, y) :: rest -> if (getRegister x) >= y then (setRegister B 1) else (setRegister B 0); run rest
  | LtI  (x, y) :: rest -> if (getRegister x) <  y then (setRegister B 1) else (setRegister B 0); run rest
  | GtI  (x, y) :: rest -> if (getRegister x) >  y then (setRegister B 1) else (setRegister B 0); run rest
  | If   (x, l) :: rest -> if (getRegister x) =  1 then run l.(0) else if Array.length l = 2 then run l.(1); run rest
  | RetR x :: rest -> setRegister A (getRegister x); run rest
  | RetI x :: rest -> setRegister A x; run rest
  | AddR (x, y) :: rest -> (getRegister x) + (getRegister y) |> setRegister A; run rest
  | AddI (x, y) :: rest -> (getRegister x) + y |> setRegister A; run rest
  | SubR (x, y) :: rest -> (getRegister x) - (getRegister y) |> setRegister A; run rest
  | SubI (x, y) :: rest -> (getRegister x) - y |> setRegister A; run rest
  | MulR (x, y) :: rest -> (getRegister x) * (getRegister y) |> setRegister A; run rest
  | MulI (x, y) :: rest -> (getRegister x) * y |> setRegister A; run rest
  | MovR (x, y) :: rest -> (setRegister x (getRegister y)); run rest
  | MovI (x, y) :: rest -> (setRegister x y); run rest
  | PopTo r :: rest -> popto stack r; run rest
  | PushR r :: rest -> Stack.push stack (getRegister r); run rest
  | PushI x :: rest -> Stack.push stack x; run rest

(*
  Func#1 is the same as
  let rec fact n =
    if n = 0 then 1
    else
      let m = n - 1 in
      let k = fact m in
      return n * k;;
*)

(*
let program = [
  Func (1, [
      EqI(F, 0);
      If(B, [|[
          RetI 1
        ];[
            SubI(F, 1);
            MovR(D, A);
            PushR F;
            CallFAR(1, [D]);
            PopTo E;
            MulR(E, A);
            RetR A
          ]|])
    ]);
  CallFA(1, [10]);
  Print A
]
*)

(*
  Func#2 is the same as
	let rec fib n =
    if n <= 1 then
      n
    else
      let k1 = n - 2 in
      let r1 = fib k1 in
      let k2 = n - 1 in
      ret r2 = fib k2 in
      r1 + r2
*)

let program = [
  Func(2, [
      LeqI(F, 1);
      If(B, [|[
          RetR(F)
        ]; [
            SubI(F, 2);
            MovR(C, A);
            PushR(F);
            CallFAR(2, [C]);
            MovR(C, A);
            PopTo(F);
            SubI(F, 1);
            MovR(D, A);
            PushR(C);
            CallFAR(2, [D]);
            PopTo(C);
            MovR(D, A);
            AddR(C, D);
            RetR(A)
          ]|])
    ]);
  CallFA(2, [30]);
  Print(A)
]

let () =
  run program
