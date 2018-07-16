open Core

type registers = {
  mutable a: int;
  mutable b: int;
  mutable c: int;
  mutable d: int;
  mutable e: int;
  mutable f: int
}

let registers_init () = {a=0;b=0;c=0;d=0;e=0;f=0}

let registers_dup registers =
  let newRegisters = registers_init () in
  newRegisters.a <- registers.a;
  newRegisters.b <- registers.b;
  newRegisters.c <- registers.c;
  newRegisters.d <- registers.d;
  newRegisters.e <- registers.e;
  newRegisters.f <- registers.f;
  newRegisters

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
  | SubR  of register * register
  | MulR  of register * register
  | DivR  of register * register
  | ModR  of register * register
  | AddI  of register * int
  | SubI  of register * int
  | MulI  of register * int
  | DivI  of register * int
  | ModI  of register * int
  | MovR  of register * register
  | MovI  of register * int
  | PopTo of register
  | PushR of register
  | PushI of int
  | MTh of int * instruction list
  | RTh of int
  | JTh of int
  | SleepI of int
  | Printsln of string

type frame = {
  mutable stack: int Stack.t;
  mutable registers: registers;
  mutable functions: instruction list Array.t;
  mutable prog: instruction List.t
};;

let functions_init () = [|[];[];[];[];[];[]|]

let functions_dup functions =
  Array.copy functions 

let frame_init () =
  {
    stack = Stack.create();
    registers = registers_init ();
    functions = functions_init ();
    prog = []
  }

let frame_dup frame =
  let newFrame = frame_init () in 
  newFrame.stack <- Stack.copy frame.stack;
  newFrame.registers <- registers_dup frame.registers;
  newFrame.functions <- functions_dup frame.functions;
  newFrame

let frame_init_with_prog prog =
  let frame = frame_init () in
  frame.prog <- prog;
  frame

let setRegister frame x v =
  match x with
  | A -> frame.registers.a <- v
  | B -> frame.registers.b <- v
  | C -> frame.registers.c <- v
  | D -> frame.registers.d <- v
  | E -> frame.registers.e <- v
  | F -> frame.registers.f <- v

let getRegister frame x =
  match x with
  | A -> frame.registers.a
  | B -> frame.registers.b
  | C -> frame.registers.c
  | D -> frame.registers.d
  | E -> frame.registers.e
  | F -> frame.registers.f

let popto frame r =
  let opt = Stack.pop frame.stack in
  match opt with
  | None -> setRegister frame r 0
  | Some x -> setRegister frame r x

let rec reduceStack frame result f =
  let i = Stack.pop frame.stack in
  match i with
  | None -> Stack.push frame.stack result
  | Some x -> reduceStack frame (f result x) f

let saveFunction frame i l = frame.functions.(i) <- l

let getFunction frame i = frame.functions.(i)

let threads_init () = Int.Table.create () ~size:8

let threads = threads_init ();;

let saveThread id th = Hashtbl.set threads ~key:id ~data:th

let frames_init () = Int.Table.create () ~size:8

let frames = frames_init ()

let saveFrame id frame =  Hashtbl.set frames ~key:id ~data: frame

let getFrame id =
  match Hashtbl.find frames id with
  | Some frame -> frame
  | None -> raise (Not_found_s (sexp_of_string "No such a frame"))

(*
  関数を呼ぶ場合，
  F -> 第1引数
  E -> 第2引数
  D -> 第3引数
  C -> 第4引数
*)
let setArgs frame l =
  let rs: register array = [|F; E; D; C|] in
  List.iteri ~f:(fun i v -> setRegister frame rs.(i) v) l

let binary_condition_expr_rr op x y frame =
  if op (getRegister frame x) (getRegister frame y) then (setRegister frame B 1) else (setRegister frame B 0);;

let binary_condition_expr_ri op x y frame =
  if op (getRegister frame x) y then (setRegister frame B 1) else (setRegister frame B 0);;

let binary_arithmatic_op_rr op x y frame =
  op (getRegister frame x) (getRegister frame y) |> setRegister frame A;;

let binary_arithmatic_op_ri op x y frame =
  op (getRegister frame x) y |> setRegister frame A;;

let rec run frame = function
  | [] -> () (*printf "no more instruction\n"*)
  | HLT :: _ -> printf "execution stopped\n"
  | Func (i, l) :: rest -> saveFunction frame i l; run frame rest
  | CallF i :: rest -> getFunction frame i |> run frame ; run frame rest
  | CallFA  (i, l) :: rest -> setArgs frame l; getFunction frame i |> run frame ; run frame rest
  | CallFAR (i, r) :: rest -> List.map ~f:(fun x -> getRegister frame x) r |> setArgs frame; getFunction frame i |> run frame; run frame rest;
  | Print i :: rest -> Printf.printf "%s : %d\n" (show_register i) (getRegister frame i); run frame rest
  | Eq   (x, y) :: rest -> (binary_condition_expr_rr (=) x y frame); run frame rest
  | Neq  (x, y) :: rest -> (binary_condition_expr_rr (<>) x y frame); run frame rest
  | Leq  (x, y) :: rest -> (binary_condition_expr_rr (<=) x y frame); run frame rest
  | Geq  (x, y) :: rest -> (binary_condition_expr_rr (>=) x y frame); run frame rest
  | Lt   (x, y) :: rest -> (binary_condition_expr_rr (<) x y frame); run frame rest
  | Gt   (x, y) :: rest -> (binary_condition_expr_rr (>) x y frame); run frame rest
  | EqI  (x, y) :: rest -> (binary_condition_expr_ri (=) x y frame); run frame rest
  | NeqI (x, y) :: rest -> (binary_condition_expr_ri (<>) x y frame); run frame rest
  | LeqI (x, y) :: rest -> (binary_condition_expr_ri (<=) x y frame); run frame rest
  | GeqI (x, y) :: rest -> (binary_condition_expr_ri (>=) x y frame); run frame rest
  | LtI  (x, y) :: rest -> (binary_condition_expr_ri (<) x y frame); run frame rest
  | GtI  (x, y) :: rest -> (binary_condition_expr_ri (>) x y frame); run frame rest
  | If   (x, l) :: rest -> if (getRegister frame x) =  1 then run frame l.(0) else if Array.length l = 2 then run frame l.(1); run frame rest
  | RetR x :: rest -> setRegister frame A (getRegister frame x); run frame rest
  | RetI x :: rest -> setRegister frame A x; run frame rest
  | AddR (x, y) :: rest -> binary_arithmatic_op_rr (+) x y frame; run frame rest
  | SubR (x, y) :: rest -> binary_arithmatic_op_rr (-) x y frame; run frame rest
  | MulR (x, y) :: rest -> binary_arithmatic_op_rr ( * ) x y frame; run frame rest
  | DivR (x, y) :: rest -> binary_arithmatic_op_rr (/) x y frame; run frame rest
  | ModR (x, y) :: rest -> binary_arithmatic_op_rr (mod) x y frame; run frame rest
  | AddI (x, y) :: rest -> binary_arithmatic_op_ri (+) x y frame; run frame rest
  | SubI (x, y) :: rest -> binary_arithmatic_op_ri (-) x y frame; run frame rest
  | MulI (x, y) :: rest -> binary_arithmatic_op_ri ( * ) x y frame; run frame rest
  | DivI (x, y) :: rest -> binary_arithmatic_op_ri (/) x y frame; run frame rest
  | ModI (x, y) :: rest -> binary_arithmatic_op_ri (mod) x y frame; run frame rest
  | MovR (x, y) :: rest -> (setRegister frame x (getRegister frame y)); run frame rest
  | MovI (x, y) :: rest -> (setRegister frame x y); run frame rest
  | PopTo r :: rest -> popto frame r; run frame rest
  | PushR r :: rest -> Stack.push frame.stack (getRegister frame r); run frame rest
  | PushI x :: rest -> Stack.push frame.stack x; run frame rest
  | MTh (id, insts) :: rest ->
    let newFrame = frame_dup frame in
    newFrame.prog <- insts;
    saveFrame id newFrame;
    run frame rest
  | RTh id :: rest -> 
    let thread =
      Thread.create (fun id -> let newFrame = getFrame id in run newFrame newFrame.prog)
    in
    saveThread id @@ thread id;
    run frame rest
  | JTh id :: rest ->
    begin
      match Hashtbl.find threads id with
      | Some thread -> Thread.join thread
      | None -> ();
        run frame rest
    end
  | SleepI sec :: rest -> 
    Unix.sleep sec;
    run frame rest
  | Printsln msg :: rest ->
    Printf.printf "%s\n" msg;
    Out_channel.flush stdout;
    run frame rest

let run_with_frame frame =
  run frame frame.prog

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
  CallFA(2, [35]);
  Print(A)
]

(* let program = [
   MTh(1, [
      Func(1, [
          Eq(F, E);
          If(B, [|[
              RetI(0)
            ]; [
                SleepI(1);
                Printsln("thread1");
                AddI(E, 1);
                MovR(E, A);
                CallFAR(1, [F; E])
              ]|])
        ]);
      CallFA(1, [10; 0])
    ]);
   MTh(2, [
      Func(2, [
          Eq(F, E);
          If(B, [|[
              RetI(0)
            ]; [
                SleepI(1);
                Printsln("thread2");
                AddI(E, 1);
                MovR(E, A);
                CallFAR(2, [F; E])
              ]|])
        ]);
      CallFA(2, [50; 0])
    ]);
   RTh(1);
   RTh(2);
   JTh(1);
   JTh(2);
   ] *)

let () =
  run_with_frame @@ frame_init_with_prog program
