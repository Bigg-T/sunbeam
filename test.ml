open Compile
open Runner
open Printf
open OUnit2
open ExtLib
open Types
open Expr
open Pretty
open Optimize

let t name program expected = name>::test_run [] program name expected;;
let tgc name heap_size program expected = name>::test_run [string_of_int heap_size] program name expected;;
let tvg name program expected = name>::test_run_valgrind [] program name expected;;
let tvgc name heap_size program expected = name>::test_run_valgrind [string_of_int heap_size] program name expected;;
let terr name program expected = name>::test_err [] program name expected;;
let tgcerr name heap_size program expected = name>::test_err [string_of_int heap_size] program name expected;;

(* let tfvs name program expected = name>::
                                 (fun _ ->
                                    let ast = parse_string name program in
                                    let anfed = anf (tag ast) in
                                    let vars = free_vars anfed in
                                    let c = Pervasives.compare in
                                    let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
                                    assert_equal (List.sort ~cmp:c vars) (List.sort ~cmp:c expected) ~printer:str_list_print)
;; *)

let t_opt name program expected = name>::
                                  (fun _ ->
                                     let ast = parse_string name program in
                                     let anfed = atag (anf (tag ast)) in
                                     let optimized = optimize anfed false in
                                     assert_equal (string_of_aprogram optimized) expected)
;;
let t_any name value expected = name>::(fun _ -> assert_equal expected value);;

let rec print_errs (errs : exn list) : string =
  match errs with
  | [] -> ""
  | first::rest -> Printexc.to_string first ^ " " ^ print_errs rest
  | _ -> "Nothing"
;;

let pair_tests = [
  t "tup1" "let t = (4, (5, 6)) in
            begin
              t[0] := 7;
              t
            end" "(7, (5, 6))";
  t "tup2" "let t = (4, (5, 6)) in
            begin
              t[1] := 7;
              t
            end" "(4, 7)";
  (* TODO new print isn't working with our tuples, so don't have cyclic tuple checking *)
  (* t "tup3" "let t = (4, (5, 6)) in
            begin
              t[1] := t;
              t
            end" "(4, <cyclic tuple 1>)"; *)
  t "tup4" "let t = (4, 6) in
            (t, t)"
    "((4, 6), (4, 6))"

]

let oom = [
  (* TODO should be getting out of memory error, getting 0 *)
  tgcerr "oomgc1" 7 "(1, (3, 4))" "Out of memory";
  tgc "oomgc2" 8 "(1, (3, 4))" "(1, (3, 4))";
  tvgc "oomgc3" 8 "(1, (3, 4))" "(1, (3, 4))";
  tgc "oomgc4" 4 "(3, 4)" "(3, 4)";
  tgcerr "oomgc5" 3 "(3, 4)" "Allocation";
]

let gc = [
  tgc "gc1" 10
    "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
    "(1, 2)";
  tgc "gc2" 9 (* TODO seems to require 9 words ? *)
    "let f = (lambda: (1, 2)) in
         begin
           f();
           f()
         end"
    "(1, 2)";
  tgc "gc3" 8 "let f = (1, 2, 3) in let b = f[2] in (3, 4, 5)" "(3, 4, 5)";
  tgc "gc4" 8 "let t = (4, (5, 6)) in
                      begin
                        t[1] := 19;
                        let a = (1) in t
                      end" "(4, 19)";
  tgc "gc5" 12 "let t = (4, (5, 6, 9)) in
                      begin
                        t[1] := 19;
                        let a = (2, 3) in a
                      end" "(2, 3)";
  tgc "gc6" 16 "let t = (4, 3) in
                      begin
                          let a = (lambda x :
                            let d =
                               let f = (lambda x: (14, 34, 44)) in f()
                            in 6)
                          in (a(1));
                          let s = (2, 4) in t;
                      end" "(4, 3)";
  tgc "gc7" 12 "let five = 5 in
                      begin
                          let a = (lambda x :
                            let d =
                               let f = (lambda x: (five, 34, 44)) in f()
                            in 6)
                          in (a(1));
                          let s = (2, 4) in (3, s);
                      end" "(3, (2, 4))";

  (* TODO get a weird integer overflow here? why? *)
  (* tgc "gc8" 20 "let t = (1, (2, (3, 4))) in
                      let a = (lambda x: x) in
                        begin
                          a(t);
                          a[1] := 5;
                          let b = (5, 6, 7, 8, 9, 10) in a(b);
                        end" "(5, 6, 7, 8, 9, 10)" *)
  tgc "gc9" 26 "let five = 5 in
                      begin
                          let a = (lambda x :
                            let d =
                               let f = (lambda x: (five, 34, (3, 2, 5))) in f()
                            in 6)
                          in (a(1));
                          let g = (lambda: (2, 4, (5, 7))) in (3, g());
                      end" "(3, (2, 4, (5, 7)))";
  tgc "gc10" 28 "let a = (lambda x: x) in
                        begin
                          a((1, (2, (3, 4))));
                          let f = let b = (5, 6, 7, 8, 9, 10) in a(b) in f
                        end" "(5, 6, 7, 8, 9, 10)";
  tgc "gc11" 12 "let yo100 = 100 in
                    let yo300 = 300 in
                      begin
                        let foo = (lambda x: (yo100, (yo300, x))) in
                          let foo2 = foo(8) in
                            begin
                              foo2[1] := yo100;
                              5
                            end;
                        let bar = (1, 2) in bar
                      end" "(1, 2)";
  tgc "gc12" 26 "let tup = (1, 2) in
                    begin
                      let f = (lambda x: (tup, x)) in
                        f(5)[0] := (100, 300);
                      let g = (lambda: ((1, 2), 3)) in g();
                    end" "((1, 2), 3)";
  tgc "gc13" 20 "let t = 5 in
                    begin
                      let tup = ((100, 211, 311), (1431, 2132, 532)) in
                        let f = (lambda x: (tup, x)) in
                          begin
                            f(5)[0] := 1;
                            tup[0] := 1;
                            tup[1] := 2;
                          end
                    end" "(1, 2)";

  (* tgc "gc14" 8 "begin
                    let y = (lambda f: f(7)) in
                      y((lambda x: x + 1));
                    (3, 2)
                  end" "(3, 2)"; *)

  (* tgc "gc15" 18 "let five = 5 in let yo = (lambda x, y, z: ((x * y) - z) + (five + 1)) in let applyToFive = (lambda q, it: (it(yo(five, 2, 3))) + q) in let incr = (lambda x: x + 1) in applyToFive(7, incr)" "21"; *)
  tgc "gc16" 8 "let t = (4, (5, 6)) in
                      begin
                        t[1] := 19;
                        t
                      end" "(4, 19)";
  (* TODO getting segfaults instead of out of memory errors? *)
  (* tgcerr "gc17" 11 "(1, (3, (4, 6, 7)))" "Out of memory"; *)
  tgc "gc18" 4 "let five = 5 in let one = 1 in let x = (lambda : five + one) in x()" "6";
  tgc "gc19" 7 "let x = (lambda y, z : y) in x(7, 5)" "7";
  tgc "gc20" 12 "let a100 = 100 in
                    begin
                      let yo = (lambda x:
                                  let my = (lambda t:
                                              let egg = (lambda what: (1, what)) in egg(33))
                                    in my(4)) in yo(5)
                    end" "(1, 33)";
  tgc "gc21" 28 "let five = 5 in
                  begin
                      let a = (lambda x :
                        let d =
                           let h = (lambda: 70000) in
                             let f = (lambda x: (five, 34, (3, 2, h))) in f()
                        in 6)
                      in (a(1));
                      let g = (lambda: (2, 4, (5, 7))) in (3, g());
                  end" "(3, (2, 4, (5, 7)))";
  tgc "gc22" 14 "begin
                    let f = (lambda x: let b = (7, 8, 9, (10, 11, 12, 13)) in 4)
                      in f(5);
                    let a = (1, 2) in
                      ((7, a), a)
                 end" "((7, (1, 2)), (1, 2))";
]
;;

let tests = [
  (* t "test1" "(lambda: 5)" ""; (*TODO seg fault if not let bind*) *)
  t "test2" "let five = (lambda: 5) in five()" "5";
  t "test3" "let incr = (lambda x: x + 1) in incr(5)" "6";
  t "test4" "let a = 7 in a" "7";
  t "test5" "let a = (lambda x: x) in 5" "5";
  (* t "test6" "let applyToFive = (lambda yo: yo(5)) in let incr = (lambda x : x + 1) in applyToFive(incr)" "6"; *)
  t "test7" "(1, 2, 3)" "(1, 2, 3)";
  t "test8" "(1, 2, 3, 4)" "(1, 2, 3, 4)";
  (* t "test9" "(lambda x: x)" "()"; (* TODO  No clue why this segfault looks the same as test5 but without let bind*) *)
  t "test10" "let x = (lambda y: y) in x(7)" "7";
  (* t "test11" "let applyToFive = (lambda y: y(5)) in let incr = (lambda x : x + 1) in applyToFive(incr)" "6"; *)
  (* t "test12" "let x = (lambda a, b: a(5) + b) in let incr = (lambda x: x + 1) in x(incr, 5)" "11"; *)
  (* t "test13" "let five = 5 in let applyToFive = (lambda it: it(five)) in let incr = (lambda x: x + 1) in applyToFive(incr)" "6"; *)
  t "test14" "let a = 7 in let b = a in b" "7";
  t "test15" "let a = 7 in let b = 4 + 4 in let c = a in c" "7";
  t "test16" "let five = 5 in let x = (lambda : five) in x()" "5";
  t "test17" "let x = (lambda y, z : y) in x(7, 5)" "7";
  (* t "test18" "let five = 5 in let applyToFive = (lambda q, it: it(five) + q(five)) in let incr = (lambda x: x + 1) in applyToFive(incr, incr)" "12"; *)
  (* t "test19" "let five = 5 in let applyToFive = (lambda q, it: (it(five) + q)) in let incr = (lambda x: x + 1) in applyToFive(7, incr)" "13"; *)
  (* t "test20" "let applyToFive = (lambda q, it: (q + it(9))) in let incr = (lambda x: x + 1) in applyToFive(7, incr)" "17"; *)
  (* t "test21" "let applyToFive = (lambda it, q: it(9) + q) in let incr = (lambda x: x + 1) in applyToFive(incr, 7)" "17"; *)
  t "test22" "let six = 6 in let three = 3 in let x = (lambda : six * three) in (x())" "18";
  (* t "test23" "let five = 5 in let yo = (lambda x : x + five) in let applyToFive = (lambda q, it: (it(yo(five)) + q)) in let incr = (lambda x: x + 1) in applyToFive(7, incr)" "18"; *)
  (* t "test24" "let five = 5 in let yo = (lambda x, y, z: ((x * y) - z) + (five + 1)) in let applyToFive = (lambda q, it: (it(yo(five, 2, 3))) + q) in let incr = (lambda x: x + 1) in applyToFive(7, incr)" "21"; *)
]
;;

let mutable_tuple_tests = [
  terr "mt_test1" "(1, 2, 3)[-1]:=4" "Error: index out of bounds";
  terr "mt_test2" "(1, 2, 3)[3]:=4" "Error: index out of bounds";
  terr "mt_test3" "(1, 2, 3)[4]:=4" "Error: index out of bounds";
  t "mt_test4" "(1, 2, 3)[2]:=4" "(1, 2, 4)";
  t "mt_test5" "(1, 2, 3)[2]:=true" "(1, 2, true)";
  t "mt_test6" "(1, 2, 3)[2]:=false" "(1, 2, false)";
  t "mt_test7" "(1, 2, 3)[2]:=(4, 5)" "(1, 2, (4, 5))";
  t "mt_test8" "(1, 2, (4, 5))[2][0]" "4";
  t "mt_test9" "(1, 2, 3)[1]:=4" "(1, 4, 3)";
  t "mt_test10" "(1, 2, 3)[0]:=4" "(4, 2, 3)";
  t "mt_test11" "(1, 2, 3)[1]:=true" "(1, true, 3)";
  t "mt_test12" "(4, (5, 6))[0] := 7" "(7, (5, 6))";
  t "mt_test13" "(4, (5, 6))[1] := 7" "(4, 7)";

  (* t "mt_test4" "(1, 2, 3)[0]" "1"; *)
  (* terr "mt_test5" "(1, 2, 3)[3]" "Error"; *)
]
;;

let regression_tests = [
  t "r_test1" "print((4, 5, 6))" "(4, 5, 6)\n(4, 5, 6)";
  t "r_test2" "print((4, 5, (1, 2)))" "(4, 5, (1, 2))\n(4, 5, (1, 2))";
  t "r_test3" "let a = (lambda: (1, 2)) in print(a())" "(1, 2)\n(1, 2)";
  t "r_test4" "let a = (1, 2, 3) in (1 + (2 * 3)) + a[2]" "10";
  t "r_test5" "let a = (1, 2, 3) in print(a)" "(1, 2, 3)\n(1, 2, 3)";
  t "r_test6" "print(7)" "7\n7";
  tgc "r_test7" 12 "let a = (1, 2, 3) in let b = (4, 5, 6) in let c = (7, 8) in a[1] + b[1] + c[1]" "15";
  t "r_test8" "let a = (lambda: 7) in print(a)" "<function>\n<function>";
  (* t "r_test9" "let a = (1, 2) in a[1] := a" "(1, <cyclic tuple 1>)"; *)
]
;;

let wfn_tests = [
  t "wfn_test1" "let x:int = 7 in x" "7";
  t "wfn_test2" "let x:[Y] Int = 7 in x" "7";
  t "wfn_test3" "let x:[Y] Z = 7 in x" "7";
]
;;

let letrec_tests = [
  t "letrec1" "let rec a = (lambda x: if x == 0: 1000 else: a(x - 1)) in a(3)" "1000";
  t "letrec2" "let rec a = (lambda x: if x == 0: 0 else: a(x - 1)), b = (lambda: 52) in a(4)" "0";
  t "letrec3" "let rec a = (lambda x: if x == 0: 0 else: a(x - 1)), b = (lambda: 52) in a(b())" "0";
  t "letrec4" "let rec a =
                (lambda x:
                  if x == 0:
                    (0, 2)
                  else:
                    (a(x - 1), a(x - 1)))
                in a(2)"
    "(((0, 2), (0, 2)), ((0, 2), (0, 2)))";
  t "letrec5" "let rec a = (lambda x: if x == 0: 3 else: ((a(x - 1)) + (a(x - 1)))) in a(1)" "6";
  t "letrec6" "let a = (lambda: 6) in (a(), a())" "(6, 6)";
  t "letrec7" "let rec a = (lambda x: if x == 0: 6 else: a(x - 1)) in (a(1), a(0))" "(6, 6)";
  t "letrec8" "let rec a = (lambda x: if x == 0: 6 else: a(x - 1)) in a(2)" "6";
  t "letrec9" "let rec a = (lambda x: if x == 0: 100 else: a(x - 1) + 1) in a(3)" "103";
  t "letrec10" "let five = 5 in let rec a = (lambda x: if x == 0: five else: five + a(x - 1) + 1) in a(3)" "23";
  t "letrec11" "let rec fact = (lambda x: if (x == 0): 1 else: x * fact(x - 1)) in fact(3)" "6";
  t "letrec12" "let rec fib = (lambda x: if ((x == 2) || (x == 1)): 1 else: (fib(x - 1)) + (fib(x - 2))) in fib(4)" "3";
  t "letrec13" "let rec fib = (lambda x: if ((x == 2) || (x == 1)): 1 else: (fib(x - 1)) + (fib(x - 2))) in fib(9)" "34";
]
;;

let constant_prop_tests = [
  t_opt "o_test1" "add1(7)" "8";
  t_opt "o_test2" "sub1(7)" "6";
  t_opt "o_test3" "!(true)" "false";
  t_opt "o_test4" "!(false)" "true";
  t_opt "o_test5" "isnum(5)" "true";
  t_opt "o_test6" "isnum(false)" "false";
  t_opt "o_test7" "isnum(5 + 7)" "(alet binop_2 = 12 in true)";
  t_opt "o_test8" "isbool(true)" "true";
  t_opt "o_test9" "isbool(7)" "false";
  t_opt "o_test10" "isnum(add1(7))" "(alet unary_2 = 8 in true)";
  t_opt "o_test11" "5 + 2" "7";
  t_opt "o_test12" "isbool(3 - 1)" "(alet binop_2 = 2 in false)";
  t_opt "o_test13" "4 * (3 - 1)" "(alet binop_2 = 2 in 8)";
  t_opt "o_test14" "8 < 2" "false";
  t_opt "o_test15"
    "let x = 4 + 5 in
    let y = x * 2 in
    let z = y - x in
    let a = x + 7 in
    let b = 14 in
    a + b"
    "(alet x = 9 in (alet y = 18 in (alet z = 9 in (alet a = 16 in (alet b = 14 in 30)))))";
  t_opt "o_test16"
    "
      begin
        let we = isnum(add1(7)) in we;
        isnum(add1(7));
        let a = 8 in let b = 4 in a + b;
      end
    "
    "(alet unary_6 = 8 in (alet we = true in (true; (alet unary_9 = 8 in (true; (alet a = 8 in (alet b = 4 in 12)))))))";
  t_opt "o_test17" "let a = (lambda x: 1 + x) in a(3)" "(alet a = (lambda(x): (1 + x)) in (a(3)))";
  t_opt "o_test18"
    "let f = (lambda x: x(7)) in let a = (lambda x: x + 1) in f(a)"
    "(alet f = (lambda(x): (x(7))) in (alet a = (lambda(x): (x + 1)) in (f(a))))";
  t_opt "o_test19"
    "let rec a = (lambda x: if x == 0: 3 + 2 else: a(x - 1)) in a(6 + 1)"
    "(aletrec a = (lambda(x): (alet binop_18 = (x == 0) in (if binop_18: (3 + 2) else: (alet binop_11 = (x - 1) in (a(binop_11)))))) in (alet binop_3 = 7 in (a(7))))";
  t_opt "o_test20" "let a = 5 + 10 in isnum(a)" "(alet a = 15 in true)";
  t_opt "o_test21"
    "let a = (lambda x: x(5)) in let b = (lambda y: y) in a(b)"
    "(alet a = (lambda(x): (x(5))) in (alet b = (lambda(y): y) in (a(b))))";
  t_opt "o_test22"
    "let rec a = (lambda x: x(5)), b = (lambda y: y) in a(b)"
    "(aletrec a = (lambda(x): (x(5))), b = (lambda(y): y) in (a(b)))";
  t_opt "o_test24"
    "let a = (lambda x: x) in let b = (lambda y: 100) in a(b(4))"
    "(alet a = (lambda(x): x) in (alet b = (lambda(y): 100) in (alet app_4 = (b(4)) in (a(app_4)))))";
  t_opt "o_test24"
    "let a = (lambda x: x) in let b = (lambda y: 100) in a(b(4 + 2))"
    "(alet a = (lambda(x): x) in (alet b = (lambda(y): 100) in (alet binop_5 = 6 in (alet app_4 = (b(6)) in (a(app_4))))))";
  t_opt "o_test25" "let a = (lambda: 3 + 4) in a()" "(alet a = (lambda(): 7) in (a()))";
  t_opt "o_test26"
    "let a = ((let yo = (lambda: 5 + 6) in yo), (2 + 3), 7) in a"
    "(alet yo = (lambda(): 11) in (alet binop_12 = 5 in (alet a = (yo, binop_12, 7) in a)))";
  t_opt "o_test27"
    "let a = (3, 4, 5) in begin a[1] := (7 + 2); a end"
    "(alet a = (3, 4, 5) in (alet binop_4 = 9 in (a[1] := binop_4; a)))";
  t_opt "o_test28"
    "5 + (if ((6 + 3) == 4): (8 * 2) else: (6 - 1))"
    "(alet binop_11 = 9 in (alet binop_9 = false in (alet if_2 = (if binop_9: 16 else: 5) in (5 + if_2))))";
  t_opt "o_test29" "let a = true + 5 in a" "(alet a = (true + 5) in a)";
]
;;

let cse_tests = [
  t_opt "cse_test1"
    "
  let x = 5 in
  let y = x in
  let a = x + 2 in
  let b = y + 2 in
  b
  "
    "(alet x = 5 in (alet y = x in (alet a = (x + 2) in (alet b = a in a))))";
  t_opt "cse_test2"
    "let x = (let y = 5 in y) in x"
    "(alet y = 5 in (alet x = y in y))";
  t_opt "cse_test3"
    "let x = (let y = 5 in y + 2) in x"
    "(alet y = 5 in (alet x = (y + 2) in x))";
  t_opt "cse_test4"
    "let x = 5 + 2 in
  let y = 2 in
  let z = 5 + y in
  z"
    "(alet x = (5 + 2) in (alet y = 2 in (alet z = (5 + y) in z)))";
  t_opt "cse_test5"
    "let f = (lambda x: x + 1) in
  let y = f(5) in
  let z = f(5) in
  z
  "
    "(alet f = (lambda(x): (x + 1)) in (alet y = (f(5)) in (alet z = y in y)))";
  t_opt "cse_test6"
    "
  let a =
  begin
    let z = 5 + 2 in
    let yo = (lambda a: 5 + 2) in
    let yo1 = yo in
    100;
    100;
  end in a
    "
    "(alet z = (5 + 2) in (alet yo = (lambda(a): z) in (alet yo1 = yo in (100; (alet a = 100 in a)))))";
  t_opt "cse_test7"
    "let rec a = (lambda: 7), b = (lambda: 9 + 8) in a()"
    "(aletrec a = (lambda(): 7), b = (lambda(): (9 + 8)) in (a()))";
  t_opt "cse_test8"
    "let a = 7 + 8 in
  let b = (1, 2, (7 + 8)) in
  b"
    "(alet a = (7 + 8) in (alet binop_8 = a in (alet b = (1, 2, binop_8) in b)))";
  t_opt "cse_test9"
    "let a = (1, 2, 3) in
  let b = 1 + 2 in
  begin
    a[0] := (1 + 2);
    a
  end"
    "(alet a = (1, 2, 3) in (alet b = (1 + 2) in (alet binop_5 = b in (a[0] := b; a))))";
  t_opt "cse_test10"
    "let a = 0 in
   let b = (a == 0) in
   if (a == 0): a + 2 else: a + 5"
    "(alet a = 0 in (alet b = (a == 0) in (alet binop_10 = b in (if b: (a + 2) else: (a + 5)))))";
  t_opt "cse_test11"
    "let a = (lambda: 7) in
    let b = a() in
    let c = a() in
    c"
    "(alet a = (lambda(): 7) in (alet b = (a()) in (alet c = b in b)))";
  t_opt "cse_test12"
    "let a = (lambda: (1, 2, 3)) in
    let b = a() in
    let c = a() in
    c"
    "(alet a = (lambda(): (1, 2, 3)) in (alet b = (a()) in (alet c = (a()) in c)))";
  t_opt "cse_test13"
    "let a = (lambda: (1, 2, 3)) in
     let b = a() in
     let c = b in
     let d = c in
     7"
    "(alet a = (lambda(): (1, 2, 3)) in (alet b = (a()) in (alet c = b in (alet d = b in 7))))";
]
;;

let dae_tests = [
  t_opt "d_test1" "let a = 5 in 7" "7";
  t_opt "d_test2" "let a = 5 in a" "(alet a = 5 in a)";
  t_opt "d_test3"
    "let a = 5 in let b = 6 in let c = b in c"
    "(alet b = 6 in (alet c = b in c))";
  t_opt "d_test4"
    "let a = 6 in let c = (let b = 7 in a) in c"
    "(alet a = 6 in (alet c = a in c))";
  t_opt "d_test5" "if true: (let a = 6 in 5) else: 4" "(if true: 5 else: 4)";
  t_opt "d_test6" "if false: (let a = 6 in 5) else: (let b = 4 in 6)" "(if false: 5 else: 6)";
  t_opt "d_test7"
    "let five = 5 in let x = (lambda : five) in x()"
    "(alet five = 5 in (alet x = (lambda(): five) in (x())))";
  t_opt "d_test8"
    "let five = 5 in let x = (lambda : 7) in x()"
    "(alet x = (lambda(): 7) in (x()))";
  t_opt "d_test9"
    "let t = ((let a = 8 + 4 in 5), 4) in t"
    "(alet t = (5, 4) in t)";
  t_opt "d_test10"
    "let t = ((let a = 8 + 4 in 5), 4) in begin t[1] := (let b = 4 in 7); t end"
    "(alet t = (5, 4) in (t[1] := 7; t))";
  t_opt "d_test11"
    "let rec a = (lambda x: let b = 4 in 7) in a()"
    "(aletrec a = (lambda(x): 7) in (a()))";
  t_opt "d_test12"
    "let a = 7 in if (a == 7): 1 else: 0"
    "(alet a = 7 in (alet binop_5 = (a == 7) in (if binop_5: 1 else: 0)))";
  t_opt "d_test13"
    "let a = 7 in let b = 4 in (a, 2, 3)"
    "(alet a = 7 in (a, 2, 3))";
  t_opt "d_test14"
    "let a = (1, 2, 3) in (1 + (2 * 3)) + a[2]"
    "(alet a = (1, 2, 3) in (alet binop_7 = (2 * 3) in (alet binop_6 = (1 + binop_7) in (alet get_3 = a[2] in (binop_6 + get_3)))))";
  t_opt "d_test15"
    "let a = (1, 2, 3) in let b = 2 in begin a[b] := 6; a end"
    "(alet a = (1, 2, 3) in (alet b = 2 in (a[b] := 6; a)))";
  t_opt "d_test16"
    "let a = 7 in
    let b = (1, 2, 3) in
    let c =
      begin
        b[0] := 8;
        b
      end in
    a
    "
    "(alet a = 7 in (alet b = (1, 2, 3) in (b[0] := 8; a)))";
  t_opt "d_test17"
    "let a = 7 in
    let b = (1, 2, 3) in
    let c =
      begin
        b[0] := 8;
        b
      end in
    b
    "
    "(alet b = (1, 2, 3) in (b[0] := 8; b))";
  t_opt "d_test18"
    "let a = 7 in
    let b = (1, 2, 3) in
    let c =
      begin
        b[0] := 8;
        b
      end in
    c
    "
    "(alet b = (1, 2, 3) in (b[0] := 8; (alet c = b in c)))";
  t_opt "d_test19"
    "let a = print(5) in 7"
    "(alet a = print(5) in 7)";
  t_opt "d_test20"
    "let a = print(5) in
    let b = a in
    7"
    "(alet a = print(5) in 7)";
  t_opt "d_test21"
    "let a = add1(5) in 6"
    "6";
  t_opt "d_test22"
    "let a = printStack(5 + 3) in 6"
    "(alet binop_5 = (5 + 3) in (alet a = printStack(binop_5) in 6))";
  t_opt "d_test23"
    "let a = (lambda: 6) in let b = a() in 5"
    "(alet a = (lambda(): 6) in 5)";
  t_opt "d_test24"
    "let a = (lambda: (1, 2, 3)) in let b = a() in 5"
    "(alet a = (lambda(): (1, 2, 3)) in (alet b = (a()) in 5))";
]
;;

let combined_tests = [
  t_opt "c_test1" "add1(7)" "8";
  t_opt "c_test2" "sub1(7)" "6";
  t_opt "c_test3" "!(true)" "false";
  t_opt "c_test4" "!(false)" "true";
  t_opt "c_test5" "isnum(5)" "true";
  t_opt "c_test6" "isnum(false)" "false";
  t_opt "c_test7" "isnum(5 + 7)" "true";
  t_opt "c_test8" "isbool(true)" "true";
  t_opt "c_test9" "isbool(7)" "false";
  t_opt "c_test10" "isnum(add1(7))" "true";
  t_opt "c_test11" "5 + 2" "7";
  t_opt "c_test12" "isbool(3 - 1)" "false";
  t "c_test13" "4 * (3 - 1)" "8";
  t_opt "c_test14" "8 < 2" "false";
  t_opt "c_test15"
    "let x = 4 + 5 in
    let y = x * 2 in
    let z = y - x in
    let a = x + 7 in
    let b = 14 in
    a + b"
    "30";
  t_opt "c_test16"
    "
      begin
        let we = isnum(add1(7)) in we;
        isnum(add1(7));
        let a = 8 in let b = 4 in a + b;
      end
    "
    "(true; (true; 12))";
  t_opt "c_test17" "let a = (lambda x: 1 + x) in a(3)" "(alet a = (lambda(x): (1 + x)) in (a(3)))";
  t_opt "c_test19"
    "let rec a = (lambda x: if x == 0: 3 + 2 else: a(x - 1)) in a(6 + 1)"
    "(aletrec a = (lambda(x): (alet binop_18 = (x == 0) in (if binop_18: 5 else: (alet binop_11 = (x - 1) in (a(binop_11)))))) in (a(7)))";
  t_opt "c_test20" "let a = 5 + 10 in isnum(a)" "true";
  t_opt "c_test24"
    "let a = (lambda x: x) in let b = (lambda y: 100) in a(b(4))"
    "(alet a = (lambda(x): x) in (alet b = (lambda(y): 100) in (alet app_4 = (b(4)) in (a(app_4)))))";
  t_opt "c_test24"
    "let a = (lambda x: x) in let b = (lambda y: 100 + 1) in a(b(4 + 2))"
    "(alet a = (lambda(x): x) in (alet b = (lambda(y): 101) in (alet app_4 = (b(6)) in (a(app_4)))))";
  t_opt "c_test25" "let a = (lambda: 3 + 4) in a()" "(alet a = (lambda(): 7) in (a()))";
  t_opt "c_test26"
    "let a = ((let yo = (lambda: 5 + 6) in yo), (2 + 3), 7) in a"
    "(alet yo = (lambda(): 11) in (alet binop_12 = 5 in (alet a = (yo, binop_12, 7) in a)))";
  t_opt "c_test27"
    "let a = (3, 4, 5) in begin a[1] := (7 + 2); a end"
    "(alet a = (3, 4, 5) in (alet binop_4 = 9 in (a[1] := binop_4; a)))";
  t_opt "c_test28"
    "5 + (if ((6 + 3) == 4): (8 * 2) else: (6 - 1))"
    "(alet binop_9 = false in (alet if_2 = (if binop_9: 16 else: 5) in (5 + if_2)))";
  t_opt "c_test29" "let a = true + 5 in a" "(alet a = (true + 5) in a)";
  t_opt "c2_test1"
    "
 let x = 5 in
 let y = x in
 let a = x + 2 in
 let b = y + 2 in
 b
 "
    "7";
  t_opt "c2_test2"
    "let x = (let y = 5 in y) in x"
    "5";
  t_opt "c2_test3"
    "let x = (let y = 5 in y + 2) in x"
    "7";
  t_opt "c2_test4"
    "let x = 5 + 2 in
   let y = 2 in
   let z = 5 + y in
   z"
    "7";
  t_opt "c2_test5"
    "let f = (lambda x: x + 1) in
   let y = f(5) in
   let z = f(5) in
   z
   "
    "(alet f = (lambda(x): (x + 1)) in (alet y = (f(5)) in y))";
  t_opt "c2_test6"
    "
   let a =
   begin
     let z = 5 + 2 in
     let yo = (lambda a: 5 + 2) in
     let yo1 = yo in
     100;
     100;
   end in a
     "
    "((lambda(a): 7); (100; 100))";
  t_opt "c2_test7"
    "let rec a = (lambda: 7), b = (lambda: 9 + 8) in a()"
    "(aletrec a = (lambda(): 7), b = (lambda(): 17) in (a()))";
  t_opt "c2_test8"
    "let a = 7 + 8 in
   let b = (1, 2, (7 + 8)) in
   b"
    "(alet binop_8 = 15 in (alet b = (1, 2, binop_8) in b))";
  t_opt "c2_test9"
    "let a = (1, 2, 3) in
   let b = 1 + 2 in
   begin
     a[0] := (1 + 2);
     a
   end"
    "(alet a = (1, 2, 3) in (alet binop_5 = 3 in (a[0] := binop_5; a)))";
  t_opt "c2_test10"
    "let a = 0 in
    let b = (a == 0) in
    if (a == 0): a + 2 else: a + 5"
    "(alet binop_10 = true in (if binop_10: 2 else: 5))";
  t_opt "c2_test11"
    "let a = (lambda: 7) in
     let b = a() in
     let c = a() in
     c"
    "(alet a = (lambda(): 7) in (alet b = (a()) in b))";
  t_opt "c2_test12"
    "let a = (lambda: (1, 2, 3)) in
     let b = a() in
     let c = a() in
     c"
    "(alet a = (lambda(): (1, 2, 3)) in ((a()); (alet c = (a()) in c)))";
  t_opt "c2_test13"
    "let a = (lambda: (1, 2, 3)) in
    let b = a() in
    let c = b in
    let d = c in
    7"
    "(alet a = (lambda(): (1, 2, 3)) in ((a()); 7))";
  t_opt "c3_test1" "let a = 5 in 7" "7";
  t_opt "c3_test2" "let a = 5 in a" "5";
  t_opt "c3_test3"
    "let a = 5 in let b = 6 in let c = b in c"
    "6";
  t_opt "c3_test4"
    "let a = 6 in let c = (let b = 7 in a) in c"
    "6";
  t_opt "c3_test5" "if true: (let a = 6 in 5) else: 4" "(if true: 5 else: 4)";
  t_opt "c3_test6" "if false: (let a = 6 in 5) else: (let b = 4 in 6)" "(if false: 5 else: 6)";
  t_opt "c3_test7"
    "let five = 5 in let x = (lambda : five) in x()"
    "(alet x = (lambda(): 5) in (x()))";
  t_opt "c3_test8"
    "let five = 5 in let x = (lambda : 7) in x()"
    "(alet x = (lambda(): 7) in (x()))";
  t_opt "c3_test9"
    "let t = ((let a = 8 + 4 in 5), 4) in t"
    "(alet t = (5, 4) in t)";
  t_opt "c3_test10"
    "let t = ((let a = 8 + 4 in 5), 4) in begin t[1] := (let b = 4 in 7); t end"
    "(alet t = (5, 4) in (t[1] := 7; t))";
  t_opt "c3_test11"
    "let rec a = (lambda x: let b = 4 in 7) in a()"
    "(aletrec a = (lambda(x): 7) in (a()))";
  t_opt "c3_test12"
    "let a = 7 in if (a == 7): 1 else: 0"
    "(alet binop_5 = true in (if binop_5: 1 else: 0))";
  t_opt "c3_test13"
    "let a = 7 in let b = 4 in (a, 2, 3)"
    "(alet a = 7 in (a, 2, 3))";
  t_opt "c3_test14"
    "let a = (1, 2, 3) in (1 + (2 * 3)) + a[2]"
    "(alet a = (1, 2, 3) in (alet get_3 = a[2] in (7 + get_3)))";
  t_opt "c3_test15"
    "let a = (1, 2, 3) in let b = 2 in begin a[b] := 6; a end"
    "(alet a = (1, 2, 3) in (alet b = 2 in (a[b] := 6; a)))";
  t_opt "c3_test16"
    "let a = 7 in
    let b = (1, 2, 3) in
    let c =
      begin
        b[0] := 8;
        b
      end in
    a
    "
    "(alet b = (1, 2, 3) in (b[0] := 8; 7))";
  t_opt "c3_test17"
    "let a = 7 in
    let b = (1, 2, 3) in
    let c =
      begin
        b[0] := 8;
        b
      end in
    b
    "
    "(alet b = (1, 2, 3) in (b[0] := 8; b))";
  t_opt "c3_test18"
    "let a = 7 in
    let b = (1, 2, 3) in
    let c =
      begin
        b[0] := 8;
        b
      end in
    c
    "
    "(alet b = (1, 2, 3) in (b[0] := 8; b))";
  t_opt "c3_test19"
    "let a = print(5) in 7"
    "(print(5); 7)";
  t_opt "c3_test20"
    "let a = print(5) in
    let b = a in
    7"
    "(print(5); 7)";
  t_opt "c3_test21"
    "let a = add1(5) in 6"
    "6";
  t_opt "c3_test22"
    "let a = printStack(5 + 3) in 6"
    "(printStack(8); 6)";
  t_opt "c3_test23"
    "let a = (lambda: 6) in let b = a() in 5"
    "(alet a = (lambda(): 6) in ((a()); 5))";
  t_opt "c3_test24"
    "let a = (lambda: (1, 2, 3)) in let b = a() in 5"
    "(alet a = (lambda(): (1, 2, 3)) in ((a()); 5))";
  t_opt "c3_test25"
    "let a = 5 in
     let b = print(a) in
     let c = print(b) + 5 in
     a"
    "(alet b = print(5) in (alet unary_8 = print(b) in ((unary_8 + 5); 5)))";
]
;;

let struct_tests = [
  t "s_test1" "defstruct document (author) 7" "7";
  t "s_test2" "defstruct document (rating) makestruct document (100)" "(struct 100)";
  terr "s_test3" "makestruct document (100)" "The structname document, used at <s_test3, 1:0-1:25>, was not defined";
  terr "s_test4" "defstruct document (rating) makestruct document (a)"
    "The identifier a, used at <s_test4, 1:49-1:50>, is not in scope";
  (* TODO add arity checking for fieldnames in  wfn *)
  t "s_test5" "defstruct document (rating, isGood) makestruct document (100, true)" "(struct 100, true)";
  t "s_test6" "defstruct document (rating, isGood) let doc1 = makestruct document (100, true) in doc1" "(struct 100, true)";
  t "s_test7" "defstruct document (rating, isGood) let doc1 = makestruct document (100, true) in (document-rating doc1)" "100";
  t "s_test8" "defstruct document (rating, isGood) let doc1 = makestruct document (100, true) in (document-isGood doc1)" "true";
  t "s_test9" "defstruct document (rating, isGood)
              defstruct cabinet (d1, d2)
              let doc1 = makestruct document (100, true) in
                let doc2 = makestruct document (401, false) in
                  let cab1 = makestruct cabinet (doc1, doc2) in
                    (cabinet-d1 cab1)" "(struct 100, true)";
  t "s_test10" "defstruct document (rating, isGood)
               defstruct cabinet (d1, d2)
               let doc1 = makestruct document (100, true) in
                 let doc2 = makestruct document (401, false) in
                   let cab1 = makestruct cabinet (doc1, doc2) in
                     (document-rating (cabinet-d1 cab1))" "100";
  (* t "s_test11" "defstruct document (rating, isGood)
                let doc1 = makestruct document (100, true) in
                is document(doc1)"
                "true"; *)
  (* isdocument was ambiguous, so we used document? instead *)
  t "s_test11" "defstruct document (rating, isGood)
                let doc1 = makestruct document (100, true) in
                document?(doc1)"
    "true";
  terr "s_test12" "defstruct document (rating, isGood)
                let doc1 = makestruct document (100, true) in
                dog?(doc1)"
    "The structname dog, used at <s_test12, 3:16-3:26>, was not defined";
  t "s_test13" "defstruct document (rating, isGood)
                let doc1 = makestruct document (100, true) in
                document?(5)"
    "false";
  t "s_test14" "defstruct document (rating, isGood)
              let doc1 = makestruct document (100, true) in
              begin
                (document-isGood doc1) := false;
                (document-isGood doc1)
              end
              " "false";
  t "s_test15" "defstruct document (rating, isGood)
              let doc1 = makestruct document (100, true) in
              begin
                (document-isGood doc1) := false;
                let a = (lambda : 122) in (document-rating doc1) := a;
                doc1;
              end
              " "(struct <function>, false)";
  terr "s_test16" "(document-author doc1)"
    "The structname document, used at <s_test16, 1:0-1:22>, was not defined
The identifier doc1, used at <s_test16, 1:17-1:21>, is not in scope";
  terr "s_test17" "defstruct document (rating, isGood)
                  let doc1 = makestruct document (100, true) in
                  (document-author doc1)"
    "The struct document does not have field author used at <s_test17, 3:18-3:40>";
  terr "s_test18" "defstruct document (rating, isGood)
                  let doc1 = makestruct document (100, true) in
                  (document-author doc1) := 5"
    "The struct document does not have field author used at <s_test18, 3:18-3:45>";
  terr "s_test19" "defstruct document (rating, isGood)
                  let doc1 = makestruct document (100, true) in
                  (document-rating doc1) := (a + 5)"
    "The identifier a, used at <s_test19, 3:45-3:46>, is not in scope";
  terr "s_test20" "defstruct document (rating, isGood)
                    let doc1 = makestruct document (true) in
                    doc1"
    "The struct document expects 2 fields, received 1 at <s_test20, 2:31-2:57>";
  terr "s_test21" "defstruct document (rating, isGood)
                defstruct document (grade)
                7"
    "The struct document used at <s_test21, 2:16-2:42> has already been defined";
  t "s_test22" "defstruct dog (isGood, id)
                defstruct cat (isGood, id)
                defstruct julie (dog, cat)
                let dog1 = makestruct dog (true, 1) in
                let cat1 = makestruct cat (true, 2) in
                let me = makestruct julie (dog1, cat1) in
                me"
    "(struct (struct true, 1), (struct true, 2))";
  t_opt "s_test23" "defstruct score (grade1, grade2)
                let score1 = makestruct score (70 + 3, 5) in
                score1"
     "(defstruct score (grade1, grade2))(alet binop_5 = 73 in (alet score1 = (make-struct score (binop_5, 5)) in score1))";
  t_opt "s_test24" "defstruct score (grade1, grade2)
                  let a = 70 + 3 in
                  let b = a + 73 in
                  let score1 = makestruct score (a + 73, 5) in
                  score1"
     "(defstruct score (grade1, grade2))(alet binop_7 = 146 in (alet score1 = (make-struct score (binop_7, 5)) in score1))";
  t_opt "s_test25" "defstruct score (grade1, grade2)
                 let score1 = makestruct score (73, 5) in
                 begin
                   (score-grade1 score1) := let a = 70 + 3 in let b = a + 73 in a + 73;
                   score1
                 end"
    "(defstruct score (grade1, grade2))(alet score1 = (make-struct score (73, 5)) in (alet binop_6 = 146 in (alet structget_3 = (score-grade1 score1) := binop_6 in (structget_3; score1))))";
  t_opt "s_test26" "defstruct score (grade1, grade2) 5" "5";
  t "s_test27" "defstruct grade (listofscores, scorefn)
                let grade1 = makestruct grade ((70, 80, 90), (lambda x, y, z: (x + y + z))) in
                let a = (grade-scorefn grade1) in
                a(5, 6, 7)"
    "18";
  t "s_test28" "defstruct dog (isGood)
                let dogs = ((makestruct dog (true)), (makestruct dog (true))) in
                dogs"
     "((struct true), (struct true))";
  t "s_test29" "defstruct dog (isGood)
                let getdog = (lambda : (makestruct dog (true))) in
                getdog()"
    "(struct true)";

  t "s_test30" "let yo = (lambda : (lambda x: x)) in let a = yo() in a(5)" "5";
  t "s_test31" "let yo = (lambda : (lambda x: x)) in yo()" "<function>";
]
;;
(* defstruct document (rating, isGood) makestruct document (100, true) document-rating doc1 *)

(* assignment has us assume that higher order functions aren't passed impure arguments*)
(* t "c_test18" (* *)
   "let f = (lambda x: x(7)) in let a = (lambda x: x + 1) in f(a)"
   "(alet f = (lambda(x): (x(7))) in (alet a = (lambda(x): (x + 1)) in (f(a))))"; *)


let focus = [

]
;;


let suite =
  (* "suite">:::tests @ mutable_tuple_tests @ pair_tests @ oom @ wfn_tests
             @ regression_tests @ gc @ letrec_tests @ combined_tests *)
  "suite">:::struct_tests
  (* "suite">:::focus *)
;;

let () =
  run_test_tt_main suite
;;
