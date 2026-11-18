open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);

  Test ("Student-Provided Tests For Problem 4.4", [
    ("Interpret 1", assert_eqf (fun () -> interpret [("x", 3L)] (Neg (Neg (Neg (Var "x"))))) (-3L));
    ("Interpret 2", assert_eqf (fun () -> interpret [("x", 3L); ("y", -3L)] (Neg (Neg (Add ((Var "y"), (Var "x")))))) (0L));
    ("Interpret 3", assert_eqf (fun () -> interpret [("x", 3L); ("y", 5L)] (Mult (Add (Var "y", Const 4L), Neg (Var "x")))) (-27L));
    ("Interpret 4", assert_eqf (fun () -> interpret [("x", 3L)] (Neg (Add (Const 5L, Mult (Const 0L, Var "x"))))) (-5L));
  ]);

  Test ("Student-Provided Tests For Problem 4.5", [
    ("optimize4", assert_eqf (fun () -> optimize (Add(Var "x", Neg (Var "x")))) (Const 0L));
    ("optimize5", assert_eqf (fun () -> optimize (Neg (Neg (Const 5L)))) (Const (5L)));
    ("optimize6", assert_eqf (fun () -> optimize (Neg (Add ((Const (-5L)),(Const 5L)) ))) (Const (0L)));
    ("optimize7", assert_eqf (fun () -> optimize (Neg (Neg (Neg (Var "x"))))) (Neg (Var "x")));
    ("optimize8", assert_eqf (fun () -> optimize (Mult ((Const 0L), (Var "x")) )) (Const 0L));
    ("optimize9", assert_eqf (fun () -> optimize (Add ((Neg ((Neg (Const (-5L))))),(Neg (Add (Const (-2L), Const (-3L))))))) (Const (0L)));
    ("optimize10", assert_eqf (fun () -> optimize (Neg (Neg (Neg (Const 8L))))) (Const (-8L)));
  ]);

  Test ("Student-Provided Tests For Problem 5", [
    ("Compile 1", assert_eqf (fun () -> run [] (compile (Add(Const 4L, Const 4L)))) (8L));
    ("Compile 2", assert_eqf (fun () -> run [] (compile (Mult (Const 4L, Const 4L)))) (16L));
    ("Compile 3", assert_eqf (fun () -> run [] (compile (Add(Const 4L, Neg (Const (-4L)))))) (8L));
    ("Compile 4", assert_eqf (fun () -> run [] (compile (Neg (Neg (Neg (Const 8L)))))) (-8L));
    ("Compile 5", assert_eqf (fun () -> run [("x", 3L)] (compile (Neg (Neg (Neg (Var "x")))))) (-3L));
    ("Compile 6", assert_eqf (fun () -> run [("x", -3L)] (compile (Neg (Neg (Neg (Var "x")))))) (3L));
    ("Compile 7", assert_eqf (fun () -> run [("x", -3L)] (compile (Mult((Var "x"), Const 0L)))) (0L));
    ("Compile 8", assert_eqf (fun () -> run [("x", -3L)] (compile (Mult((Var "x"), Const 0L)))) (0L));
    ("Compile 9", assert_eqf (fun () -> run [("x", -3L)] (compile (Mult((Var "x"), Add (Const 2L, Var "x"))))) (3L));
    ("Compile 10", assert_eqf (fun () -> run [("x", 3L); ("x", -3L)] (compile (Mult((Var "x"), Add (Const 2L, Var "x"))))) (15L));
    ("Compile 11", assert_eqf (fun () -> run [("y", 3L); ("x", -3L)] (compile (Mult((Var "x"), Add (Const 2L, Var "x"))))) (3L));
  ]);
] 
