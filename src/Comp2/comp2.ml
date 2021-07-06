open Definition

let rec to_nat n =
  if n = 0
  then O
  else S (to_nat (n - 1))

let rec printws n acc =
  let t = Sys.time() in
  let res = w (to_nat (acc)) in
  Printf.printf "W%i = %s (in %fs)\n" acc (Uint63.to_string res) (Sys.time() -. t);
  Stdlib.flush stdout;
  if n = 0
  then ()
  else printws (n - 1) (acc + 1)

let rec printintlist l acc =
  match l with
  | Nil -> ()
  | Cons (h,l) -> Printf.printf "W%i = %s\n" acc (Uint63.to_string h);
                  printintlist l (acc + 1)

let _ =
  if 2 < Array.length Sys.argv
  then printintlist (table (Uint63.of_int(int_of_string(Sys.argv.(1))))) 0
  else printws (int_of_string(Sys.argv.(1))) 0
