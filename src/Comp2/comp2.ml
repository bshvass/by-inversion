
open Definition

let rec to_nat n =
  if n = 0
  then O
  else S (to_nat (n - 1))

let rec printws n acc _ =
  if n = -1
  then ()
  else printws (n - 1) (acc + 1) (print_string(String.concat (Uint63.to_string(w (to_nat (acc)))) [String.concat (string_of_int acc) ["W"; " = "]; "\n"]))

let _ = printws (int_of_string(Sys.argv.(1))) 0 ()
