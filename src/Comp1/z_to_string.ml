(* for debugging *)

let rec pos_to_string p =
  match p with
  | XI p -> String.concat "" [pos_to_string p; "1"]
  | XO p -> String.concat "" [pos_to_string p; "0"]
  | XH -> "1"

let z_to_string a =
  match a with
  | Z0 -> "0"
  | Zpos p -> pos_to_string p
  | Zneg p -> String.concat "" ["-"; pos_to_string p]
