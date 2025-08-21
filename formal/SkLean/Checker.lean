import SkLean.Ast3

def check (e : Expr) : Option Expr :=
  match e with
    | SKM[(((K t_x) x) y)] =>
      if check x == some t_x then
        t_x
      else
        none
    | SKM[((((((S t_x) x) t_y) y) t_z) z)] =>
      if all [check x == some t_x , check y == some t_y, check z == some t_z] then
        SKM[((x t_z) (y t_z))]
      else
        
