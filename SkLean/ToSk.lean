import Mathlib.Tactic

inductive LExpr where
  | var   : ℕ     → LExpr
  | app   : LExpr → LExpr → LExpr
  -- type, body
  | lam   : LExpr → LExpr → LExpr
  | m     : LExpr
  | s     : LExpr
  | k     : LExpr
  | const : String → LExpr
  | hole  : LExpr
  | ty    : LExpr

inductive SkExpr where
  | s     : ℕ      → SkExpr
  | k     : ℕ      → SkExpr
  | m     : ℕ      → SkExpr
  | call  : SkExpr → SkExpr → SkExpr
  | hole  : SkExpr
  | const : String → SkExpr
  | lam   : SkExpr → SkExpr → SkExpr
  | var   : ℕ      → SkExpr
  | ty    : SkExpr
deriving BEq, Nonempty

declare_syntax_cat skmexpr
syntax "K" term                    : skmexpr
syntax "S" term                    : skmexpr
syntax "M" term                    : skmexpr
syntax "(" skmexpr skmexpr ")"     : skmexpr
syntax "?"                         : skmexpr
syntax ident                       : skmexpr
syntax "#" term                    : skmexpr
syntax "λ" ":" skmexpr "." skmexpr : skmexpr
syntax "(" skmexpr ")"             : skmexpr

syntax " ⟪ " skmexpr " ⟫ "         : term
syntax "SKM[ " skmexpr " ] "       : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K $e:term ⟫)                   => `(SkExpr.k $e)
  | `(⟪ S $e:term ⟫)                   => `(SkExpr.s $e)
  | `(⟪ M $e:term ⟫)                   => `(SkExpr.m $e)
  | `(⟪ Ty ⟫)                          => `(SkExpr.ty)
  | `(⟪ ? ⟫)                           => `(SkExpr.hole)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ λ : $t:skmexpr . $e:skmexpr ⟫) => `(SkExpr.lam ⟪$t⟫ ⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(SkExpr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

def mk_arrow (α β : SkExpr) := SKM[((((K 0) ((M 0) β)) α) β)]

infix:20 "~>" => mk_arrow

namespace SkExpr

def toStringImpl : SkExpr → String
    | .s n          => s!"S {n}"
    | .k n          => s!"K {n}"
    | .m n          => s!"M {n}"
    | .ty           => s!"Ty"
    | SKM[((((K 0) ((M 0) β)) α) β_e)] => s!"{α.toStringImpl} → {β.toStringImpl}"
    | .call lhs rhs => s!"({lhs.toStringImpl} {rhs.toStringImpl})"
    | .const str    => s!"{str}"
    | .hole         => "_"
    | .lam t body  => s!"λ :{t.toStringImpl} . {body.toStringImpl}"
    | .var v        => s!"var {v}"

instance : ToString SkExpr where
  toString := SkExpr.toStringImpl

partial def eval_n (n : ℕ) (e : SkExpr) : SkExpr :=
  if n = 0 then
    e
  else
    let e' := match e with
      | SKM[(((((K _n) _α) _β) x) _y)] => x
      | SKM[(((((((S _n) _α) _β) _γ) x) y) z)] => eval_n n.pred SKM[((x z) (y z))]
      | SKM[(lhs rhs)] => eval_n n.pred.pred SKM[((#(eval_n n.pred lhs)) (#(eval_n n.pred rhs)))] 
      | x => x

      eval_n  n.pred.pred.pred e'

end SkExpr

partial def normalize' (e : SkExpr) : SkExpr :=
  match e with
    | .lam t (.var 0) =>
      let t' := normalize' t

      SKM[((((((S 0) #(t' ~> (t' ~> t'))) #(t' ~> t')) t') (((K 0) #(normalize' t')) ?)) (((K 0) #(normalize' t')) ?))]
    | .lam t (.var $ n + 1) =>
      let t' := normalize' t

      SKM[((((K 0) t') ?) #(.var n))]
    | .k n => SKM[(K n)]
    | .ty  => SKM[Ty]
    | .m n => SKM[(M n)]
    | .s n => SKM[(S n)]
    | .lam t (.call lhs rhs) =>
      let t' := normalize' t

      normalize' SKM[((((((S 0) ?) ?) t') #(normalize' (.lam t' lhs))) #(normalize' (.lam t' rhs)))]
    | .lam t x => SKM[((((K 0) #(normalize' t)) ?) #(normalize' x))]
    | .const c => .const c
    | .call lhs rhs => SKM[(#(normalize' lhs) #(normalize' rhs))]
    | .var n       => .var n
    | .hole => .hole

partial def to_sk (e : LExpr) : SkExpr :=
  match e with
    | .ty => .ty
    | .lam t (.var 0) =>
      let t' := to_sk t

      SKM[
           ((((((S 0) ?) ?) t')
             (((K 0) t') #(t' ~> t')))
             (((K 0) t') t'))
      ]
    | .lam t (.var $ n + 1) =>
      let t' := to_sk t

      normalize' (.lam t' SKM[((((K 0) ?) ?) #(.var n))])
    | .k => SKM[K 0]
    | .m => SKM[M 0]
    | .s => SKM[S 0]
    | (.app lhs rhs) => normalize' SKM[((#(to_sk lhs)) #(to_sk rhs))]
    | .lam t (.app lhs rhs) =>
      let t' := to_sk t
      normalize' SKM[(((((((S 0) ?) ?) t') #(.lam t' $ to_sk lhs))) #(.lam t' $ to_sk rhs))]
    | .lam t x =>
      let t' := to_sk t

      normalize' (.lam t' SKM[#(normalize' ∘ to_sk $ x)])
    | .const c => .const c
    | .var 0       => .var 0
    | .var v       => .var v
    | .hole        => .hole

/-
We want -> : Type → Type → Type. But we don't really have a way to represent Type.
One possible solution is adding a universe expression that contains all combinators of a given order.
But then what do we do with expressions whose universe level is not immediately clear?
We don't want to have separate arrow expression typings for different combinators, ideally.
We want one. And we don't want to just add a fucking hole in the language that makes -> polymorphic.
That's very hacky. Intuitively, this is something with M. One way to do this is with a fixpoint.
This seems kind of complicated, but if -> has access to its own type (is "inductive"), then we can
type it, since M gives us the type of something. This seems like it won't really work though.
However, this could be how we add inductive types to the language! With a fixpoint.

New arrow expression (lc, convert to SKM):

\(a : M a, a)

bruhhhh momento. The question is, does this adhere to our current typing?
We already know that the type of any expression is e : M e, if it is well-typed.
There is no reason why we can't do this for ->....
HOWEVER, M e only works if there is a valid typing of it.
This is circular, and doesn't work. We ought to have some explict typing of this.
This is kinda ass though. We need some like concrete typing.

Perhaps some way to represent any arbitrary type? But we're constrained by universe levels, too.
And we don't want to add an expression to the language that just adds an escape hole.
Because we will be able to use that expression in nother places.

\\(M\\) is the obvious candidate. M is well-typed.
I don't see why we can't type -> similarly. HOWEVER, we are modifying the typing of M.
We are still using universe hierarchies, but not K₀ : K₁. K₀ : S₀ (->)
((K₀ ℕ ℝ) : (S₀ (->) ℕ ℝ = -> ℝ (ℕ ℕ))).

Essentially, we just want the type of any expression to be something like

K (M a) B a.

theoretically, we could do this for the arrow expression itself, but then we're recursing
like I said, we could just make its type M a, but then we can't typecheck it.
We don't want any holes in the language. So what is the type of ->? I mean, we don't really have to explicitly type it.

We can just derive the type from its value, I guess. This is kinda ass though. We want at the top level to know what its type is.

We could theoretically do this with a fixpoint. This could be how we do inductive types.

Ok, another idea. -> A B : Type? I don't really know how this makes sense, because literally everything is a type.
except K₀. K₀ is not a type. it's just an expression. K₁ is though. WAIT A SECOND.....
the thing is though, if we add a type expression, then literally everything is a type.
like what. then we can just have an escape hatch in the language. we don't want to do that.

I mean, we could say that M : Type. This is another important question, because like...
what the fuck is M?

M : Type????? Also .... typing of M? M is necessarily polymorphic. like it is untyped.
M works with any expression. it doesn't have a coherent typing.
M₀ : M₁. This could be our escape hatch.

M₀ e : M₁ (M₁ e).

smth like this fr.

but how do we capture the input type of this function? input types are kind of ammbiguous.
They're explicit for K and S via the arrow expression, but still kinda confusing, since
we don't have any notion of a "Type" epxression. so the typing of M is also obscure.
whenever we do a function call we need to match up the input types.
orrrrrrr.... we can just check if (e : t) arg (t arg : ?) t arg typechecks.
This could work. yeah. based. this bubbles up.
this could potentially simplify everything.
but what's our base case? realistically we need some way to properly encode the input type explicitly.
but M is necessarily polymoprhic. if we specify the input type to M, we have literally defeated the entire
point of M. this could potentially just be our like base case.

we could say that M e for anything is well-typed if e has a type.
yeah. this works. so M is polymorphic. any argument works, as long as that argument is well-typed.

so, what's the type of ->? -> A B = K (M A) B A.
fixpoint idea again. could theoretically have -> be similar, and rely on M.

-> : M. -> A B = (M A B). This is not good.
we want -> to typecheck similarly to M where any two arguments work, so long as they have a valid type.

so, ideally we want to rely only on M and -> in our typing of ->.

-> : M ->?
-> : -> M?

Only two possibilities. -> A B : M -> A B. bruhhhhh. that's based. genuinely based. like holy shit.

Why do we need an explicit typing of ->? Because we want it to propogate down to the actual calls within.
So we need a legit concrete type. Realistically, we don't need an actual expression to represent this.
We just need an expression to encapsulate all types.
Honestly I think type is fine. Type is a universe containing all K_{n} and S_{n} where n > 0.
Remember. no type can have the type K₀. K₀ is our Prop.
-/

def arrow_type := SKM[((((K 0) Ty) Ty) Ty)]

def arrow := (.lam .ty (.lam .ty (.app (.app (.app .k (.app .m (.var 0))) (.var 1)) (.var 0))))
  |> normalize' ∘ to_sk

#eval SKM[S 0] ~> SKM[K 0]

def extract_in (t : SkExpr) : SkExpr :=
  match t with
    | SKM[((((((K n) _β) α) β)))] => α
    | x => (.const s!"bruh1 : {x}")

def extract_out (t : SkExpr) : SkExpr :=
  match t with
    | SKM[((((((K n) _β) α) β)))] => β
    | x => (.const s!"bruh2 : {x}")

#eval extract_in $ SKM[S 0] ~> SKM[K 0]
#eval extract_out $ SKM[S 0] ~> SKM[K 0]

-- S₁ : Ty, K₁ : Ty, but S₁ : K₁ is not true.

#eval SKM[((arrow Ty) Ty)] |> SkExpr.eval_n 20
