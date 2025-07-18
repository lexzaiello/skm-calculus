import Mathlib.Tactic

inductive LExpr where
  | var   : ℕ     → LExpr
  | app   : LExpr → LExpr → LExpr
  -- type, body
  | lam   : LExpr → LExpr → LExpr
  | m     : ℕ → LExpr
  | s     : ℕ → LExpr
  | k     : ℕ → LExpr
  | const : String → LExpr
  | hole  : LExpr
  | ty    : ℕ → LExpr

inductive SkExpr where
  | s     : ℕ      → SkExpr
  | k     : ℕ      → SkExpr
  | m     : ℕ      → SkExpr
  | call  : SkExpr → SkExpr → SkExpr
  | hole  : SkExpr
  | const : String → SkExpr
  | lam   : SkExpr → SkExpr → SkExpr
  | var   : ℕ      → SkExpr
  | ty    : ℕ → SkExpr
deriving BEq, Nonempty

declare_syntax_cat skmexpr
syntax "K" term                                                        : skmexpr
syntax "S" term                                                        : skmexpr
syntax "M" term                                                        : skmexpr
syntax "Ty" term                                                       : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax "?"                                                             : skmexpr
syntax ident                                                           : skmexpr
syntax "#" term                                                        : skmexpr
syntax "λ" ":" skmexpr "." skmexpr                                     : skmexpr
syntax "(" skmexpr ")"                                                 : skmexpr

syntax " ⟪ " skmexpr " ⟫ "                                             : term
syntax "SKM[ " skmexpr " ] "                                           : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K $e:term ⟫)                   => `(SkExpr.k $e)
  | `(⟪ S $e:term ⟫)                   => `(SkExpr.s $e)
  | `(⟪ M $e:term ⟫)                   => `(SkExpr.m $e)
  | `(⟪ Ty $e:term ⟫)                  => `(SkExpr.ty $e)
  | `(⟪ ? ⟫)                           => `(SkExpr.hole)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ λ : $t:skmexpr . $e:skmexpr ⟫) => `(SkExpr.lam ⟪$t⟫ ⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫) => `(SkExpr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

def mk_arrow (α β : SkExpr) := SKM[((((K 0) ((M 0) β)) α) β)]

infix:20 "~>" => mk_arrow

namespace SkExpr

def toStringImpl : SkExpr → String
    | .s n          => s!"S {n}"
    | .k n          => s!"K {n}"
    | .m n          => s!"M {n}"
    | .ty n         => s!"Ty {n}"
    | SKM[(((((K 0) ((M 0) β)) α)) β_e)] => s!"{α.toStringImpl} → {β.toStringImpl}"
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

def extract_in (t : SkExpr) : SkExpr :=
  match t with
    | SKM[((((((K n) _β) α) β)))] => α
    | x => (.const s!"bruh1 : {x}")

def extract_out_lam (t : LExpr) : LExpr :=
  match t with
    | (.lam _ t_out) => t_out
    | _ => .hole

def extract_out (t : SkExpr) : SkExpr :=
  match t with
    | SKM[((((((K n) _β) α) β)))] => β
    | x => (.const s!"bruh2 : {x}")

partial def normalize' (e : SkExpr) (t : SkExpr) : SkExpr :=
  match e with
    | .lam t_in (.var 0) =>
      let t' := normalize' t SKM[((M 0) t)]

      SKM[((((((S 0) #(t' ~> (t' ~> t'))) #(t' ~> t')) t') (((K 0) t') #(t' ~> t'))) (((K 0) t') t'))]
    | .lam t (.var $ n + 1) =>
      let t' := normalize' t SKM[((M 0) t)]

      SKM[((((K 0) t') ?) #(.var n))]
    | .k n  => SKM[(K n)]
    | .ty n => SKM[Ty n]
    | .m n => SKM[(M n)]
    | .s n => SKM[(S n)]
    | .lam t_in (.call lhs rhs) =>
      let t_in' := normalize' t_in SKM[((M 0) t_in)]
      let t_out := extract_out t

      -- Note that it's not exactly clear what the type of lhs is
      -- since it could theoretically be something besides a lambda abstraction
      -- we can't derive it top down. we don't have enough information from
      -- the type of the parent abstraction to know the "in-between" type
      -- in the children.

      normalize' SKM[((((((S 0)
        #(t_in' ~> (SKM[?] ~> t_out)))
        #(t_in' ~> SKM[?])) t_in')
        #(normalize' (.lam t_in' lhs) (t_in' ~> (SKM[?] ~> t_out))))
        #(normalize' (.lam t_in' rhs) (t_in' ~> SKM[?])))] t
    | .lam t x => SKM[((((K 0) #(normalize' t SKM[((M 0) t)])) ?) #(normalize' x SKM[?]))]
    | .const c => .const c
    | .call lhs rhs =>
      let t_rhs := SKM[((M 0) rhs)]

      SKM[(#(normalize' lhs (t_rhs ~> t)) #(normalize' rhs t_rhs))]
    | .var n => .var n
    | .hole => .hole

partial def to_sk (e : LExpr) : SkExpr :=
  match e with
    | .ty n => .ty n
    | .lam t (.var 0) =>
      let t' := to_sk t (.app (.m 0) t)

      SKM[
           ((((((S 0) #(t' ~> (t' ~> t'))) #(t' ~> t')) t')
             (((K 0) t') #(t' ~> t')))
             (((K 0) t') t'))
      ]
    | .lam t_in (.var $ n + 1) =>
      let t_in' := to_sk t_in (.app (.m 0) t_in)
      let inner_lifted_cnst := SKM[((((K 0) ?) ?) #(.var n))]

      normalize' (.lam t_in' inner_lifted_cnst) (t_in' ~> SKM[((M 0) inner_lifted_cnst)])
    | .k n => SKM[K n]
    | .m n => SKM[M n]
    | .s n => SKM[S n]
    | (.app lhs rhs) =>
      let t_rhs := (.app (.m 0) rhs)
      let t_lhs := (.lam t_rhs t)

      normalize' SKM[((#(to_sk lhs t_lhs)) #(to_sk rhs t_rhs))] $ to_sk t (.app (.m 0) t)
    | .lam t (.app lhs rhs) =>
      let t' := to_sk t (.app (.m 0) t)

      let out_t := extract_out_lam t

      let t_rhs := (.app (.m 0) rhs)
      let t_lhs := (.lam t_rhs out_t)

      normalize' SKM[(((((((S 0) ?) ?) t') #(.lam t' $ to_sk lhs t_lhs))) #(.lam t' $ to_sk rhs t_rhs))] t
    | .lam t_in x =>
      let t_in' := to_sk t_in (.app (.m 0) t_in)
      let out_t := extract_out_lam t
      let x' := to_sk x out_t
      let out_t' := to_sk out_t (.app (.m 0) out_t)
      let t' := to_sk t (.app (.m 0) t)

      normalize' (.lam t_in' SKM[#(normalize' x' out_t')]) t'
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

def arrow := (LExpr.lam (.ty (.lam .ty (.app (.app (.app .k (.app .m (.var 0))) (.var 1)) (.var 0))))
  |> normalize' ∘ to_sk

#eval SKM[S 0] ~> SKM[K 0]

#eval extract_in $ SKM[S 0] ~> SKM[K 0]
#eval extract_out $ SKM[S 0] ~> SKM[K 0]

#eval arrow

/-
Issue with Type expression.

Type n is supposed to contain every expression with a universe level of n.
For example, K₀ α β : K₁ (M β) α

"Type" expression is kind of synonymous with M.

K₀ is our "prop". Or rather, all universe levels < 0 are prop.
You cannot construct an expression of type K₀.
We essentially want a name for every expression which is a possible type.

We are in combinator land after all. Why don't we make the type of

we want the type of any "callable" expression to
eventually reduce to something of the form K_{some n} (M b) a b

K₀ : K₁
(K₀ α β : K₁

K₀ : ->

K₀ A B : (-> A B = K (M B) A B)

K₀ A B should be A -> B -> A

A is duplicated

K₀ A B : 

Why do we need universes again?

What if we had some way to "wrap" a type to feed it into K?
And we can say unify K, S, under this type?

Idea: M (-> x y) = Type
-> x y = K (M y) y x = y

WAIT A MINUTE.
Any expression which is not computable is a type
M (K α) = Type
M K = Type

Or, we want K (M

Ok switch things up again.

-> is ∀. So -> should return the type of x in
K x y = x
-> α β = K (M β) α β

Yeah this is still fine. This works for everything.

But we still want (-> α β : Type).
K (M β) α β is another "incomplete" expression.
or "noncomputable"

K (M β) α β does not actually evaluate to anything.

What about computable types? CoC has computation in types?
We can still have a judgment rule that permits this.

-> A B : Type

I think this is good.
-/
