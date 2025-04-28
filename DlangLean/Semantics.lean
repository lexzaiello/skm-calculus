import Mathlib.Tactic

inductive SkExpr where
  | S    : SkExpr
  | K    : SkExpr
  | Call : SkExpr → List SkExpr → SkExpr

-- It is possible for programs in the SK combinator calculus
-- to never terminate.
--
-- Thus, we cannot express them in Lean.
-- The question is, what subset of the SK combinators can we prove properties of?
-- Note that the K combinator is guaranteed to terminate
def eval' : SkExpr → SkExpr
  | SkExpr.Call SkExpr.K (x::_::_) => x
  | x => x

-- What if we embed a proof of termination in our code?
-- What would that look like?
--
-- An elementary way of doing this is with simple typing
-- with simple typing, we cannot easily express
-- recursive functions beyond the limits of what we can
-- express manually

-- For example:
-- (K 1   : Const → Const)
-- (S 1 2 : Const → ?? doesn't typecheck)

-- K 1 2 : Const
--
-- K with one argument is necessarily polymorphic
-- Is it possible to express the type of (K 1 : ?)
--
-- Obviously K 1 is a map from anything to 1
-- we would like to express this nicely
-- in the dependent typing way
--
-- Say, then, that K (α : Type) (β : Type) : α → β → α
--
-- In our notation: K : (K : E → E → E)
--
-- But, how can K have two different types?
-- Suppose for simplicity for now that the S and K combinators
-- are polymorphic in a nondependent way
-- Just generic
--
-- I don't really like this, but we're just experimenting for now
-- However, in a corollary to lambda calculus, the lambda is not a dependent function
-- it just exists
-- So, maybe this is fine

-- Let us say, then, that nondependent polymorphic K is hidden to the user
-- Then, we can easily define polymorphic dependent K, as above
--
-- K₀ : E → E → E
-- K  : K'
--
-- This solve our turtles all the way down situation.

inductive Expr where
  | s       : ℕ      → Expr
  | k       : ℕ      → Expr
  | implies : Expr   → Expr → Expr
  | const   : String → Expr
  | call    : Expr   → Expr → Expr
deriving BEq

-- Flatten the type signature of the expr first
-- Intuitively our type system should prevent nontermination
--
-- Since everything must have a type
-- and we don't really have a way to do unstructured recirsion

-- First, let us prove that a given term terminates
-- We have to decide whether terminate will rely on eval
-- Or whether eval will rely on terminate
-- I think we can reasonably determine whethher something terminates
-- based on whether the type terminates

-- Inconsistency check
-- e : e, this does NOT make sense
-- otherwise, the type of EVERYTHING is e
-- We will need type universes of some kind
--
-- type 0 is our base case
-- but, how the fuck do we "strongly normalize" that shit
-- just have it normalize to itself? how is that not the same problem
-- well nothing but type is of type 0
-- so it should be find
-- it is not possible to express below type 0
-- What the hell are sorts for then, does that not
-- fuck shit up more? :skull:
--
-- Let's say that s₀ does not work with our base type
-- I don't really know yet how this will limit our language
-- Let us say that s₀ is ONLY used for creating the dependently typed
-- s
-- therefore, it is just a mpapping from types to types

-- Other thought: what about making syntax relevant in our language?
-- This may be too abstract, not sure yet
-- We can do lean style elaboration later I think
-- or we may want to choose something lisp style early on

-- No type inference for now
-- The expr layer will be explicitly typed

-- if K is of type       K : K₀
-- then we should assume S is of type : S₀
-- Depends on what the type of S₀ is
--
-- S₀ : (E → E → E) → (E → E) → E → E
-- kind of, let's try it out
-- S : (S₀ : E →

-- Final K definition:
-- K₀ is polymorphic. Therefore, K : K₀ := K₀
-- This is consistent. K : ∀ α β, α → β → α
-- for any α.

-- S definition:
-- Naively, S : S₀ := S₀
-- Let's expandt this to lean terms with ∀:
-- S₀ : ∀ α β γ, (α → β → γ) → (α → β) → α → γ
-- S  : ∀ α β γ, (α → β → γ) → (α → β) → α → γ := S₀
--- Again, since S₀ is polymorphic.

-- Thoughts on partial evaluation:
--
-- can test if a function normalizes to S or K
-- by applying a future value to it

-- Evaluate the S combinator
    -- S S K K =>
        --   S K (K K) =>
        --   K K (K K) => K
    -- Some facts:
    -- ty_1 is guaranteed to be a function
    -- in fact, even if it is K, the call
    -- is still guaranteed to work
    -- For example, K takes two args: K x y = x
    -- however, K x y z = ??
    -- this is defined. K x z
    -- This is nice, since
    -- any combination of S and K is guaranteed to work
    -- Especially for s₀ and k₀, which are polymorphic
    -- Question: how do we prevent infinite recursion with s₀ and k₀,
    -- since they are essentially untyped?
    -- Let us say that S₀ only works on types
    -- However, everything is a type.
    -- This is problematic
    -- UNLESS, we guarantee that there is no occurrence of S₀
    -- or K₀ inside the expression
    -- Since we know S and K to terminate, since they are well-typed
    -- In this way, we will not consider S and S₀ to be strictly the same
    -- Or typeed the same
    --
    -- For example, s₀ s₀ _ _, s₀ _ s₀ _, s₀ _ _ s₀. Any combination
    -- of these is "undefined?"
    -- since they could infinitely recurse
    -- However, using S or K inside is "fine"
    -- but not just K or S, a well-typed K or S (not sure about this)

-- When is the S₀ combinator guaranteed to terminate?
-- and can we restrict the types that s₀ works on?
-- How about lisp style, s₀ takes syntax?
-- S₀ : (Syntax → Syntax → Syntax) → (Syntax → Syntax) → Syntax → Syntax
-- We can't really define syntax without inductive types,
-- which we don't have yet
-- Can we do S₀ : (Type → Type → Type) → (Type → Type) → Type → Type?
-- But, now we have to separate out Type from Expr, which I don't really want to do
-- However, we can't guarantee termination if a non-typedd thing appears inside
-- a type.
-- Stratifying our type system may fix this.
-- Say we only have two universes for now:
-- well-typed objects
-- and polymorphic objects
-- However, we want to be able to define K as such
-- K : K₀ := K₀
-- And K₀
-- What the hell is the type of K₀
-- Obviously a function from a b => a
-- but we don't want it to include s₀ or k₀
-- so, K₀ (α : Type 1) (β : Type 1) : α → β → α
-- Type 1 : Type 2
-- therefore, K₀ (u v : ℕ) (α : Type u) (β : Type v) : Type (max (u + 1) (v + 1))
-- I think this actually works for just K, actually
-- And we don't need k₀
-- However, again, we need some way to refer to these parameters
-- Let's say we do some under the hood magic
--
-- Such that K (Type 1) (Type 2) x y : Type 3
-- What is the type of partially applied K?
-- e.g., K (n + 1) : K n := K n
-- How the fuck can we make this not turtles all the way down
-- What inhabits Type 0?
-- Constant, perhaps
-- Bool : Type 0
-- ℕ    : Type 0
-- K    (u v : ℕ') (a : Type u) (b : Type v) (x : a) (y : b) : a := b
-- K 0 0 
-- K (u v : ℕ') : K (u + 1) (v + 1) := K u v (Type (u + 1))
-- Example usage K n (K 0 (type 0) (type 0) Bool ℕ)
-- (K 0 Bool ℕ) True 0 => True
-- K (universe : ℕ') (x : 
-- K of arity n can only be used of types that occupy that arity
-- for example K 1

-- Let's make this simpler
-- K : (Type : α) → (Type : β) → α → β→ α

-- Main issue: we can't really define K in terms of itself
-- Or, can we
-- How do inductive types work?
-- Let's make an inductive K
-- Goal : K (Type n₁) (Type n₂) : K (Type n₁ + 1) (Type n₂ + 1)
-- Can think of n₁ as the type of the value
-- Therefore, x is of the type type n₁
-- so it lives in type universe TYpe n₁ + 1
-- K (Type 1) (Type 1) : K (Type 2) (Type 2) := 
-- Let's define this:
-- K (Type 1) (Type 1) (x : Type 2) (y : Type 2) : Type 2
-- K (String) (Nat) "bruh" 0 : String := "bruh"
-- This is fucking sick
--
-- If we can represent pairs in the SK combinators,
-- Then we can represent types
-- K := fun x => fun y => (x, fun a => fun b => aa)
--
-- "looking up" types according
-- to parameters is incredibly difficult,
-- as we have no nmaed parameters!
-- however, we have the S combinator
--
-- HOWEVER, we again run into the issue
-- of cyclicality
--
-- I am deep in the fucking meat grinder
--
-- If we can take the type
-- and copy it in some position
-- embedded in the actual code
-- then we can infer the actual type?
--
-- Say we have some K_t : Type → Type → Type
-- Now we can define a more general K
-- For example: K := K_t

-- I like our inductive definition the most

-- Intuitively, we can translate every lambda calculus program to an SK combinator program.
-- And we can create the calculus of constructions in lambda calculus programs
-- But can we create the calculus of constructions in SK combinator programs?

-- How is it even possible to encode a type depending on a term if we do not have bindings for parameters
-- Parameters are nameless

-- Let's go back to our s₀ k₀ construction
-- let's even assume that S and K themselves are polymorphic

-- What are we formally trying to prove?
-- We are trying to prove that the calculus of constructions is expressible in the SK combinators

-- There is a decomposition of all parameter-named functions into anonymously named functions
def s (α β γ : Type) : (α → β → γ) → (α → β) → α → γ
  | x, y, z => x z (y z)

def k (α β : Type) : α → β → α
  | x, _ => x


inductive LExpr where
  -- Bind var de brujin index, ty, body
  | abstraction : ℕ → LExpr → LExpr → LExpr
  | fall        : ℕ → LExpr → LExpr → LExpr
  -- T and P, CoC
  | ty          : ℕ → LExpr
  | prp         : LExpr
  -- Bound variable
  | bvar        : ℕ      → LExpr
  | app         : LExpr  → LExpr → LExpr
deriving BEq

open LExpr

-- inference rules:
-- 1. prop is of type type
-- 2. if A is of type K, and x is of type A, then x is of type A
  -- This seems trivial?
-- 3. if A is of type K, and x is of type A, and B has type L
-- then (∀x:A.B) is of type L
-- this is like return type matching the type of the whole expr can be inferred to be L
-- 4. M:(λx:A.B)

-- Note that reduction happens in inference, too
-- as per 6. https://en.wikipedia.org/wiki/Calculus_of_constructions

def eval_infer (e : LExpr) : StateT (List $ (ℕ × (LExpr × LExpr))) Option (LExpr × LExpr) :=
  match e with
  | p@prp => pure $ (p, ty 0)
  | t@(ty n) => pure $ (t, (ty $ n + 1))
  | f@(fall idx e_ty e_body)  => do
    -- Set type and normal form of bound vars with idx
    -- to the inferred type of e_ty
    StateT.modifyGet (⟨(), (idx, ← eval_infer e_ty) :: .⟩)

    -- Use new inference rules to infer body type
    -- This is the type of the entire expression
    pure (f, (← eval_infer e_body).snd)
  | a@(abstraction idx e_ty e_body) => do
    -- Pretty similar thing to forall
    let norm_e_ty ← eval_infer e_ty
    StateT.modifyGet (⟨(), (idx, norm_e_ty) :: .⟩)

    pure $ (a, fall idx norm_e_ty.snd (← eval_infer e_body).snd)
  | app (fall idx bind_ty body) rhs => do
    let (norm_rhs, ty_rhs) ← eval_infer rhs

    -- These are technically also the same if they are beta
    -- normally equivalent
    if ty_rhs != (← eval_infer (bind_ty)).snd then
      none

    StateT.modifyGet (⟨(), (idx, (norm_rhs, ty_rhs)) :: .⟩)

    eval_infer body
  | bvar idx => do
    match (← StateT.get) |> List.filter λ(idx₂, _) => idx == idx₂ with
    | (_, (v, ty_var))::_ => pure (v, ty_var)
    | List.nil => none
  | _ => none
