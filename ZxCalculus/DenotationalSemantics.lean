import ZxCalculus.AST
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Denotational Semantics for ZX-Calculus

We interpret ZX diagrams as linear maps between finite-dimensional complex vector spaces.
An n-wire diagram corresponds to ℂ^(2^n).
-/

open Complex

-- Helper: vector space for n qubits
abbrev Qubits (n : ℕ) := Fin (2^n) → ℂ

-- Linear maps between qubit spaces
abbrev LinMap (n m : ℕ) := Qubits n →ₗ[ℂ] Qubits m

noncomputable section
-- Interpret generators (to be filled in)
def interpGen (g : Generator') : (Σ n m : ℕ, LinMap n m) :=
match g with
  | .empty => ⟨0, 0, LinearMap.id⟩
  | _ => sorry

-- Main interpretation
def interp : ZxTerm' → (Σ n m : ℕ, LinMap n m)
  | .gen g => interpGen g
  | f ; g =>
      let ⟨nf, mf, φf⟩ := interp f
      let ⟨ng, mg, φg⟩ := interp g
      ⟨nf, mg, sorry⟩  -- φg.comp φf, need to handle mf = ng
  | f ⊗ g => sorry
end
