import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSlab

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure AlexanderCollarSlab (S : Set E) (A : E →ᵃ[ℝ] ℝ) (q : E) (β : ℝ) where

  width_pos : 0 < β

  apex_mem : q ∈ S

  apex_height : A q = 0

  upper : E → ℝ

  collar : Set E

  residual : Set E

  residualComplex : SimplicialComplex ℝ E

  chart : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
    p.2 ∈ Icc 0 (upper p.1)} ≃ₜ collar

  chart_finitePL : chart.IsFinitePL

  residual_finite : residualComplex.faces.Finite

  residual_space : residualComplex.space = residual

  cover : collar ∪ residual = S ∩ {x | A x ∈ Icc 0 β}

  residual_zero : residual ∩ {x | A x = 0} ⊆ {q}

  roof_contact : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)},
    (chart p : E) ∈ residual ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1

  upper_finitePL : FinitePiecewiseAffineOn upper (S ∩ {x | A x = 0})

  upper_bounds : ∀ x ∈ S ∩ {x | A x = 0}, upper x ∈ Icc 0 β

  apex_upper : upper q = 0

  upper_pos : ∀ x ∈ S ∩ {x | A x = 0}, x ≠ q → 0 < upper x

  height : ∀ p, A (chart p) = (p : E × ℝ).2

  bottom : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)},
    (p : E × ℝ).2 = 0 → (chart p : E) = (p : E × ℝ).1

  bottom_covered : S ∩ {x | A x = 0} ⊆ collar

def AlexanderHalfSlab.toCollarSlab {S : Set E} {A : E →ᵃ[ℝ] ℝ}
    {q : E} {β : ℝ} (M : AlexanderHalfSlab S A q β) :
    AlexanderCollarSlab S A q β where
  width_pos := M.width_pos
  apex_mem := M.apex_mem
  apex_height := M.apex_height
  upper := M.upper
  collar := M.collar
  residual := M.residual
  residualComplex := M.residualComplex
  chart := M.chart
  chart_finitePL := M.chart_finitePL
  residual_finite := M.residual_finite
  residual_space := M.residual_space
  cover := M.cover
  residual_zero := M.residual_zero
  roof_contact := M.roof_contact
  upper_finitePL := M.upper_finitePL
  upper_bounds := M.upper_bounds
  apex_upper := M.apex_upper
  upper_pos := M.upper_pos
  height := M.height
  bottom := M.bottom
  bottom_covered := M.bottom_covered

theorem AlexanderCollarSlab.chart_eq_apex_of_base_eq {S : Set E} {A : E →ᵃ[ℝ] ℝ}
    {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
    (p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)}) (hp : (p : E × ℝ).1 = q) :
    (M.chart p : E) = q := by
  have hz : (p : E × ℝ).2 = 0 := by
    apply le_antisymm _ p.property.2.1
    simpa only [hp, M.apex_upper] using p.property.2.2
  exact (M.bottom p hz).trans hp

theorem AlexanderCollarSlab.apex_mem_residual {S : Set E} {A : E →ᵃ[ℝ] ℝ}
    {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β) : q ∈ M.residual := by
  let p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} :=
    ⟨(q, 0), ⟨M.apex_mem, M.apex_height⟩, le_rfl, M.apex_upper.symm.le⟩
  have hp : (M.chart p : E) = q := M.chart_eq_apex_of_base_eq p rfl
  have hmem : (M.chart p : E) ∈ M.residual :=
    (M.roof_contact p).mpr M.apex_upper.symm
  rw [hp] at hmem
  exact hmem

end Geometry
