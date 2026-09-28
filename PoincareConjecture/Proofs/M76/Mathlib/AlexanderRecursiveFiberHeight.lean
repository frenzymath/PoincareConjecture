import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.VariableHeightBand










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem AlexanderCollarSlab.exists_fiber_strict_height_bound
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    {g : E → ℝ} (hg : FinitePiecewiseAffineOn g M.collar)
    (v : E) (hv : A.linear v = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ H : E → E,
      (∀ x ∈ M.collar, H x = x + (t * g x) • v) →
      ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)},
        t * g (p : E × ℝ).1 ≤ A (H (M.chart p)) ∧
          (0 < (p : E × ℝ).2 → t * g (p : E × ℝ).1 < A (H (M.chart p))) := by
  let D : Set (E × ℝ) := {p | p.1 ∈ S ∩ {x | A x = 0} ∧
    p.2 ∈ Icc 0 (M.upper p.1)}
  obtain ⟨f, hf, hval⟩ := M.chart_finitePL
  have hmap : MapsTo f D M.collar := by
    intro p hp
    rw [← hval ⟨p, hp⟩]
    exact (M.chart ⟨p, hp⟩).property
  have hgf : FinitePiecewiseAffineOn (g ∘ f) D := hg.comp hf hmap
  obtain ⟨δ, hδ, hmono⟩ := hgf.exists_strictMonoOn_band_perturbation
    (B := S ∩ {x | A x = 0}) (lower := fun _ => 0) (upper := M.upper)
  refine ⟨δ, hδ, fun t ht H hformula p => ?_⟩
  have hbottom : (g ∘ f) ((p : E × ℝ).1, 0) = g (p : E × ℝ).1 := by
    change g (f ((p : E × ℝ).1, 0)) = g (p : E × ℝ).1
    let z : D := ⟨((p : E × ℝ).1, 0), p.property.1,
      le_rfl, (M.upper_bounds _ p.property.1).1⟩
    rw [← hval z, M.bottom z rfl]
  have hA : A (H (M.chart p)) = (p : E × ℝ).2 + t * g (M.chart p) := by
    rw [hformula (M.chart p) (M.chart p).property, add_comm (M.chart p : E)]
    change A ((t * g (M.chart p)) • v +ᵥ (M.chart p : E)) = _
    rw [A.map_vadd, map_smul, hv, M.height p]
    change t * g (M.chart p) * 1 + (p : E × ℝ).2 =
      (p : E × ℝ).2 + t * g (M.chart p)
    ring
  rw [hA]
  have hz : (0 : ℝ) ∈ Icc 0 (M.upper (p : E × ℝ).1) :=
    ⟨le_rfl, (M.upper_bounds _ p.property.1).1⟩
  have hm := hmono t ht _ p.property.1
  constructor
  · have h := hm.monotoneOn hz p.property.2 p.property.2.1
    change 0 + t * (g ∘ f) ((p : E × ℝ).1, 0) ≤
      (p : E × ℝ).2 + t * (g ∘ f) (p : E × ℝ) at h
    rwa [hbottom, zero_add, Function.comp_apply, ← hval p] at h
  · intro hp
    have h := hm hz p.property.2 hp
    change 0 + t * (g ∘ f) ((p : E × ℝ).1, 0) <
      (p : E × ℝ).2 + t * (g ∘ f) (p : E × ℝ) at h
    rwa [hbottom, zero_add, Function.comp_apply, ← hval p] at h

end Geometry
