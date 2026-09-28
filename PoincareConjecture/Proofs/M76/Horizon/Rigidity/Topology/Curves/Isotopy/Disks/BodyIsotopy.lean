import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.AlexanderTrack
import PoincareConjecture.Proofs.M76.Mathlib.RelativeAlexanderIsotopy

set_option autoImplicit false
open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_unit_halfspace_body_joint_PL_isotopy
    {C : Set E} {e : C ≃ₜ C} (he : e.IsFinitePL)
    (hfix : ∀ x : C, (x : E) ∈ frontier C → e x = x)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ (H : unitInterval → C ≃ₜ C) (F Fi : (ℝ × E) → E),
      H 0 = Homeomorph.refl C ∧ H 1 = e ∧
      (∀ t : unitInterval, ∀ x : C, (x : E) ∈ frontier C → H t x = x) ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ C) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ C) ∧
      (∀ t : unitInterval, ∀ x : C, F (t, x) = (H t x : E)) ∧
      (∀ t : unitInterval, ∀ x : C, Fi (t, x) = ((H t).symm x : E)) := by
  classical
  have hcompact : IsCompact C := by obtain ⟨f, hf, _⟩ := he; exact hf.isCompact
  have hC := hcompact.isClosed
  let g := e.closedExtension hC hfix
  have hstar : StarConvex ℝ (0 : E) C := by
    intro y hy a b ha hb hab
    rw [hrep] at hy ⊢
    intro i
    simp only [smul_zero, zero_add, map_smul, smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left (hy i) hb).trans (by nlinarith)
  have hfixed (t : unitInterval) (x : E) (hx : x ∉ C) :
      g.alexanderFamily (t : ℝ) x = x :=
    g.alexanderFamily_fixed_compl_starConvex hstar
      (fun _ h => e.closedExtension_apply_notMem hC hfix h) t.property hx
  have hmem (t : unitInterval) (x : E) :
      x ∈ C ↔ g.alexanderFamily (t : ℝ) x ∈ C := by
    constructor
    · intro hx
      by_contra hout
      have h := hfixed t _ hout
      have heq := (g.alexanderFamily (t : ℝ)).injective h
      exact hout (heq.symm ▸ hx)
    · intro hx
      by_contra hout
      rw [hfixed t x hout] at hx
      exact hout hx
  let H : unitInterval → C ≃ₜ C := fun t =>
    (g.alexanderFamily (t : ℝ)).sets (Set.ext (hmem t))
  have hHval (t : unitInterval) (x : C) :
      (H t x : E) = g.alexanderFamily (t : ℝ) x := rfl
  have hHival (t : unitInterval) (x : C) :
      ((H t).symm x : E) = (g.alexanderFamily (t : ℝ)).symm x := rfl
  have hPL := he.closedExtension_alexander_joint_finitePL_on_prism hC hfix L hL hrep
  refine ⟨H, (fun p => g.alexanderFamily p.1 p.2),
    (fun p => (g.alexanderFamily p.1).symm p.2), ?_, ?_, ?_, hPL.1, hPL.2,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · ext x
    rw [hHval]
    simp
  · ext x
    rw [hHval]
    change g.alexanderFamily 1 x = (e x : E)
    simpa only [alexanderFamily_one] using
      e.closedExtension_apply_mem hC hfix x.property
  · intro t x hx
    apply Subtype.ext
    exact g.alexanderFamily_fixed_relative hstar
      (fun _ h => e.closedExtension_apply_notMem hC hfix h) t.property (Or.inr hx)

end Homeomorph
