import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePL.exists_interior_chart {C : Set E} {T : Set F}
    {e : C ≃ₜ T} (he : e.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ H : OpenPartialHomeomorph E F,
      H.source = interior C ∧ H.target = interior T ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      FinitePiecewiseAffineOn (H : E → F) C ∧
      FinitePiecewiseAffineOn (H.symm : F → E) T ∧
      (∀ x : C, H x = (e x : F)) ∧
      ∀ y : T, H.symm y = (e.symm y : E) := by
  obtain ⟨g, hg, heg⟩ := he.symm
  obtain ⟨f, hf, hef⟩ := he
  have hPL : e.IsFinitePL := ⟨f, hf, hef⟩
  have hmap : MapsTo f (interior C) (interior T) := by
    intro x hx
    rw [← hef ⟨x, interior_subset hx⟩]
    exact hPL.mem_interior hdim (x := ⟨x, interior_subset hx⟩) hx
  have hinvmap : MapsTo g (interior T) (interior C) := by
    intro y hy
    rw [← heg ⟨y, interior_subset hy⟩]
    exact hPL.symm.mem_interior hdim.symm (x := ⟨y, interior_subset hy⟩) hy
  have hleft : LeftInvOn g f (interior C) := by
    intro x hx
    rw [← hef ⟨x, interior_subset hx⟩, ← heg, e.symm_apply_apply]
  have hright : LeftInvOn f g (interior T) := by
    intro y hy
    rw [← heg ⟨y, interior_subset hy⟩, ← hef, e.apply_symm_apply]
  let H : OpenPartialHomeomorph E F :=
    { toFun := f
      invFun := g
      source := interior C
      target := interior T
      map_source' := hmap
      map_target' := hinvmap
      left_inv' := hleft
      right_inv' := hright
      continuousOn_toFun := hf.continuousOn.mono interior_subset
      continuousOn_invFun := hg.continuousOn.mono interior_subset
      open_source := isOpen_interior
      open_target := isOpen_interior }
  exact ⟨H, rfl, rfl,
    hf.locallyPiecewiseAffineOn_of_subset_interior isOpen_interior Subset.rfl,
    hg.locallyPiecewiseAffineOn_of_subset_interior isOpen_interior Subset.rfl,
    hf, hg, fun x => (hef x).symm, fun y => (heg y).symm⟩

end Homeomorph
