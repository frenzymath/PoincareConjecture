import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinderHalfspace

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry

theorem exists_centered_compatible_halfspace_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E) (H : OpenPartialHomeomorph X E)
    (hcompat : ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E)
    (x : X) (ell : E →ᴬ[ℝ] ℝ) (hzero : ell (H x) = 0) :
    ∃ G : OpenPartialHomeomorph X E,
      G.source = H.source ∧ G x = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      ∀ y, ell.toAffineMap.linear (G y) = ell (H y) := by
  let a : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-(H x))
  let G := H.trans a.toHomeomorph.toOpenPartialHomeomorph
  have hGs : G.source = H.source := by
    change H.source ∩ H ⁻¹' (univ : Set E) = H.source
    rw [preimage_univ, inter_univ]
  have ha : a.toHomeomorph.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E :=
    ⟨locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine a.symm.toContinuousAffineMap isOpen_univ⟩
  refine ⟨G, hGs, ?_, ?_, ?_⟩
  · change -H x + H x = 0
    exact neg_add_cancel _
  · intro i
    simpa only [G, ← OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans (hcompat i) ha
  · intro y
    change ell.toAffineMap.linear (-H x + H y) = ell (H y)
    rw [show -H x + H y = H y - H x by abel]
    have h := ell.toAffineMap.linearMap_vsub (H y) (H x)
    change ell.toAffineMap.linear (H y - H x) = ell (H y) - ell (H x) at h
    rwa [hzero, sub_zero] at h

end Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_centered_boundary_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {x : X} (hx : x ∈ frontier R) :
    ∃ (G : OpenPartialHomeomorph X V3) (A : V3 →ₗ[ℝ] ℝ),
      x ∈ G.source ∧ G x = 0 ∧ A ≠ 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ R ↔ 0 ≤ A (G y)) ∧
      ∀ y ∈ G.source, y ∈ frontier R ↔ A (G y) = 0 := by
  obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := he.halfspace x hx
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    norm_num at hval
  obtain ⟨G, hGs, hGx, hGcompat, hvalue⟩ :=
    exists_centered_compatible_halfspace_chart e H hcompat x ell hzero
  have hfront := H.isImage_frontier_of_affine_nonneg ell hell hhalf
  refine ⟨G, ell.toAffineMap.linear, hGs.symm.subset hxH, hGx, hell, hGcompat, ?_, ?_⟩
  · intro y hy
    rw [hvalue]
    exact hhalf y (hGs.subset hy)
  · intro y hy
    rw [hvalue]
    exact (hfront.apply_mem_iff (hGs.subset hy)).symm

theorem exists_centered_disk_rim_chart {z : V2} (hz : z ∈ sphere (0 : V2) 1) :
    ∃ (H : OpenPartialHomeomorph V2 V2) (B : V2 →ₗ[ℝ] ℝ),
      z ∈ H.source ∧ H z = 0 ∧ B ≠ 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ closedBall (0 : V2) 1 ↔ 0 ≤ B (H x)) ∧
      ∀ x ∈ H.source, x ∈ sphere (0 : V2) 1 ↔ B (H x) = 0 := by
  have hcube : coordinateCylinder (Finset.univ : Finset (Fin 2)) =
      closedBall (0 : V2) 1 := by
    ext x
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [coordinateCylinder, mem_ofPred_eq, Finset.mem_univ, forall_const,
      Real.norm_eq_abs]
  have hzfront : z ∈ frontier (coordinateCylinder (Finset.univ : Finset (Fin 2))) := by
    rw [hcube, frontier_closedBall _ one_ne_zero]
    exact hz
  obtain ⟨ell, v, H0, hv, hzH0, hH0z, hellz, hH0, hhalf⟩ :=
    exists_coordinateCylinder_halfspace_chart Finset.univ hzfront
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    norm_num at hval
  have hzero : ell (H0 z) = 0 := by rw [hH0z]; exact hellz
  let e : Unit → OpenPartialHomeomorph V2 V2 := fun _ => OpenPartialHomeomorph.refl V2
  have hcompat : ∀ i, (e i).symm.trans H0 ∈ piecewiseAffineGroupoid V2 := by
    intro i
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
      using hH0
  obtain ⟨H, hHs, hHz, hHcompat, hvalue⟩ :=
    exists_centered_compatible_halfspace_chart e H0 hcompat z ell hzero
  have hH : H ∈ piecewiseAffineGroupoid V2 := by
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
      using hHcompat ()
  have hfront := H0.isImage_frontier_of_affine_nonneg ell hell hhalf
  refine ⟨H, ell.toAffineMap.linear, hHs.symm.subset hzH0, hHz, hell, hH.1, hH.2, ?_, ?_⟩
  · intro x hx
    rw [hvalue, ← hcube]
    exact hhalf x (hHs.subset hx)
  · intro x hx
    rw [hvalue, ← frontier_closedBall (0 : V2) one_ne_zero, ← hcube]
    exact (hfront.apply_mem_iff (hHs.subset hx)).symm

end PoincareConjecture.M76
