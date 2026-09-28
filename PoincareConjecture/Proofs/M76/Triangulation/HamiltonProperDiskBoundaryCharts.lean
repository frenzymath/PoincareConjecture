import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBoundaryPatch
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinderHalfspace
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

private theorem exists_centered_linear_halfspace_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : OpenPartialHomeomorph E E)
    (hH : LocallyPiecewiseAffineOn H H.source)
    (hHi : LocallyPiecewiseAffineOn H.symm H.target)
    {p : E} (ell : E →ᴬ[ℝ] ℝ) (hzero : ell (H p) = 0) :
    ∃ G : OpenPartialHomeomorph E E,
      G.source = H.source ∧ G p = 0 ∧
      LocallyPiecewiseAffineOn G G.source ∧
      LocallyPiecewiseAffineOn G.symm G.target ∧
      ∀ x, ell.toAffineMap.linear (G x) = ell (H x) := by
  let a : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-(H p))
  let G := H.trans a.toHomeomorph.toOpenPartialHomeomorph
  have hGs : G.source = H.source := by
    change H.source ∩ H ⁻¹' (univ : Set E) = H.source
    rw [preimage_univ, inter_univ]
  have hG : LocallyPiecewiseAffineOn G G.source :=
    (locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ).comp hH
  have hGi : LocallyPiecewiseAffineOn G.symm G.target :=
    hHi.comp (locallyPiecewiseAffineOn_affine a.symm.toContinuousAffineMap isOpen_univ)
  refine ⟨G, hGs, ?_, hG, hGi, ?_⟩
  · change -H p + H p = 0
    exact neg_add_cancel _
  · intro x
    change ell.toAffineMap.linear (-H p + H x) = ell (H x)
    rw [show -H p + H x = H x - H p by abel]
    have h := ell.toAffineMap.linearMap_vsub (H x) (H p)
    change ell.toAffineMap.linear (H x - H p) = ell (H x) - ell (H p) at h
    rwa [hzero, sub_zero] at h

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_proper_disk_boundary_pair_chart {R D : Set V3}
    (hR : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hDR : D ⊆ R)
    (b : closedBall (0 : V2) 1 ≃ₜ D) (hb : b.IsFinitePL)
    (hproper : ∀ x : closedBall (0 : V2) 1,
      (b x : V3) ∈ frontier R ↔ (x : V2) ∈ sphere (0 : V2) 1)
    {p : V3} (hpD : p ∈ D) (hpR : p ∈ frontier R) :
    ∃ K : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
      p ∈ K.source ∧ K.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn K K.source ∧
      LocallyPiecewiseAffineOn K.symm K.target ∧ K p = 0 ∧
      (∀ x ∈ K.source, x ∈ R ↔ 0 ≤ (K x).1.1) ∧
      ∀ x ∈ K.source, x ∈ D ↔ 0 ≤ (K x).1.1 ∧ (K x).2 = 0 := by
  classical
  let z : closedBall (0 : V2) 1 := b.symm ⟨p, hpD⟩
  have hbz : (b z : V3) = p := congrArg Subtype.val (b.apply_symm_apply ⟨p, hpD⟩)
  have hz : (z : V2) ∈ sphere (0 : V2) 1 := (hproper z).mp (hbz.symm ▸ hpR)
  have hcube : coordinateCylinder (Finset.univ : Finset (Fin 2)) =
      closedBall (0 : V2) 1 := by
    ext x
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [coordinateCylinder, mem_ofPred_eq, Finset.mem_univ, forall_const,
      Real.norm_eq_abs]
  have hzfront : (z : V2) ∈ frontier (coordinateCylinder (Finset.univ : Finset (Fin 2))) := by
    rw [hcube, frontier_closedBall _ one_ne_zero]
    exact hz
  obtain ⟨ell, v, H0, hv, hzH0, hH0z, hellz, hH0, hhalf0⟩ :=
    exists_coordinateCylinder_halfspace_chart Finset.univ hzfront
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hv' : ell.toAffineMap.linear v = 1 := hv
    rw [he] at hv'
    norm_num at hv'
  have hellH : ell (H0 z) = 0 := by rw [hH0z]; exact hellz
  obtain ⟨H, hHs, hHz, _, hHi, hHval⟩ :=
    exists_centered_linear_halfspace_chart H0 hH0.1 hH0.2 ell hellH
  have hhalf (x : V2) (hx : x ∈ H.source) :
      x ∈ closedBall (0 : V2) 1 ↔ 0 ≤ ell.toAffineMap.linear (H x) := by
    rw [hHval, ← hcube]
    exact hhalf0 x (hHs.subset hx)
  have hfront := H0.isImage_frontier_of_affine_nonneg (K := closedBall (0 : V2) 1) ell hell
    (fun x hx => by rw [← hcube]; exact hhalf0 x hx)
  have hboundary (x : V2) (hx : x ∈ H.source) :
      x ∈ sphere (0 : V2) 1 ↔ ell.toAffineMap.linear (H x) = 0 := by
    rw [hHval, ← frontier_closedBall (0 : V2) one_ne_zero]
    exact (hfront.apply_mem_iff (hHs.subset hx)).symm
  obtain ⟨psi, w, G0, hw, hpG0, hpsi0, hcompat, hRhalf⟩ := hR.halfspace p hpR
  have hpsi : psi.toAffineMap.linear ≠ 0 := by
    intro he
    have hw' : psi.toAffineMap.linear w = 1 := hw
    rw [he] at hw'
    norm_num at hw'
  have hG0 : LocallyPiecewiseAffineOn G0 G0.source := by
    have h := (hcompat ()).1
    exact (h.mono G0.open_source (fun _ hx => ⟨mem_univ _, hx⟩)).congr (fun _ _ => rfl)
  have hG0i : LocallyPiecewiseAffineOn G0.symm G0.target := by
    have h := (hcompat ()).2
    exact (h.mono G0.open_target (fun _ hx => ⟨hx, mem_univ _⟩)).congr (fun _ _ => rfl)
  obtain ⟨G, hGs, hGp, hG, hGi, hGval⟩ :=
    exists_centered_linear_halfspace_chart G0 hG0 hG0i psi hpsi0
  have hGfront := G0.isImage_frontier_of_affine_nonneg psi hpsi hRhalf
  have hpositive (x : closedBall (0 : V2) 1) (hx : (b x : V3) ∈ G.source) :
      0 ≤ psi.toAffineMap.linear (G (b x)) := by
    rw [hGval]
    exact (hRhalf (b x) (hGs.subset hx)).mp (hDR (b x).property)
  have hzero (x : closedBall (0 : V2) 1) (hx : (b x : V3) ∈ G.source) :
      psi.toAffineMap.linear (G (b x)) = 0 ↔ (x : V2) ∈ sphere (0 : V2) 1 := by
    rw [hGval]
    exact (hGfront.apply_mem_iff (hGs.subset hx)).trans (hproper x)
  obtain ⟨K, hpK, hKG, hKt, hK, hKi, hK0, hKA, hKD⟩ :=
    exists_boundary_pair_chart_of_actual_disk_charts (by simp) b hb z H
      (hHs.symm.subset hzH0) hHz hHi ell.toAffineMap.linear hell hhalf hboundary G
      (by rw [hbz, hGs]; exact hpG0) (by rw [hbz, hGp]) hG hGi
      psi.toAffineMap.linear hpsi hpositive hzero
  refine ⟨K, hbz ▸ hpK, hKt, hK, hKi, ?_, ?_, hKD⟩
  · rwa [hbz] at hK0
  · intro x hx
    have hh : x ∈ R ↔ 0 ≤ psi.toAffineMap.linear (G x) := by
      rw [hGval]
      exact hRhalf x (hGs.subset (hKG hx))
    exact hh.trans (hKA x hx)

end PoincareConjecture.M76.HamiltonIndexOne
