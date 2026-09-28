import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Reflection.HalfspaceMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.LocalPLInvariance
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

theorem exists_doubled_halfspace_open_chart
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {f : P × ℝ → P × ℝ} {A : Set P} {r : ℝ} (hr : 0 < r)
    (hA : (0 : P) ∈ interior A)
    (hf : FinitePiecewiseAffineOn f (A ×ˢ Icc (0 : ℝ) r))
    (hfi : InjOn f (A ×ˢ Icc (0 : ℝ) r)) (hf0 : f 0 = 0)
    (hfpos : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, 0 ≤ (f z).2)
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, (f z).2 = 0 ↔ z.2 = 0) :
    ∃ H : OpenPartialHomeomorph (P × ℝ) (P × ℝ),
      H.source = interior (A ×ˢ Icc (-r) r) ∧ (0 : P × ℝ) ∈ H.source ∧ H 0 = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧ LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z, H z = doubleHalfspaceMap f z) ∧
      (∀ z ∈ H.source, 0 ≤ (H z).2 ↔ 0 ≤ z.2) ∧
      ∀ z ∈ H.source, 0 ≤ z.2 → H z = f z := by
  let F := doubleHalfspaceMap f
  let S := A ×ˢ Icc (-r) r
  have hF : FinitePiecewiseAffineOn F S := finitePiecewiseAffineOn_doubleHalfspaceMap hf hfzero
  have hFi : InjOn F S := doubleHalfspaceMap_injOn hfi hfpos hfzero
  obtain ⟨D, hD, hDval⟩ := hF.exists_homeomorph_image hFi
  obtain ⟨p, hp, hpval⟩ := hD.symm
  have hpf (z : P × ℝ) (hz : z ∈ S) : p (F z) = z := by
    have hh := hpval (D ⟨z, hz⟩)
    rw [D.symm_apply_apply] at hh
    exact (congrArg p (hDval ⟨z, hz⟩)).symm.trans hh.symm
  have hlocal : LocallyPiecewiseAffineOn F (interior S) :=
    hF.locallyPiecewiseAffineOn_of_subset_interior isOpen_interior subset_rfl
  have hopen : IsOpen (F '' interior S) := hlocal.isOpen_image_of_injOn rfl (hFi.mono interior_subset)
  let H : OpenPartialHomeomorph (P × ℝ) (P × ℝ) := {
    toFun := F
    invFun := p
    source := interior S
    target := F '' interior S
    map_source' := fun z hz => mem_image_of_mem F hz
    map_target' := by rintro _ ⟨z, hz, rfl⟩; rw [hpf z (interior_subset hz)]; exact hz
    left_inv' := fun z hz => hpf z (interior_subset hz)
    right_inv' := by rintro _ ⟨z, hz, rfl⟩; rw [hpf z (interior_subset hz)]
    continuousOn_toFun := hF.continuousOn.mono interior_subset
    continuousOn_invFun := hp.continuousOn.mono (image_mono interior_subset)
    open_source := isOpen_interior
    open_target := hopen }
  refine ⟨H, rfl, ?_, ?_, hlocal, H.locallyPiecewiseAffineOn_symm hlocal,
    fun _ => rfl, fun z hz => doubleHalfspaceMap_nonneg_iff hfpos hfzero (interior_subset hz),
    fun _ _ hz => doubleHalfspaceMap_positive f hz⟩
  · change (0 : P × ℝ) ∈ interior (A ×ˢ Icc (-r) r)
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hA, neg_lt_zero.mpr hr, hr⟩
  · exact (doubleHalfspaceMap_positive f le_rfl).trans hf0

end PoincareConjecture.M76
