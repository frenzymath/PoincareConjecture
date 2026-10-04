import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.Mathlib.CompatibleInverseChart
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHypersurfaceCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHalfspaceSubcomplex

/-!
# Actual finite patches on the original domain boundary

Cut a finite neighborhood in a supplied halfspace chart by its
exact zero hyperplane. All inverse values lie on the original
frontier, with PL certificates in the unchanged atlas.
See Hudson 1969, pp. 12--19 and rigidity derivation 004.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}

/-- Every original boundary point has an actual finite planar
patch in a compatible halfspace chart. Its entire inverse carrier
is on the original frontier, and it contains a relative frontier
neighborhood of that point. See rigidity derivation 004. -/
theorem PLDomain.exists_polyhedral_boundary_patch (he : PLDomain e R)
    {x : X} (hx : x ∈ frontier R) :
    ∃ (B : OpenPartialHomeomorph X V3) (K : SimplicialComplex ℝ V3) (V : Set X),
      K.faces.Finite ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ B.source ∧
      K.space ⊆ B.target ∧ MapsTo B.symm K.space (frontier R) ∧
      (∀ y ∈ V, y ∈ frontier R → B y ∈ K.space) ∧
      PolyhedralPLInCharts e B.symm K.space ∧
      ∀ i, B.symm.trans (e i) ∈ piecewiseAffineGroupoid V3 := by
  classical
  obtain ⟨ell, v, B, hellv, hxB, _, hcompat, hhalf⟩ := he.halfspace x hx
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hzero : ell.contLinear v = 0 := by
      change ell.toAffineMap.linear v = 0
      rw [h]
      rfl
    exact zero_ne_one (hzero.symm.trans hellv)
  have hfront := B.isImage_frontier_of_affine_nonneg ell hell hhalf
  have hcompatible (i : ι) : B.symm.trans (e i) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hcompat i)
  obtain ⟨P, hP, hxP, hPt⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      (isCompact_singleton : IsCompact {B x}) B.open_target
      (singleton_subset_iff.mpr (B.map_source hxB))
  obtain ⟨K, hK, hKP⟩ :=
    P.exists_finite_triangulation_inter_halfspaces hP {ell.toAffineMap, -ell.toAffineMap}
  have hplane : K.space = P.space ∩ {z | ell z = 0} := by
    rw [hKP]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, AffineMap.coe_neg, Pi.neg_apply]
    change (z ∈ P.space ∧ ell z ≤ 0 ∧ -ell z ≤ 0) ↔
      (z ∈ P.space ∧ ell z = 0)
    rw [neg_nonpos, and_congr_right_iff]
    intro _
    exact le_antisymm_iff.symm
  have hKt : K.space ⊆ B.target := fun z hz => hPt ((hplane.subset hz).1)
  have hKfront : MapsTo B.symm K.space (frontier R) := by
    intro z hz
    exact (hfront.symm_apply_mem_iff (hKt hz)).mpr (hplane.subset hz).2
  let V := B.source ∩ B ⁻¹' interior P.space
  have hV : IsOpen V := B.isOpen_inter_preimage isOpen_interior
  have hBPL : PolyhedralPLInCharts e B.symm K.space :=
    polyhedralPLInCharts_of_compatible_chart_inverse e he.cover B hcompatible K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK)
      hKt
  refine ⟨B, K, V, hK, hV, ⟨hxB, hxP (mem_singleton _)⟩,
    inter_subset_left, hKt, hKfront, ?_, hBPL, hcompatible⟩
  intro y hy hyfront
  apply hplane.symm.subset
  exact ⟨interior_subset hy.2, (hfront.apply_mem_iff hy.1).mpr hyfront⟩

end PoincareMT.M76
