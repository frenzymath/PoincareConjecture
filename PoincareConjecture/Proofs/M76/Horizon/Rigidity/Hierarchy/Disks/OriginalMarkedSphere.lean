import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedFiniteModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CappedEulerCount
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLCubeSphereModel
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage










set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_original_simplyConnected_marked_sphere
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Nonempty X]
    (e : ι → OpenPartialHomeomorph X V3) (hX : IsCompact (univ : Set X))
    {R S M : Set X} (he : PLDomain e R) (hS : IsCompact S)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ psi (T y) = 0))
    (hrim : Disjoint S M) [SimplyConnectedSpace S] :
    Nonempty (ChartwisePLSphere e S) := by
  classical
  obtain ⟨s, F, K, B, g, hFc, hFi, _, hK, _, _, hKs, hBs,
      hgPL, hgi, _, hgS, hpure, hcofaces, hlinks, _⟩ :=
    exists_original_marked_surface_finite_incidence_with_rim_polygons
      e hX he hS hlocal
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let HS : S ≃ₜ K.space :=
    (Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn F S hFi.injOn)
      ((hFc.comp continuous_subtype_val).subtype_mk _)).trans
        (Homeomorph.setCongr hKs.symm)
  let : SimplyConnectedSpace K.space := HS.symm.toHomotopyEquiv.simplyConnectedSpace
  have hBempty : B.space = ∅ := by
    rw [hBs, disjoint_iff_inter_eq_empty.mp hrim, image_empty]
  have hnoface (t : Finset (s → ℝ × V3)) : t ∉ B.faces := by
    intro ht
    obtain ⟨x, hx⟩ := B.nonempty_of_mem_faces ht
    have hxB := B.convexHull_subset_space ht (subset_convexHull ℝ _ hx)
    simp only [hBempty, mem_empty_iff_false] at hxB
  have htwo (t : Finset (s → ℝ × V3)) (ht : t ∈ K.faces) (htc : t.card = 2) :
      {u : Finset (s → ℝ × V3) | u ∈ K.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2 := by
    simpa only [if_neg (hnoface t)] using hcofaces t ht htc
  have hcount := HamiltonIntervalTorus.surfaceEulerCount_eq_two_of_simplyConnected
    K hK hpure htwo (by convert! hlinks)
  obtain ⟨H, hH⟩ := K.exists_sphere_model_of_surfaceEulerCount_eq_two hK hpure htwo
    (by convert! hlinks) (isConnected_iff_connectedSpace.mpr inferInstance) hcount
  have hcv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  obtain ⟨b, hb⟩ := hH.exists_unit_cube_sphere_model (isCompact_halfBall (Or.inl rfl)) hcv
    (interior_halfBall_nonempty (h := 1) (Or.inl rfl)) (by simp [Module.finrank_prod])
  have hsphere := exists_chartwisePLSphere_image K hgPL hgi (Subset.refl K.space) b hb
  rwa [hgS] at hsphere

end PoincareConjecture.M76
