import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeChartWitnesses
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDualRegionFacts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalRegionCofaces









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)




theorem exists_edge_normal_witnesses
    (p : (T.marked 2).vertices) {s t : Finset (T.index → ℝ × V3)}
    (hps : (p : T.index → ℝ × V3) ∈ s) (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 2) (ht : t ∈ (T.marked 2).faces) (htcard : t.card = 3)
    (hst : s ⊆ t) :
    ∃ u ∈ T.ambient.faces, ∃ v ∈ T.ambient.faces,
      t ⊆ u ∧ t ⊆ v ∧ u.card = 4 ∧ v.card = 4 ∧
      u.centroid ℝ id ∈ T.dualRegionRim s ∧
      v.centroid ℝ id ∈ T.dualRegionRim s ∧
      T.height p (u.centroid ℝ id) < 0 ∧ 0 < T.height p (v.centroid ℝ id) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let ell : C3 →ₗ[ℝ] ℝ :=
    T.weight (T.chart_index p) • LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have h := congrArg (fun m : C3 →ₗ[ℝ] ℝ => m ((0, 0), 1)) he
    apply T.weight_nonzero (T.chart_index p)
    change T.weight (T.chart_index p) * 1 = 0 at h
    simpa only [mul_one] using h
  have htstar : t ∈ (T.ambient.closedStar p).faces := by
    refine ⟨T.marked_le 2 ht, ?_⟩
    simpa only [Finset.insert_eq_of_mem (hst hps)] using (T.marked_le 2 ht)
  have hzero : ∀ x ∈ t, ell (T.chart (T.chart_index p) (T.inverse x)) = 0 := by
    intro x hx
    change T.height p x = 0
    have hxD := (T.marked 2).subset_space ht hx
    exact (T.height_eq_zero_iff p ((T.ambient.closedStar p).subset_space htstar hx)
      (T.disk_space_subset_region hxD)).mpr hxD
  obtain ⟨u, hu, v, hv, htu, htv, huc, hvc, huQ, hvQ, hun, hvp⟩ :=
    T.exists_edge_chart_sign_witnesses p hps hs hscard (T.marked_le 2 ht) htcard hst
      ell.toAffineMap hell hzero
  have hregion {w : Finset (T.index → ℝ × V3)}
      (hw : w ∈ T.ambient.faces) (htw : t ⊆ w) :
      w.centroid ℝ id ∈ (T.marked 0).space :=
    (T.marked 0).convexHull_subset_space
      (T.triangle_coface_mem_region ht htcard hw htw)
      (w.centroid_mem_convexHull (T.ambient.nonempty_of_mem_faces hw))
  exact ⟨u, hu, v, hv, htu, htv, huc, hvc,
    Or.inl ⟨huQ, hregion hu htu⟩, Or.inl ⟨hvQ, hregion hv htv⟩, hun, hvp⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
