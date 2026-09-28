import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.ObliqueTopCorners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OriginalCorners









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Classical
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph Plane S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

private theorem vertex_parameter_source (v : Fin (B.interface.count + 1) × Bool) :
    collarParameterEquiv.symm (B.cut v.1, if v.2 then B.interface.height v.1 else 0) ∈
      B.coordinates.source := by
  obtain ⟨i, hi⟩ : ∃ i : Fin B.interface.count, v.1 = i.castSucc ∨ v.1 = i.succ := by
    by_cases h : (v.1 : ℕ) < B.interface.count
    · exact ⟨⟨v.1, h⟩, Or.inl (Fin.ext rfl)⟩
    · refine ⟨B.lastCell, Or.inr (Fin.ext ?_)⟩
      have hn := B.interface.count_pos
      have hv := v.1.isLt
      simp only [lastCell, Fin.val_succ]
      omega
  have ht : B.cut v.1 ∈ Icc (B.cut i.castSucc) (B.cut i.succ) := by
    rcases hi with hi | hi
    · rw [hi]
      exact left_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le
    · rw [hi]
      exact right_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le
  have hh : B.upperGraph i (B.cut v.1) = B.interface.height v.1 := by
    rcases hi with hi | hi
    · rw [hi]
      exact (B.upperGraph_endpoints i).1
    · rw [hi]
      exact (B.upperGraph_endpoints i).2
  apply (B.pair i).band_subset_source
  change (collarParameterEquiv (collarParameterEquiv.symm
      (B.cut v.1, if v.2 then B.interface.height v.1 else 0))).1 ∈
      Icc (B.cut i.castSucc) (B.cut i.succ) ∧ _
  rw [collarParameterEquiv.apply_symm_apply]
  refine ⟨ht, ?_⟩
  have hpos := (B.interface.vertex_height_bounds v.1).1
  change 0 ≤ (if v.2 then B.interface.height v.1 else 0) ∧
    (if v.2 then B.interface.height v.1 else 0) ≤ B.upperGraph i (B.cut v.1)
  rw [hh]
  cases v.2 <;> simp [hpos.le]



theorem coordinates_symm_vertex (v : Fin (B.interface.count + 1) × Bool) :
    collarParameterEquiv (B.coordinates.symm (B.vertex v)) =
      (B.cut v.1, if v.2 then B.interface.height v.1 else 0) := by
  rw [vertex, B.coordinates.left_inv (B.vertex_parameter_source v),
    collarParameterEquiv.apply_symm_apply]




theorem vertex_mem_face_carrier_iff
    (p : Fin B.interface.count × Bool) (v : Fin (B.interface.count + 1) × Bool) :
    B.vertex v ∈ (B.face p).carrier ↔
      ∃ k : Fin 3, B.faceCoordinates p (B.faceBasis p k) = B.vertex v := by
  constructor
  · rcases p with ⟨i, s⟩
    rcases v with ⟨k, t⟩
    intro hv
    have hp := ((B.pair i).parameter_mem hv).1
    rw [B.coordinates_symm_vertex] at hp
    have hleft : i.castSucc ≤ k := B.cut_strictMono.le_iff_le.mp hp.1
    have hright : k ≤ i.succ := B.cut_strictMono.le_iff_le.mp hp.2
    have hk : k = i.castSucc ∨ k = i.succ := by
      apply or_iff_not_imp_left.mpr
      intro hne
      apply Fin.ext
      have hkval : k.val ≠ i.val := fun h => hne (Fin.ext h)
      change i.val ≤ k.val at hleft
      change k.val ≤ i.val + 1 at hright
      simp only [Fin.val_succ]
      omega
    rcases hk with rfl | rfl
    · cases s <;> cases t
      · exact ⟨0, by simp [B.face_corner_eq_vertex, cornerVertexIndex]⟩
      · have hx : (collarParameterEquiv
            (B.coordinates.symm (B.vertex (i.castSucc, true)))).1 = B.cut i.castSucc := by
          rw [B.coordinates_symm_vertex]
        have he := (B.pair i).lower_left_vertex hv hx
        have he' : B.vertex (i.castSucc, true) = B.vertex (i.castSucc, false) := he
        have hfalse := congrArg Prod.snd (B.vertex_injective he')
        exact Bool.noConfusion hfalse
      · exact ⟨0, by simp [B.face_corner_eq_vertex, cornerVertexIndex]⟩
      · exact ⟨1, by simp [B.face_corner_eq_vertex, cornerVertexIndex]⟩
    · cases s <;> cases t
      · exact ⟨1, by simp [B.face_corner_eq_vertex, cornerVertexIndex]⟩
      · exact ⟨2, by simp [B.face_corner_eq_vertex, cornerVertexIndex]⟩
      · have hx : (collarParameterEquiv
            (B.coordinates.symm (B.vertex (i.succ, false)))).1 = B.cut i.succ := by
          rw [B.coordinates_symm_vertex]
        have he := (B.pair i).upper_right_vertex hv hx
        have he' : B.vertex (i.succ, false) = B.vertex (i.succ, true) := by
          simpa [vertex, (B.upperGraph_endpoints i).2] using he
        have hfalse := congrArg Prod.snd (B.vertex_injective he')
        exact Bool.noConfusion hfalse
      · exact ⟨2, by simp [B.face_corner_eq_vertex, cornerVertexIndex]⟩
  · rintro ⟨k, hk⟩
    rw [B.face_carrier_eq_coordinates]
    exact ⟨B.faceBasis p k, subset_convexHull ℝ _ (mem_range_self k), hk⟩



theorem refined_contribution_eq_zero_of_not_mem_carrier
    (g : RiemannianMetric 2 S) (p : Fin B.interface.count × Bool)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) {q : S} (hq : q ∉ (B.face p).carrier) :
    meshVertexAngleContribution g (B.faceCoordinates p)
      ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines) q = 0 := by
  let M := (TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines
  change meshVertexAngleContribution g (B.faceCoordinates p) M q = 0
  unfold meshVertexAngleContribution
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro k _
  have hne : B.faceCoordinates p (meshTriangleBasis M t k) ≠ q := by
    intro heq
    apply hq
    rw [B.face_carrier_eq_coordinates]
    refine ⟨meshTriangleBasis M t k, ?_, heq⟩
    have hm := meshTriangleBasis_subset_support M t
      (subset_convexHull ℝ _ (mem_range_self k))
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hm
  simp only [if_neg hne]



theorem refined_contribution_at_vertex
    (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (p : Fin B.interface.count × Bool) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (v : Fin (B.interface.count + 1) × Bool) :
    meshVertexAngleContribution g (B.faceCoordinates p)
      ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines)
      (B.vertex v) =
      ∑ k : Fin 3, if B.faceCoordinates p (B.faceBasis p k) = B.vertex v
        then coordinateTriangleAngle g (B.faceCoordinates p) (B.faceBasis p) k else 0 := by
  by_cases hv : B.vertex v ∈ (B.face p).carrier
  · obtain ⟨k, hk⟩ := (B.vertex_mem_face_carrier_iff p v).mp hv
    have hpres := single_refineByLines_original_corner g (B.faceCoordinates p)
      (B.faceBasis p) lines (B.smooth_faceCoordinates hF p)
      (B.smooth_faceCoordinates_symm hFi p) (B.face_triangle_subset_source p) k
    rw [hk] at hpres
    rw [hpres]
    have heq (l : Fin 3) : B.faceCoordinates p (B.faceBasis p l) = B.vertex v ↔ l = k := by
      constructor
      · intro hl
        apply (B.faceBasis p).ind.injective
        exact (B.faceCoordinates p).injOn
          (B.face_triangle_subset_source p (subset_convexHull ℝ _ (mem_range_self l)))
          (B.face_triangle_subset_source p (subset_convexHull ℝ _ (mem_range_self k)))
          (hl.trans hk.symm)
      · rintro rfl
        exact hk
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [B.refined_contribution_eq_zero_of_not_mem_carrier g p lines hv]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hne : B.faceCoordinates p (B.faceBasis p k) ≠ B.vertex v :=
      fun hk => hv ((B.vertex_mem_face_carrier_iff p v).mpr ⟨k, hk⟩)
    simp only [if_neg hne]



theorem sum_refined_vertex_contributions
    (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (v : Fin (B.interface.count + 1) × Bool) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.vertex v)) =
      ∑ p : Fin B.interface.count × Bool, ∑ k : Fin 3,
        if B.faceCoordinates p (B.faceBasis p k) = B.vertex v
        then coordinateTriangleAngle g (B.faceCoordinates p) (B.faceBasis p) k else 0 := by
  apply Finset.sum_congr rfl
  intro p _
  exact B.refined_contribution_at_vertex g hF hFi p (lines p) v



theorem internal_bottom_refined_vertex_fan
    (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.vertex (i.succ, false))) = Real.pi := by
  rw [B.sum_refined_vertex_contributions g hF hFi lines]
  exact B.internal_bottom_vertex_fan g hF hFi i j hij



theorem internal_top_refined_vertex_fan
    (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.vertex (i.succ, true))) +
      g.cornerAngle (B.vertex (i.succ, true)) (B.topOutwardRay i) (B.topLeftChord i) +
      g.cornerAngle (B.vertex (i.succ, true)) (B.topOutwardRay i) (B.topRightChord j) =
      2 * Real.pi := by
  rw [B.sum_refined_vertex_contributions g hF hFi lines]
  exact B.internal_top_vertex_fan g hF hFi i j hij

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
