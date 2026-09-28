import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  {K : Set M}
  [ChartedSpace (EuclideanHalfSpace (m + 1)) K]

private theorem exists_inclusion_charts
    (h : _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (Subtype.val : K → M)) (x : K) :
    ∃ (φ : OpenPartialHomeomorph K (EuclideanHalfSpace (m + 1)))
      (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))))
      (A : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (m + 1))),
      x ∈ φ.source ∧ (x : M) ∈ ψ.source ∧
      φ ∈ IsManifold.maximalAtlas (𝓡∂ (m + 1)) ∞ K ∧
      φ.source ⊆ Subtype.val ⁻¹' ψ.source ∧
      EqOn (ψ ∘ Subtype.val) (A ∘ (𝓡∂ (m + 1)) ∘ φ) φ.source := by
  have hi := h.isImmersion.isImmersionAt x
  let L : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (m + 1)) :=
    hi.equiv.toLinearMap.comp (LinearMap.inl ℝ _ _)
  have hL : Function.Injective L := by
    intro u v huv
    exact congrArg Prod.fst (hi.equiv.injective huv)
  let A := (LinearEquiv.ofBijective L
    ⟨hL, LinearMap.injective_iff_surjective.mp hL⟩).toContinuousLinearEquiv
  refine ⟨hi.domChart, hi.codChart, A, hi.mem_domChart_source,
    hi.mem_codChart_source, hi.domChart_mem_maximalAtlas,
    hi.source_subset_preimage_source, ?_⟩
  intro y hy
  have hz := hi.writtenInCharts
    ((hi.domChart.extend (𝓡∂ (m + 1))).map_source (by
      simpa only [OpenPartialHomeomorph.extend_source] using hy))
  dsimp only [Function.comp_apply] at hz
  rw [hi.domChart.extend_left_inv hy] at hz
  exact hz

theorem image_interior_of_isSmoothEmbedding
    (h : _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (Subtype.val : K → M)) :
    Subtype.val '' (𝓡∂ (m + 1)).interior K = interior K := by
  have hpoint (x : K) :
      (𝓡∂ (m + 1)).IsInteriorPoint x ↔ (x : M) ∈ interior K := by
    obtain ⟨φ, ψ, A, hxφ, hxψ, hφ, hsource, hcoord⟩ := exists_inclusion_charts h x
    have hxcoord : ψ x = A ((φ.extend (𝓡∂ (m + 1))) x) := hcoord hxφ
    have himage : A '' (φ.extend (𝓡∂ (m + 1))).target =
        ψ '' (Subtype.val '' φ.source) := by
      rw [φ.extend_target_eq_image_source]
      simp only [image_image]
      apply image_congr
      intro y hy
      exact (hcoord hy).symm
    rw [ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) hφ hxφ,
      mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds]
    constructor
    · intro ht
      have ha := A.toHomeomorph.isOpenMap.image_mem_nhds ht
      simp only [ContinuousLinearEquiv.coe_toHomeomorph] at ha
      rw [himage, ← hxcoord] at ha
      have hb := ψ.symm.image_mem_nhds (ψ.map_source hxψ) ha
      rw [ψ.left_inv hxψ] at hb
      apply mem_of_superset hb
      rintro y ⟨z, ⟨w, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
      rw [ψ.left_inv (hsource hv)]
      exact v.property
    · intro hxK
      have hs : Subtype.val '' φ.source ∈ 𝓝 (x : M) := by
        have hs := image_mem_map (m := (Subtype.val : K → M))
          (φ.open_source.mem_nhds hxφ)
        rw [h.isEmbedding.map_nhds_of_mem x (by simpa only [Subtype.range_coe] using hxK)]
          at hs
        exact hs
      have ha := A.symm.toHomeomorph.isOpenMap.image_mem_nhds (ψ.image_mem_nhds hxψ hs)
      simp only [ContinuousLinearEquiv.coe_toHomeomorph] at ha
      rw [hxcoord, A.symm_apply_apply] at ha
      simpa only [← himage, image_image, Function.comp_def, A.symm_apply_apply,
        image_id'] using ha
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hpoint y).mp hy
  · intro hx
    exact ⟨⟨x, interior_subset hx⟩, (hpoint ⟨x, interior_subset hx⟩).mpr hx, rfl⟩

end Poincare.Manifold
