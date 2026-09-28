import PoincareConjecture.Definitions.Ch09.NeckCapTopology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_sphere_embedding_local_retraction
    {f : UnitTwoSphere → M}
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (q : UnitTwoSphere) {U : Set M} (hU : IsOpen U) (hqU : f q ∈ U) :
    ∃ (V : Set M) (r : M → UnitTwoSphere),
      IsOpen V ∧ f q ∈ V ∧ V ⊆ U ∧
      ContMDiffOn (𝓡 3) (𝓡 2) ∞ r V ∧
      ∀ z : UnitTwoSphere, f z ∈ V → r (f z) = z := by
  let h : Manifold.IsImmersionAt (𝓡 2) (𝓡 3) ∞ f q :=
    hf.isImmersion.isImmersionAt q
  let P : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) h.complement).comp
      h.equiv.symm.toContinuousLinearMap
  let p : M → EuclideanSpace ℝ (Fin 2) :=
    fun y => P ((h.codChart.extend (𝓡 3)) y)
  let r : M → UnitTwoSphere := fun y => (h.domChart.extend (𝓡 2)).symm (p y)
  have hp : ContMDiffOn (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ p
      h.codChart.source :=
    P.contMDiff.comp_contMDiffOn
      (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas)
  have hpf (z : UnitTwoSphere) (hz : z ∈ h.domChart.source) :
      p (f z) = (h.domChart.extend (𝓡 2)) z := by
    have hzt : (h.domChart.extend (𝓡 2)) z ∈ (h.domChart.extend (𝓡 2)).target :=
      (h.domChart.extend (𝓡 2)).map_source (by simpa using hz)
    have heq := h.writtenInCharts hzt
    change (h.codChart.extend (𝓡 3))
        (f ((h.domChart.extend (𝓡 2)).symm ((h.domChart.extend (𝓡 2)) z))) =
      h.equiv ((h.domChart.extend (𝓡 2)) z, 0) at heq
    rw [h.domChart.extend_left_inv hz] at heq
    change P ((h.codChart.extend (𝓡 3)) (f z)) = _
    rw [heq]
    simp [P]
  obtain ⟨O, hO, hOf⟩ :=
    hf.isEmbedding.isInducing.isOpen_iff.mp h.domChart.open_source
  let V : Set M := (U ∩ O) ∩
    (h.codChart.source ∩ p ⁻¹' (h.domChart.extend (𝓡 2)).target)
  have hV : IsOpen V :=
    (hU.inter hO).inter
      (hp.continuousOn.isOpen_inter_preimage h.codChart.open_source
        h.domChart.isOpen_extend_target)
  have hqO : f q ∈ O := by
    have : q ∈ f ⁻¹' O := by rw [hOf]; exact h.mem_domChart_source
    exact this
  have hqV : f q ∈ V := by
    refine ⟨⟨hqU, hqO⟩, h.mem_codChart_source, ?_⟩
    change p (f q) ∈ (h.domChart.extend (𝓡 2)).target
    rw [hpf q h.mem_domChart_source]
    exact (h.domChart.extend (𝓡 2)).map_source (by simpa using h.mem_domChart_source)
  have hrs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) ∞
      (h.domChart.extend (𝓡 2)).symm (h.domChart.extend (𝓡 2)).target := by
    rw [h.domChart.extend_target']
    exact contMDiffOn_extend_symm h.domChart_mem_maximalAtlas
  refine ⟨V, r, hV, hqV, fun _ hy => hy.1.1,
    hrs.comp (hp.mono fun _ hy => hy.2.1) (fun _ hy => hy.2.2), ?_⟩
  intro z hz
  have hzdom : z ∈ h.domChart.source := by
    rw [← hOf]
    exact hz.1.2
  change (h.domChart.extend (𝓡 2)).symm (p (f z)) = z
  rw [hpf z hzdom]
  exact h.domChart.extend_left_inv hzdom

end PoincareConjecture.M28
