import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.LocalModels









set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance



theorem exists_initial_source_models
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    [T2Space (Quotient O.setoid)]
    (i₀ : ι) {C₀ : Set (Piece U i₀)} (hC₀ : IsCompact C₀)
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    (hopen : ∀ k, Topology.IsOpenEmbedding (e k i₀))
    (hsmooth : letI := (hU i₀).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i₀)) :
    letI := quotientChartedSpace U hU O
    ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
      O.include i₀ '' C₀ ⊆ V ∧
      ∃ F : ∀ k, Quotient O.setoid → M k,
        HasLocalSourceModels U hU O e F V ∧
        ∀ k, Topology.IsOpenEmbedding (fun x : V => F k x) ∧
          IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V ∧
          ∀ y : Piece U i₀, y ∈ C₀ → F k (O.include i₀ y) = e k i₀ y := by
  classical
  let : LocallyCompactSpace (Piece U i₀) := (hU i₀).locallyCompactSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i₀) :=
    (hU i₀).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := quotientChartedSpace U hU O
  let q := O.include i₀
  have hq := O.include_isOpenEmbedding i₀
  obtain ⟨C, hC, hC₀C⟩ := exists_compact_superset hC₀
  let V := q '' interior C
  have hV : IsOpen V := hq.isOpenMap _ isOpen_interior
  have hVc : IsCompact (closure V) :=
    (hC.image hq.continuous).of_isClosed_subset isClosed_closure
      (closure_minimal (image_mono interior_subset) (hC.image hq.continuous).isClosed)
  let F : ∀ k, Quotient O.setoid → M k :=
    fun k z => e k i₀ (Function.invFun q z)
  have hFq (k : ℕ) (x : Piece U i₀) : F k (q x) = e k i₀ x := by
    exact congrArg (e k i₀)
      (Function.leftInverse_invFun (show Function.Injective q from hq.injective) x)
  refine ⟨V, hV, hVc, image_mono hC₀C, F, ?_, ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨i₀, interior C, isOpen_interior, ⟨x, hx, rfl⟩,
      subset_rfl, (fun _ => id), Eventually.of_forall (fun _ => contDiff_id), ?_, ?_⟩
    · intro m K _
      exact Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
        Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε
    · exact Eventually.of_forall fun k y _ => by
        simpa only [id_eq, chartParametrization_apply] using hFq k y
  · intro k
    refine ⟨?_, ?_, fun y _ => hFq k y⟩
    · let H := hq.isEmbedding.toHomeomorph
      have hVr : V ⊆ range q := image_subset_range _ _
      let incl : V → range q := inclusion hVr
      have hincl : Topology.IsOpenEmbedding incl :=
        .inclusion hVr (hV.preimage continuous_subtype_val)
      have hH (z : range q) : q (H.symm z) = z :=
        congrArg Subtype.val (H.apply_symm_apply z)
      have hF : (fun z : V => F k z) = e k i₀ ∘ (H.symm ∘ incl) := by
        funext z
        change F k z = e k i₀ (H.symm (incl z))
        rw [← hFq k (H.symm (incl z))]
        exact congrArg (F k) (hH (incl z)).symm
      rw [hF]
      exact (hopen k).comp (H.symm.isOpenEmbedding.comp hincl)
    · rintro ⟨z, hz⟩
      obtain ⟨x, _, rfl⟩ := hz
      apply (include_isLocalDiffeomorph U hU O hO i₀ x).of_comp
      exact (hsmooth k x).congr_of_eventuallyEq (Eventually.of_forall (hFq k))

end PoincareConjecture.ChartDistance
