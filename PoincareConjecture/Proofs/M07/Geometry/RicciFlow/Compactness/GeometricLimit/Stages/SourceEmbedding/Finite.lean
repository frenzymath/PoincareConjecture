import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.LocalReadout
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Extension
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Initial










set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth in


theorem exists_local_source_models_near_compact
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i₀ : ι) {C₀ : Set (Piece U i₀)} (hC₀ : IsCompact C₀) :
    letI : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
    let O := overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))) L he c hc hlower hopen hconn
    letI := quotientChartedSpace U hU O
    ∀ K : Set (Quotient O.setoid), IsCompact K →
      ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
        K ∪ O.include i₀ '' C₀ ⊆ V ∧
      ∃ F : ∀ k, Quotient O.setoid → M k,
        HasLocalSourceModels U hU O e F V ∧
        ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => F k x) ∧
          IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V ∧
          ∀ y ∈ C₀, F k (O.include i₀ y) = e k i₀ y := by
  classical
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let hrel := fun l q x y => (zero_iff_transition hp c hc hlower (i := l) (j := q)
    (x := x) (y := y)).symm
  let := quotientMetricSpace hp O hrel L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  let : LocallyCompactSpace (Quotient O.setoid) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) (Quotient O.setoid)
  let (k : ℕ) : Nonempty (M k) := ⟨e k i₀ Classical.ofNonempty⟩
  let : ∀ l, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U l) :=
    fun l => (hU l).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hO := overlapSystem_smooth U hU hp L he c hc hlower hopen hconn hsmooth hbound
  have hanchor : IsCompact (O.include i₀ '' C₀) :=
    hC₀.image (O.include_isOpenEmbedding i₀).continuous
  obtain ⟨V₀, hV₀, hV₀c, hC₀V, F₀, hmodels₀, hF₀⟩ :=
    exists_initial_source_models U hU O hO i₀ hC₀ (fun k => hopen k i₀) (fun k => hsmooth k i₀)
  have hfinite : ∀ (s : Finset (Σ i, Piece U i)) (C : ∀ a : Σ i, Piece U i, Set (Piece U a.1)),
      (∀ a ∈ s, IsCompact (C a)) →
      ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
        (O.include i₀ '' C₀ ∪ ⋃ a ∈ s, O.include a.1 '' C a) ⊆ V ∧
        ∃ F : ∀ k, Quotient O.setoid → M k,
          HasLocalSourceModels U hU O e F V ∧
          ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => F k x) ∧
            IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V ∧
            ∀ y ∈ C₀, F k (O.include i₀ y) = e k i₀ y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro C _
      exact ⟨V₀, hV₀, hV₀c, by simpa using hC₀V, F₀, hmodels₀, Eventually.of_forall hF₀⟩
    | @insert a s ha ih =>
      intro C hC
      have hCs : ∀ b ∈ s, IsCompact (C b) := fun b hb => hC b (Finset.mem_insert_of_mem hb)
      obtain ⟨V, hV, _, hKV, F, hmodels, hF⟩ := ih C hCs
      have hK : IsCompact (O.include i₀ '' C₀ ∪ ⋃ b ∈ s, O.include b.1 '' C b) :=
        hanchor.union (s.isCompact_biUnion fun b hb =>
          (hCs b hb).image (O.include_isOpenEmbedding b.1).continuous)
      obtain ⟨A', hA', hKA', hA'V⟩ := exists_compact_between hK hV hKV
      obtain ⟨A, hA, hKA, hAA'⟩ := exists_compact_between hK isOpen_interior hKA'
      obtain ⟨B, hB, hCB⟩ := exists_compact_superset (hC a (Finset.mem_insert_self _ _))
      have hdist := tendstoUniformlyOn_source_chart_distance_of_approximation hD O hrel
        (fun i K hK hKV => HasLocalSourceModels.chart_approximation (O := O)
          hD hrel L he hmodels hV i hK hKV)
        hA' hA'.isClosed hA'V hB
      have hread := local_source_models_readout_smooth_convergence U hU hD L he c hc hlower
        hopen hconn hsmooth hbound hV hmodels a.1
      obtain ⟨b, hbjet, hbmaps⟩ := exists_source_embedding_extension (hU a.1)
        (O.include_isOpenEmbedding a.1) (fun k => hopen k a.1) (fun k => he k a.1)
        (hc a.1) (fun k => hlower k a.1) hconn hV hA hA' hAA' hA'V hB
        (hF.mono fun _ hk => hk.1) hdist
        (fun x hx => by
          obtain ⟨W, hW, hxW, _, hs⟩ := hread.1 x hx
          exact ⟨W, hW, hxW, hs⟩) hread.2
      obtain ⟨G, hG⟩ := Filter.skolem.mp (hbmaps.mono fun _ hk => hk.2.2.2)
      let W := interior A ∪ O.include a.1 '' interior B
      have hW : IsOpen W := isOpen_interior.union (O.include_isOpenMap a.1 _ isOpen_interior)
      have hAV : interior A ⊆ V := interior_subset.trans (hAA'.trans (interior_subset.trans hA'V))
      have hWcompact : IsCompact (closure W) :=
        (hA.union (hB.image (O.include_isOpenEmbedding a.1).continuous)).of_isClosed_subset
          isClosed_closure (closure_minimal
            (union_subset_union interior_subset (image_mono interior_subset))
            (hA.isClosed.union (hB.image (O.include_isOpenEmbedding a.1).continuous).isClosed))
      refine ⟨W, hW, hWcompact, ?_, G, ?_, ?_⟩
      · intro q hq
        rcases hq with hq | hq
        · exact Or.inl (hKA (Or.inl hq))
        · simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left] at hq
          rcases hq with hq | hq
          · exact Or.inr ((image_mono hCB) hq)
          · exact Or.inl (hKA (Or.inr hq))
      · exact hmodels.extend isOpen_interior hAV isOpen_interior
          (hbmaps.mono fun _ hk => hk.1) hbjet
          (hG.mono fun _ hk => hk.2.1) (hG.mono fun _ hk => hk.2.2)
      · filter_upwards [hG, hbmaps, hF] with k hk hbk hFk
        exact ⟨hk.1, isLocalDiffeomorphOn_source_extension (hU a.1)
          (include_isLocalDiffeomorph U hU O hO a.1) (hsmooth k a.1)
          isOpen_interior isOpen_interior hAV hFk.2.1 (b k) hbk.1 hbk.2.1 hbk.2.2.1
          hk.2.1 hk.2.2, fun y hy =>
            (hk.2.1 (hKA (Or.inl (mem_image_of_mem _ hy)))).trans (hFk.2.2 y hy)⟩
  dsimp only
  intro K hK
  obtain ⟨s, C, hC, hcover⟩ := exists_finite_compact_representatives O hK hK.isClosed
  obtain ⟨V, hV, hVc, hKV, F, hmodels, hF⟩ := hfinite s C hC
  refine ⟨V, hV, hVc, ?_, F, hmodels, hF⟩
  rw [hcover, union_comm] at hKV
  exact hKV

include hD he hc hlower hopen hconn hsmooth in



theorem exists_pointed_source_embeddings_near_compact
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    {i₀ : ι} (p : Piece U i₀) :
    letI : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
    let O := overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))) L he c hc hlower hopen hconn
    letI := quotientChartedSpace U hU O
    ∀ K : Set (Quotient O.setoid), IsCompact K →
      ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
        K ∪ {O.include i₀ p} ⊆ V ∧
      ∃ F : ∀ k, Quotient O.setoid → M k,
        (∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => F k x) ∧
          IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V ∧ F k (O.include i₀ p) = e k i₀ p) ∧
        (∀ i C, IsCompact C → O.include i '' C ⊆ V → TendstoUniformlyOn
          (fun k x => dist (F k (O.include i x)) (e k i x)) (fun _ => 0) atTop C) ∧
        ∀ i m B, IsCompact B → B ⊆ Subtype.val '' (O.include i ⁻¹' V) →
          TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
            (coordinateRepresentative U hU (fun x => Function.invFun (e k i) (F k (O.include i x)))))
            (iteratedFDeriv ℝ m id) atTop B := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  dsimp only
  intro K hK
  obtain ⟨V, hV, hVc, hKV, F, hmodels, hF⟩ :=
    exists_local_source_models_near_compact U hU hD L he c hc hlower hopen hconn hsmooth
      hbound i₀ (C₀ := {p}) isCompact_singleton K hK
  refine ⟨V, hV, hVc, by simpa only [image_singleton] using hKV, F, ?_, ?_, ?_⟩
  · exact hF.mono fun k hk => ⟨hk.1, hk.2.1, hk.2.2 p (mem_singleton p)⟩
  · intro i C hC hCV
    exact HasLocalSourceModels.chart_approximation (O := O) hD
      (fun i j x y => (zero_iff_transition hp c hc hlower).symm) L he hmodels hV i hC hCV
  · intro i
    exact (local_source_models_readout_smooth_convergence U hU hD L he c hc hlower
      hopen hconn hsmooth hbound hV hmodels i).2

end PoincareConjecture.ChartDistance
