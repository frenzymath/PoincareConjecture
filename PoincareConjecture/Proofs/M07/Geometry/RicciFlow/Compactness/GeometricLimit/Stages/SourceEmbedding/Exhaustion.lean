import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Finite
import PoincareConjecture.Proofs.M07.Topology.Sequences.UniformDiagonal










set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem exists_pointed_source_embeddings_on_compact_sequence
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    {i₀ : ℕ} (p : Piece U i₀) :
    letI : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
    let O := overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))) L he c hc hlower hopen hconn
    letI := quotientChartedSpace U hU O
    ∀ A : ℕ → Set (Quotient O.setoid), (∀ j, IsCompact (A j)) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ V : ℕ → Set (Quotient O.setoid),
        (∀ j, IsOpen (V j) ∧ IsCompact (closure (V j)) ∧ A j ∪ {O.include i₀ p} ⊆ V j) ∧
      ∃ F : ∀ j, Quotient O.setoid → M (σ j),
        (∀ j, Topology.IsOpenEmbedding (fun x : V j => F j x) ∧
          IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F j) (V j) ∧
          F j (O.include i₀ p) = e (σ j) i₀ p) ∧
        (∀ i C, IsCompact C → TendstoUniformlyOn
          (fun j x => dist (F j (O.include i x)) (e (σ j) i x)) (fun _ => 0) atTop C) ∧
        ∀ i m B, IsCompact B → B ⊆ U i →
          TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m
            (coordinateRepresentative U hU
              (fun x => Function.invFun (e (σ j) i) (F j (O.include i x)))))
            (iteratedFDeriv ℝ m id) atTop B := by
  classical
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  dsimp only
  intro A hA
  let C : ∀ i, CompactExhaustion (Piece U i) := fun i => CompactExhaustion.choice (Piece U i)
  let H : ℕ → Set (Quotient O.setoid) := fun j =>
    A j ∪ ⋃ i ∈ Finset.range (j + 1), O.include i '' C i j
  have hH (j : ℕ) : IsCompact (H j) :=
    (hA j).union ((Finset.range (j + 1)).isCompact_biUnion fun i _ =>
      ((C i).isCompact j).image (O.include_isOpenEmbedding i).continuous)
  choose V hV hVc hHV F hF happrox hjet using fun j =>
    exists_pointed_source_embeddings_near_compact U hU hD L he c hc hlower hopen hconn
      hsmooth hbound p (H j) (hH j)
  have hCV (j i : ℕ) (hij : i ≤ j) : O.include i '' C i j ⊆ V j := by
    intro q hq
    apply hHV j
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hij), hq⟩⟩))
  let P : ℕ → ℕ → Prop := fun j k =>
    (Topology.IsOpenEmbedding (fun x : V j => F j k x) ∧
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F j k) (V j) ∧
      F j k (O.include i₀ p) = e k i₀ p) ∧
    ∀ i ≤ j, ∀ x ∈ C i j, dist (F j k (O.include i x)) (e k i x) < 1 / ((j : ℝ) + 1)
  have hP (j : ℕ) : ∀ᶠ k in atTop, P j k := by
    have hsmall := (Finset.range (j + 1)).eventually_all.mpr fun i hi =>
      Metric.tendstoUniformlyOn_iff.mp
        (happrox j i (C i j) ((C i).isCompact j)
          (hCV j i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
        (1 / ((j : ℝ) + 1)) (by positivity)
    filter_upwards [hF j, hsmall] with k hk hs
    refine ⟨hk, ?_⟩
    intro i hij x hx
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] using
      hs i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hij)) x hx
  let f := fun (t j k : ℕ) => iteratedFDeriv ℝ t.unpair.2
    (coordinateRepresentative U hU
      (fun x => Function.invFun (e k t.unpair.1) (F j k (O.include t.unpair.1 x))))
  let g := fun t : ℕ => iteratedFDeriv ℝ t.unpair.2 (id : EuclideanSpace ℝ (Fin n) → _)
  let B := fun (t j : ℕ) => Subtype.val '' C t.unpair.1 j
  have hB (t : ℕ) : Monotone (B t) := fun j l hjl => image_mono ((C t.unpair.1).subset hjl)
  have hconv (j t : ℕ) (htj : t ≤ j) : TendstoUniformlyOn (f t j) (g t) atTop (B t j) := by
    apply hjet j t.unpair.1 t.unpair.2 (B t j)
      (((C t.unpair.1).isCompact j).image continuous_subtype_val)
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem Subtype.val
      (hCV j t.unpair.1 ((Nat.unpair_left_le t).trans htj) (mem_image_of_mem _ hx))
  obtain ⟨σ, hσ, hσP, hσconv⟩ :=
    Poincare.exists_strictMono_tendstoUniformlyOn_diagonal f g B hB hconv hP
  refine ⟨σ, hσ, V, ?_, (fun j => F j (σ j)), (fun j => (hσP j).1), ?_, ?_⟩
  · intro j
    exact ⟨hV j, hVc j, (union_subset_union_left _ subset_union_left).trans (hHV j)⟩
  · intro i K hK
    obtain ⟨l, hKl⟩ := (C i).exists_superset_of_isCompact hK
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hsmall : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
    filter_upwards [eventually_ge_atTop i, eventually_ge_atTop l, hsmall] with j hij hlj hj x hx
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] using
      ((hσP j).2 i hij x ((C i).subset hlj (hKl hx))).trans hj
  · intro i m K hK hKU
    have hKr : K ⊆ range (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) := by
      rintro x hx
      exact ⟨⟨x, hKU hx⟩, rfl⟩
    have hKi := (hU i).isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK hKr
    obtain ⟨l, hKl⟩ := (C i).exists_superset_of_isCompact hKi
    have hsub : K ⊆ Subtype.val '' C i l := by
      intro x hx
      exact ⟨⟨x, hKU hx⟩, hKl hx, rfl⟩
    have h := hσconv (Nat.pair i m) l
    dsimp only [f, g, B] at h
    rw [Nat.unpair_pair] at h
    exact h.mono hsub

end PoincareConjecture.ChartDistance
