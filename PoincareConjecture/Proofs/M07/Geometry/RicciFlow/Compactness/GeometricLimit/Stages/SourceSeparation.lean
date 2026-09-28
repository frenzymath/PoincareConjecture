import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.ChartCorrection
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.UniformDistance











set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem eventually_zero_mem_open_of_uniform_limit
    {X : Type*} [TopologicalSpace X] {f : ℕ → X → ℝ} {F : X → ℝ}
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V)
    (hF : ContinuousOn F K) (hf : TendstoUniformlyOn f F atTop K)
    (hzero : ∀ x ∈ K, F x = 0 → x ∈ V) :
    ∀ᶠ k in atTop, ∀ x ∈ K, f k x = 0 → x ∈ V := by
  by_cases hne : (K \ V).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (hK.diff hV).exists_isMinOn hne
      (hF.abs.mono sdiff_subset)
    have hpos : 0 < |F x| := abs_pos.mpr (fun hz => hx.2 (hzero x hx.1 hz))
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf _ hpos] with k hk y hy hfy
    by_contra hyv
    have hsmall := hk y hy
    rw [hfy, Real.dist_eq, sub_zero] at hsmall
    exact (not_lt_of_ge (hmin ⟨hy, hyv⟩)) hsmall
  · exact Eventually.of_forall fun _ x hx _ =>
      by_contra fun hxV => hne ⟨x, hx, hxV⟩

theorem tendstoUniformlyOn_corrected_chart_dist
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k, X → M k} {f : ∀ k, Y → M k}
    {D : X × Y → ℝ} {L : ℝ≥0} (hf : ∀ k, LipschitzWith L (f k))
    {K : Set X} {C : Set Y}
    (hD : TendstoUniformlyOn (fun k p => dist (e k p.1) (f k p.2)) D atTop (K ×ˢ C))
    {a : ℕ → Y → Y} (ha : TendstoUniformlyOn a id atTop C) :
    TendstoUniformlyOn (fun k p => dist (e k p.1) (f k (a k p.2))) D atTop (K ×ˢ C) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hden : 0 < (L : ℝ) + 1 := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hD (ε / 2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp ha (ε / (2 * ((L : ℝ) + 1))) (by positivity)]
    with k hkD hka p hp
  have heps : ((L : ℝ) + 1) * dist (a k p.2) p.2 < ε / 2 := by
    have h := hka p.2 hp.2
    rw [id_eq, dist_comm] at h
    have h' := (lt_div_iff₀ (show 0 < 2 * ((L : ℝ) + 1) by positivity)).mp h
    nlinarith
  have hdist : dist (f k (a k p.2)) (f k p.2) < ε / 2 :=
    ((hf k).dist_le_mul _ _).trans_lt
      ((mul_le_mul_of_nonneg_right (by linarith : (L : ℝ) ≤ L + 1)
        dist_nonneg).trans_lt heps)
  calc
    dist (D p) (dist (e k p.1) (f k (a k p.2))) ≤
        dist (D p) (dist (e k p.1) (f k p.2)) +
          dist (dist (e k p.1) (f k p.2)) (dist (e k p.1) (f k (a k p.2))) :=
      dist_triangle _ _ _
    _ ≤ dist (D p) (dist (e k p.1) (f k p.2)) +
          dist (f k (a k p.2)) (f k p.2) := by
      gcongr
      simpa only [dist_self, zero_add, dist_comm] using
        dist_dist_dist_le (e k p.1) (f k p.2) (e k p.1) (f k (a k p.2))
    _ < ε := by linarith [hkD p hp]



theorem eventually_corrected_source_eq_iff
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k, X → M k} {f : ∀ k, Y → M k}
    (he : ∀ k, Function.Injective (e k))
    {D : C(X × Y, ℝ)} (τ : OpenPartialHomeomorph X Y)
    (hτ : ∀ x y, D (x, y) = 0 ↔ x ∈ τ.source ∧ τ x = y)
    {A K : Set X} {C : Set Y} (hA : IsCompact A) (hC : IsCompact C)
    (hAK : A ⊆ interior K) {a : ℕ → Y → Y}
    (hD : TendstoUniformlyOn (fun k p => dist (e k p.1) (f k (a k p.2))) D atTop (A ×ˢ C))
    (hagree : ∀ᶠ k in atTop, ∀ x ∈ K, ∀ y ∈ C, D (x, y) = 0 → f k (a k y) = e k x) :
    ∀ᶠ k in atTop, ∀ x ∈ A, ∀ y ∈ C, e k x = f k (a k y) ↔ D (x, y) = 0 := by
  let V : Set Y := τ.target ∩ τ.symm ⁻¹' interior K
  have hV : IsOpen V := τ.symm.continuousOn.isOpen_inter_preimage
    τ.open_target isOpen_interior
  have hzero : ∀ p ∈ A ×ˢ C, D p = 0 → p ∈ (univ : Set X) ×ˢ V := by
    rintro ⟨x, y⟩ hp hz
    obtain ⟨hx, rfl⟩ := (hτ x y).mp hz
    exact ⟨mem_univ _, τ.map_source hx, by simpa only [mem_preimage, τ.left_inv hx] using hAK hp.1⟩
  have hcollision := eventually_zero_mem_open_of_uniform_limit (hA.prod hC)
    (isOpen_univ.prod hV) D.continuous.continuousOn hD hzero
  filter_upwards [hcollision, hagree] with k hk hc x hx y hy
  constructor
  · intro hxy
    have hyV := (hk (x, y) ⟨hx, hy⟩ (by simp only [hxy, dist_self])).2
    have hz : D (τ.symm y, y) = 0 :=
      (hτ _ _).mpr ⟨τ.map_target hyV.1, τ.right_inv hyV.1⟩
    have heq := hc (τ.symm y) (interior_subset hyV.2) y hy hz
    have hxinv : x = τ.symm y := he k (hxy.trans heq)
    exact hxinv ▸ hz
  · intro hz
    exact (hc x (interior_subset (hAK hx)) y hy hz).symm

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



theorem exists_source_chart_corrections_with_exact_identifications
    (hbound : ∀ i j, Poincare.Analysis.Calculus.LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {A : Set (Piece U i)} {C : Set (Piece U j)}
    (hA : IsCompact A) (hC : IsCompact C) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      S ⊆ Subtype.val '' overlap (fun i j => D i j) j i ∧
      ∃ a : ℕ → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
        (∀ᶠ k in atTop, ContDiff ℝ ∞ (a k) ∧ ContDiff ℝ ∞ (a k).symm ∧
          (∀ y, y ∉ S → a k y = y) ∧ (a k) '' U j = U j ∧
          ∀ x ∈ A, ∀ y ∈ C,
            e k i x = chartParametrization U hU (e k j) (a k y) ↔ D i j (x, y) = 0) ∧
        ∀ m B, IsCompact B →
          TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
            (iteratedFDeriv ℝ m id) atTop B := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  have hpoint := fun l q x y =>
    (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  obtain ⟨K, hK, hAK⟩ := exists_compact_superset hA
  obtain ⟨S, hS, hSoverlap, a, ha, hjet⟩ :=
    exists_smooth_source_chart_corrections_for_compact_pieces U hU hpoint L he c hc hlower
      hopen hconn hsmooth hbound i j hK hC
  let b : ℕ → Piece U j → Piece U j := fun k y =>
    (hU j).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm (a k y)
  have hbval : ∀ᶠ k in atTop, ∀ y : Piece U j,
      (b k y : EuclideanSpace ℝ (Fin n)) = a k y := by
    filter_upwards [ha] with k hk y
    have hay : a k y ∈ U j := hk.2.2.2.1 ▸ mem_image_of_mem (a k) y.property
    exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (f := (Subtype.val : Piece U j → EuclideanSpace ℝ (Fin n)))
      (h := (hU j).isOpenEmbedding_subtypeVal) ⟨⟨a k y, hay⟩, rfl⟩
  have hb : TendstoUniformlyOn b id atTop C := by
    have hzero : TendstoUniformlyOn (fun k => (a k : _ → _)) id atTop (Subtype.val '' C) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
          (hjet 0 _ (hC.image continuous_subtype_val))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hbval, Metric.tendstoUniformlyOn_iff.mp hzero ε hε]
      with k hk hsmall y hy
    change dist (y : EuclideanSpace ℝ (Fin n)) (b k y : EuclideanSpace ℝ (Fin n)) < ε
    rw [hk y]
    exact hsmall y (mem_image_of_mem Subtype.val hy)
  have hdist := tendstoUniformlyOn_corrected_chart_dist (fun k => he k j)
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (hA.prod hC)).mp
      ((hD i j).tendstoLocallyUniformlyOn.mono (subset_univ _))) hb
  have hagree : ∀ᶠ k in atTop, ∀ x ∈ K, ∀ y ∈ C,
      D i j (x, y) = 0 → e k j (b k y) = e k i x := by
    filter_upwards [ha] with k hk
    exact hk.2.2.2.2
  have hident := eventually_corrected_source_eq_iff (fun k => (hopen k i).injective)
    (overlapHomeomorph hpoint L he c hc hlower hopen hconn i j)
    (fun _ _ => zero_iff_transition hpoint c hc hlower) hA hC hAK hdist hagree
  refine ⟨S, hS, hSoverlap, a, ?_, hjet⟩
  filter_upwards [ha, hident] with k hk hi
  exact ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hi⟩

end PoincareConjecture.ChartDistance
