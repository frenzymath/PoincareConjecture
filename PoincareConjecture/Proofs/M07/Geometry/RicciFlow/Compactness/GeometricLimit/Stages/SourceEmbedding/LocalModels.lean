import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.DistanceControl

set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i))
    {M : ℕ → Type*} (e : ∀ k i, Piece U i → M k)

def HasLocalSourceModels (F : ∀ k, Quotient O.setoid → M k)
    (V : Set (Quotient O.setoid)) : Prop :=
  ∀ q ∈ V, ∃ i, ∃ B : Set (Piece U i), IsOpen B ∧ q ∈ O.include i '' B ∧
    O.include i '' B ⊆ V ∧
    ∃ a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ᶠ k in atTop, ContDiff ℝ ∞ (a k)) ∧
      (∀ m K, IsCompact K → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop K) ∧
      ∀ᶠ k in atTop, ∀ y ∈ B,
        F k (O.include i y) = chartParametrization U hU (e k i) (a k y)

variable {U hU O e}

theorem HasLocalSourceModels.restrict
    {F : ∀ k, Quotient O.setoid → M k} {V W : Set (Quotient O.setoid)}
    (h : HasLocalSourceModels U hU O e F V) (hW : IsOpen W) (hWV : W ⊆ V) :
    HasLocalSourceModels U hU O e F W := by
  intro q hq
  obtain ⟨i, B, hB, ⟨x, hx, rfl⟩, _, a, ha, haj, hf⟩ := h q (hWV hq)
  refine ⟨i, B ∩ O.include i ⁻¹' W,
    hB.inter (hW.preimage (O.include_isOpenEmbedding i).continuous),
    ⟨x, ⟨hx, hq⟩, rfl⟩, ?_, a, ha, haj, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  · exact hf.mono fun k hk y hy => hk y hy.1

theorem HasLocalSourceModels.extend
    {F G : ∀ k, Quotient O.setoid → M k} {V A : Set (Quotient O.setoid)}
    (h : HasLocalSourceModels U hU O e F V) (hA : IsOpen A) (hAV : A ⊆ V)
    {j : ι} {C : Set (Piece U j)} (hC : IsOpen C)
    {a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (ha : ∀ᶠ k in atTop, ContDiff ℝ ∞ (a k))
    (haj : ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop K)
    (hleft : ∀ᶠ k in atTop, EqOn (G k) (F k) A)
    (hright : ∀ᶠ k in atTop, ∀ y ∈ C,
      G k (O.include j y) = chartParametrization U hU (e k j) (a k y)) :
    HasLocalSourceModels U hU O e G (A ∪ O.include j '' C) := by
  intro q hq
  rcases hq with hq | hq
  · obtain ⟨i, B, hB, hqB, hBA, b, hb, hbj, hf⟩ := h.restrict hA hAV q hq
    refine ⟨i, B, hB, hqB, hBA.trans subset_union_left, b, hb, hbj, ?_⟩
    filter_upwards [hleft, hf] with k hk hfk y hy
    exact (hk (hBA (mem_image_of_mem _ hy))).trans (hfk y hy)
  · exact ⟨j, C, hC, hq, subset_union_right, a, ha, haj, hright⟩

theorem HasLocalSourceModels.chart_approximation
    [∀ k, MetricSpace (M k)]
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (hrel : ∀ i j (x : Piece U i) (y : Piece U j),
      O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)}
    (h : HasLocalSourceModels U hU O e F V) (hV : IsOpen V)
    (i : ι) {K : Set (Piece U i)} (hK : IsCompact K) (hKV : O.include i '' K ⊆ V) :
    TendstoUniformlyOn (fun k x => dist (F k (O.include i x)) (e k i x))
      (fun _ => 0) atTop K := by
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  apply tendstoUniformlyOn_chart_approximation_of_local_charts hD O hrel hV ?_ i hK hKV
  intro q hq
  obtain ⟨j, B, hB, hqB, _, a, _, haj, hf⟩ := h q hq
  refine ⟨j, B, hB, hqB, ?_⟩
  intro C hC hCB
  have hzero : TendstoUniformlyOn a id atTop (Subtype.val '' C) := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
          (haj 0 _ (hC.image continuous_subtype_val))
  apply (tendstoUniformlyOn_chartParametrization_displacement U hU L he hC hzero).congr
  exact hf.mono fun k hk y hy => congrArg (fun z => dist z (e k j y)) (hk y (hCB hy)).symm

end PoincareConjecture.ChartDistance
