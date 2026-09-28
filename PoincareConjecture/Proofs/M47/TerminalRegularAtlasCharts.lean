import PoincareConjecture.Proofs.M47.TerminalRegularCountableAtlas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Poincare.Gluing IsManifold
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ



theorem terminalSource_regular_atlas_charts
    (U : ℕ → Set E) (hU : ∀ i, IsOpen (U i)) [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∀ (g : RiemannianMetric 3 (Quotient O.setoid)) (B0 : ℕ → E → Bilin),
    (letI : ∀ i, ChartedSpace E (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
     ∀ i (x : Piece U i) v w, B0 i x v w = g.inner (O.include i x)
       (mfderiv (𝓡 3) (𝓡 3) (O.include i) x v)
       (mfderiv (𝓡 3) (𝓡 3) (O.include i) x w)) →
    ∃ c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) (Quotient O.setoid) E ∞,
      (∀ i, ((c i).symm : E → Quotient O.setoid) =
        ChartDistance.chartParametrization U hU (O.include i)) ∧
      (∀ i, (c i).source = range (O.include i)) ∧
      (∀ i, (c i).target = U i) ∧
      (∀ x : Quotient O.setoid, ∃ i, x ∈ (c i).source) ∧
      (∀ i, EqOn (g.pullbackCoefficients (c i).symm) (B0 i) (U i)) ∧
      ∀ i m y, y ∈ U i →
        iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm) y =
          iteratedFDeriv ℝ m (B0 i) y := by
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  intro g B0 hmetric
  let : ∀ i, ChartedSpace E (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hci (i : ℕ) : quotientChart U hU O i ∈ maximalAtlas (𝓡 3) ∞ (Quotient O.setoid) :=
    subset_maximalAtlas ⟨i, rfl⟩
  let c (i : ℕ) : PartialDiffeomorph (𝓡 3) (𝓡 3) (Quotient O.setoid) E ∞ := {
    toPartialEquiv := (quotientChart U hU O i).toPartialEquiv
    open_source := (quotientChart U hU O i).open_source
    open_target := (quotientChart U hU O i).open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (hci i)
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (hci i) }
  have hinverse (i : ℕ) : ((c i).symm : E → Quotient O.setoid) =
      ChartDistance.chartParametrization U hU (O.include i) := rfl
  have hcoeff (i : ℕ) : EqOn (g.pullbackCoefficients (c i).symm) (B0 i) (U i) := by
    intro y hy
    let x : Piece U i := ⟨y, hy⟩
    have hd := ChartDistance.mfderiv_chartParametrization U hU x
      ((include_isLocalDiffeomorph U hU O hO i).contMDiff x)
    rw [hinverse i]
    ext v w
    change g.inner (ChartDistance.chartParametrization U hU (O.include i) x.val)
      (mfderiv (𝓡 3) (𝓡 3) (ChartDistance.chartParametrization U hU (O.include i)) x.val v)
      (mfderiv (𝓡 3) (𝓡 3) (ChartDistance.chartParametrization U hU (O.include i)) x.val w) = _
    rw [ChartDistance.chartParametrization_apply, hd]
    exact (hmetric i x v w).symm
  refine ⟨c, hinverse, ?_, ?_, ?_, hcoeff, ?_⟩
  · intro i
    exact (quotientChart_source U hU O i).trans (image_univ)
  · intro i
    exact quotientChart_target U hU O i
  · intro x
    have hx : x ∈ ⋃ i, (quotientChart U hU O i).source := by
      rw [quotientChart_source_cover U hU O]
      trivial
    exact mem_iUnion.mp hx
  · intro i m y hy
    have hgerm : g.pullbackCoefficients (c i).symm =ᶠ[𝓝 y] B0 i :=
      Filter.Eventually.mono ((hU i).mem_nhds hy) (fun _ hz => hcoeff i hz)
    exact (hgerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds



theorem terminalSource_regular_chart_approximation
    (U : ℕ → Set E) (hU : ∀ i, IsOpen (U i)) [∀ i, Nonempty (Piece U i)]
    {X : Type*} (q : ∀ i, Piece U i → X)
    (M : ℕ → Type u) [∀ k, PseudoMetricSpace (M k)]
    (f : ∀ k, X → M k) (e : ∀ k i, Piece U i → M k)
    (happrox : ∀ i K, IsCompact K → TendstoUniformlyOn
      (fun k (x : Piece U i) => dist (f k (q i x)) (e k i x))
        (fun _ => 0) atTop K) :
    ∀ i K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k y => dist
        (f k (ChartDistance.chartParametrization U hU (q i) y))
        (ChartDistance.chartParametrization U hU (e k i) y)) (fun _ => 0) atTop K := by
  intro i K hK hKU
  let K' : Set (Piece U i) := Subtype.val ⁻¹' K
  have hK' : IsCompact K' :=
    (hU i).isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage'
      hK (by intro y hy; exact ⟨⟨y, hKU hy⟩, rfl⟩)
  rw [Metric.tendstoUniformlyOn_iff]
  intro delta hdelta
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (happrox i K' hK') delta hdelta]
    with k hk y hy
  have h := hk (⟨y, hKU hy⟩ : Piece U i) hy
  rw [ChartDistance.chartParametrization_apply U hU (q i) (⟨y, hKU hy⟩ : Piece U i),
    ChartDistance.chartParametrization_apply U hU (e k i) (⟨y, hKU hy⟩ : Piece U i)]
  exact h

end PoincareConjecture.M47
