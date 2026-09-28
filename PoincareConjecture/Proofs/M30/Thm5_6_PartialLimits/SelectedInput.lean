import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.PartialWindowService
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff Bundle
open PoincareConjecture.ChartDistance

universe u

namespace PoincareConjecture.M30

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1000000 in




theorem exists_selectedParabolicApplicationData_of_retained_charts
    {M : ℕ → Type u} [∀ k : ℕ, MetricSpace (M k)]
    [∀ k : ℕ, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k : ℕ, IsManifold (𝓡 3) ∞ (M k)]
    {tau A B : ℝ} (htau : 0 < tau) (hA : 0 < A)
    (F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0))
    (p : ∀ k, M k)
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 3)))
    (hU : ∀ i, IsOpen (U i)) (hconvex : ∀ i, Convex ℝ (U i))
    [∀ i, Nonempty (Piece U i)]
    (e : ∀ k i, Piece U i → M k)
    (D : ∀ i j, C(Piece U i × Piece U j, ℝ))
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (z : Piece U i × Piece U j) => dist (e k i z.1) (e k j z.2))
      (D i j) atTop)
    (L : ℕ → ℝ≥0) (hL : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hballs : ∀ k (q : M k) r, IsPreconnected (Metric.ball q r))
    (hsmooth :
      letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k i))
    (htransition : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative (U := U) (hU := hU)
        (i := i) (j := j)
        (fun x : Piece U i => Function.invFun (e k j) (e k i x))))
    (i₀ : ℕ) (z₀ : Piece U i₀)
    (hbase : ∀ k, e k i₀ z₀ = p k)
    (hrange : ∀ i (x : Piece U i), D i₀ i (z₀, x) < A)
    (hcover : ∀ R : ℝ, 0 < R → R < A → ∃ s : Finset ℕ,
      ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, Metric.ball (e k i₀ z₀) R ⊆
          ⋃ i ∈ s, e k i '' K i)
    (hdist : ∀ k (x y : M k), edist x y = ((F k).metric 0).edist x y)
    (hRm : ∀ k, ∀ t ∈ Icc (-tau) 0, ∀ x : M k,
      ((F k).connection t).curvatureTensorNorm x ≤ B)
    (hderivatives : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Icc (-tau) 0, ∀ x ∈ ((F k).metric 0).ball (p k) A,
        ((F k).connection t).curvatureDerivativeNorm m x ≤ C)
    (hcapture : ∀ i V, IsCompact V → V ⊆ U i →
      ∀ᶠ k in atTop, ∀ x ∈ V,
        chartParametrization U hU (e k i) x ∈
          ((F k).metric 0).ball (p k) A)
    (hterminal : ∀ i V, IsCompact V → V ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ k in atTop,
        ∀ x ∈ V, ∀ v,
          a * ‖v‖ ^ 2 ≤
              ((F k).metric 0).pullbackCoefficients
                (chartParametrization U hU (e k i)) x v v ∧
            ((F k).metric 0).pullbackCoefficients
                (chartParametrization U hU (e k i)) x v v ≤ b * ‖v‖ ^ 2)
    (hinitial : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => ((F k).metric 0).pullbackCoefficients
        (chartParametrization U hU (e k i))))
    (hMixed :
      ∀ (U₁ V₁ : ℕ → Set (EuclideanSpace ℝ (Fin 3)))
        (f : ∀ k, EuclideanSpace ℝ (Fin 3) → M k),
        (∀ k, IsOpen (U₁ k)) →
        (∀ k, V₁ k ⊆ U₁ k) →
        (∀ k, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f k) (U₁ k)) →
        (∀ k y, y ∈ U₁ k → (mfderiv (𝓡 3) (𝓡 3) (f k) y).IsInvertible) →
        ∀ a b : ℝ, 0 < a → 0 ≤ b →
          (∀ᶠ k in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V₁ k, ∀ v,
            a * ‖v‖ ^ 2 ≤ ((F k).metric t).pullbackCoefficients (f k) x v v ∧
              ((F k).metric t).pullbackCoefficients (f k) x v v ≤ b * ‖v‖ ^ 2) →
          (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
            ∀ t ∈ Ioo (-tau) 0, ∀ x ∈ V₁ k,
              ((F k).connection t).curvatureDerivativeNorm m (f k x) ≤ C) →
          (∀ m : ℕ, ∃ Z : ℝ, 0 ≤ Z ∧ ∀ᶠ k in atTop, ∀ x ∈ V₁ k,
            ‖iteratedFDeriv ℝ m (((F k).metric 0).pullbackCoefficients (f k)) x‖ ≤ Z) →
          ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
            ∀ z ∈ Icc (-tau) 0 ×ˢ V₁ k,
              ‖iteratedFDerivWithin ℝ m
                (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
                  ((F k).metric z.1).pullbackCoefficients (f k) z.2)
                (Icc (-tau) 0 ×ˢ U₁ k) z‖ ≤ C) :
    ∃ H : SelectedParabolicApplicationData (M := M) tau A,
      H.U = U ∧ H.flow = F ∧ HEq H.embedding e ∧
        H.base_index = i₀ ∧ HEq H.base_point z₀ ∧
          ∀ k, H.embedding k H.base_index H.base_point = p k := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let K := max B 1
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_right B 1)
  have hzero : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨by linarith, le_rfl⟩
  have hchart (k i : ℕ) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ U i) :
      (mfderiv (𝓡 3) (𝓡 3) (chartParametrization U hU (e k i)) x).IsInvertible := by
    rw [mfderiv_chartParametrization U hU (⟨x, hx⟩ : Piece U i)
      (hsmooth k i ⟨x, hx⟩).contMDiffAt]
    exact ⟨(hsmooth k i ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have helliptic (i : ℕ) (V : Set (EuclideanSpace ℝ (Fin 3)))
      (hV : IsCompact V) (hVU : V ⊆ U i) :
      ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V, ∀ v,
          a * ‖v‖ ^ 2 ≤ ((F k).metric t).pullbackCoefficients
            (chartParametrization U hU (e k i)) x v v ∧
          ((F k).metric t).pullbackCoefficients
            (chartParametrization U hU (e k i)) x v v ≤ b * ‖v‖ ^ 2 := by
    obtain ⟨a, ha, b, hb, htail⟩ := hterminal i V hV hVU
    refine ⟨Real.exp (-6 * K * tau) * a, mul_pos (Real.exp_pos _) ha,
      Real.exp (6 * K * tau) * b, mul_nonneg (Real.exp_pos _).le hb, ?_⟩
    filter_upwards [htail] with k hk t ht x hx v
    let f := chartParametrization U hU (e k i)
    let w := mfderiv (𝓡 3) (𝓡 3) f x v
    have hcmp := M04.metric_comparison_at_of_curvature_bound (F k) ht hzero ht.2 hK
      (f x) (fun s hs => (hRm k s ⟨ht.1.trans hs.1, hs.2⟩ (f x)).trans
        (le_max_left B 1)) w
    norm_num only [Nat.cast_ofNat, zero_sub] at hcmp
    have hcancel : Real.exp (-6 * K * -t) * Real.exp (6 * K * -t) = 1 := by
      rw [← Real.exp_add, show -6 * K * -t + 6 * K * -t = 0 by ring, Real.exp_zero]
    have hbackLower := mul_le_mul_of_nonneg_left hcmp.2 (Real.exp_pos (-6 * K * -t)).le
    rw [← mul_assoc, hcancel, one_mul] at hbackLower
    have hbackUpper := mul_le_mul_of_nonneg_left hcmp.1 (Real.exp_pos (6 * K * -t)).le
    rw [← mul_assoc, mul_comm (Real.exp (6 * K * -t)), hcancel, one_mul] at hbackUpper
    have hnonneg : 0 ≤ ((F k).metric 0).pullbackCoefficients f x v v :=
      (mul_nonneg ha.le (sq_nonneg ‖v‖)).trans (hk x hx v).1
    have hneg : Real.exp (-6 * K * tau) ≤ Real.exp (-6 * K * -t) := by
      apply Real.exp_le_exp.mpr
      have hlength : -t ≤ tau := by linarith [ht.1]
      exact mul_le_mul_of_nonpos_left hlength (by nlinarith [hK])
    have hpos : Real.exp (6 * K * -t) ≤ Real.exp (6 * K * tau) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by positivity)
    constructor
    · calc
        (Real.exp (-6 * K * tau) * a) * ‖v‖ ^ 2 =
            Real.exp (-6 * K * tau) * (a * ‖v‖ ^ 2) := mul_assoc _ _ _
        _ ≤ Real.exp (-6 * K * tau) * ((F k).metric 0).pullbackCoefficients f x v v :=
          mul_le_mul_of_nonneg_left (hk x hx v).1 (Real.exp_pos _).le
        _ ≤ Real.exp (-6 * K * -t) * ((F k).metric 0).pullbackCoefficients f x v v :=
          mul_le_mul_of_nonneg_right hneg hnonneg
        _ ≤ ((F k).metric t).pullbackCoefficients f x v v := hbackLower
    · calc
        ((F k).metric t).pullbackCoefficients f x v v ≤
            Real.exp (6 * K * -t) * ((F k).metric 0).pullbackCoefficients f x v v := hbackUpper
        _ ≤ Real.exp (6 * K * tau) * ((F k).metric 0).pullbackCoefficients f x v v :=
          mul_le_mul_of_nonneg_right hpos hnonneg
        _ ≤ Real.exp (6 * K * tau) * (b * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hk x hx v).2 (Real.exp_pos _).le
        _ = (Real.exp (6 * K * tau) * b) * ‖v‖ ^ 2 := (mul_assoc _ _ _).symm
  let H : SelectedParabolicApplicationData (M := M) tau A := by
    refine {
      tau_pos := htau
      U := U
      isOpen_U := hU
      convex_U := hconvex
      piece_nonempty := fun _ => inferInstance
      embedding := e
      distance_limit := D
      distance_limit_spec := hD
      lipschitz_constant := L
      lipschitz := hL
      lower_constant := c
      lower_constant_pos := hc
      lower_distance := hlower
      open_embedding := hopen
      ball_preconnected := hballs
      smooth := hsmooth
      transition_bounds := htransition
      base_index := i₀
      base_point := z₀
      radius_pos := hA
      range_bound := hrange
      compact_cover := hcover
      flow := F
      distance_eq := hdist
      metric_jets := ?_
      positive_ellipticity := ?_ }
    · intro i Z hZ hZU m
      let V : Set (EuclideanSpace ℝ (Fin 3)) := Prod.snd '' Z
      have hV : IsCompact V := hZ.image continuous_snd
      have hVU : V ⊆ U i := by
        rintro x ⟨z, hz, rfl⟩
        exact (hZU hz).2
      obtain ⟨a, ha, b, hb, hell⟩ := helliptic i V hV hVU
      have hcurv (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
          ∀ t ∈ Ioo (-tau) 0, ∀ x ∈ V,
            ((F k).connection t).curvatureDerivativeNorm j
              (chartParametrization U hU (e k i) x) ≤ C := by
        obtain ⟨C, hC, hbound⟩ := hderivatives j
        refine ⟨C, hC, ?_⟩
        filter_upwards [hbound, hcapture i V hV hVU] with k hk hcap t ht x hx
        exact hk t ⟨ht.1.le, ht.2.le⟩ _ (hcap x hx)
      have hinit (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ V,
          ‖iteratedFDeriv ℝ j (((F k).metric 0).pullbackCoefficients
            (chartParametrization U hU (e k i))) x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hinitial i V hV hVU j
        refine ⟨max C 0, le_max_right C 0, ?_⟩
        filter_upwards [hC] with k hk x hx
        exact (hk x hx).trans (le_max_left C 0)
      obtain ⟨C, _, hC⟩ := hMixed (fun _ => U i) (fun _ => V)
        (fun k => chartParametrization U hU (e k i)) (fun _ => hU i) (fun _ => hVU)
        (fun k => contMDiffOn_chartParametrization U hU (hsmooth k i).contMDiff)
        (fun k x hx => hchart k i x hx) a b ha hb hell hcurv hinit m
      refine ⟨C, ?_⟩
      filter_upwards [hC] with k hk z hz
      exact hk z ⟨(hZU hz).1, ⟨z, hz, rfl⟩⟩
    · intro t ht i x hx
      obtain ⟨a, ha, b, hb, htail⟩ :=
        helliptic i {x} isCompact_singleton (singleton_subset_iff.mpr hx)
      refine ⟨a, ha, ?_⟩
      filter_upwards [htail] with k hk v
      exact (hk t ht x (mem_singleton x) v).1
  exact ⟨H, rfl, rfl, HEq.rfl, rfl, HEq.rfl, hbase⟩

end PoincareConjecture.M30
