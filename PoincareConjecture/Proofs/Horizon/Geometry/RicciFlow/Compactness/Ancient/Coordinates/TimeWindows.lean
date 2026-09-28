import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.NormalCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

namespace RicciFlow

theorem pullbackCoefficients_exp_bounds_of_ricci_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {T' T K : ℝ}
    (hT : T' < 0 ∧ 0 < T) (hTJ : Ioo T' T ⊆ J) (hK : 0 ≤ K)
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hRic : ∀ t ∈ Ioo T' T, ∀ v : TangentSpace (𝓡 n) (e x),
      |(F.connection t).ricci (e x) v v| ≤ K * (F.metric t).inner (e x) v v)
    {t : ℝ} (ht : t ∈ Ioo T' T) (v : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-(2 * K) * (T - T')) *
        (F.metric 0).pullbackCoefficients e x v v ≤
      (F.metric t).pullbackCoefficients e x v v ∧
    (F.metric t).pullbackCoefficients e x v v ≤
      Real.exp ((2 * K) * (T - T')) *
        (F.metric 0).pullbackCoefficients e x v v := by
  let w := mfderiv (𝓡 n) (𝓡 n) e x v
  have hnonneg : 0 ≤ (F.metric 0).inner (e x) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric 0).pos (e x) w hw).le
  have h := F.metric_inner_self_exp_bounds (convex_Ioo T' T) hTJ
    (e x) w K (fun s hs => hRic s hs w) hT ht
  have htime : |t - 0| ≤ T - T' := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hT.1, hT.2]
  have hC : 0 ≤ 2 * K := by positivity
  change Real.exp (-(2 * K) * (T - T')) * (F.metric 0).inner (e x) w w ≤
      (F.metric t).inner (e x) w w ∧
    (F.metric t).inner (e x) w w ≤
      Real.exp ((2 * K) * (T - T')) * (F.metric 0).inner (e x) w w
  constructor
  · apply le_trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr ?_) hnonneg) h.1
    nlinarith [mul_le_mul_of_nonneg_left htime hC]
  · apply h.2.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr ?_) hnonneg)
    exact mul_le_mul_of_nonneg_left htime hC

end RicciFlow

namespace NormalChartCover

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {p : M}
  {T' T U' U A R ρ a b K : ℝ} {N : ℕ}

def extendTime (C : NormalChartCover F.metric p T' T A R ρ a b N)
    (hT : T' < 0 ∧ 0 < T) (hU : U' < 0 ∧ 0 < U) (hUJ : Ioo U' U ⊆ J)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hRic : ∀ i, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ t ∈ Ioo U' U,
      ∀ v : TangentSpace (𝓡 n) (C.chart i x),
        |(F.connection t).ricci (C.chart i x) v v| ≤
          K * (F.metric t).inner (C.chart i x) v v) :
    NormalChartCover F.metric p U' U A R ρ
      (Real.exp (-(2 * K) * (U - U')) * a)
      (Real.exp ((2 * K) * (U - U')) * b) N := by
  have hD : 0 ≤ (2 * K) * (U - U') :=
    mul_nonneg (by positivity) (by linarith [hU.1, hU.2])
  have hlower : Real.exp (-(2 * K) * (U - U')) * a ≤ a := by
    calc
      Real.exp (-(2 * K) * (U - U')) * a ≤ 1 * a :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_one_iff.mpr (by nlinarith)) ha
      _ = a := one_mul a
  have hupper : b ≤ Real.exp ((2 * K) * (U - U')) * b := by
    calc
      b = 1 * b := (one_mul b).symm
      _ ≤ Real.exp ((2 * K) * (U - U')) * b :=
        mul_le_mul_of_nonneg_right (Real.one_le_exp_iff.mpr hD) hb
  refine { C with coefficients := ?_, distances := ?_ }
  · intro i t ht x hx v
    obtain ⟨hl, hu⟩ := F.pullbackCoefficients_exp_bounds_of_ricci_bound
      hU hUJ hK (C.chart i) x (hRic i x hx) ht v
    obtain ⟨hl0, hu0⟩ := C.coefficients i 0 hT x hx v
    constructor
    · calc
        (Real.exp (-(2 * K) * (U - U')) * a) * ‖v‖ ^ 2 =
            Real.exp (-(2 * K) * (U - U')) * (a * ‖v‖ ^ 2) := mul_assoc _ _ _
        _ ≤ Real.exp (-(2 * K) * (U - U')) *
            (F.metric 0).pullbackCoefficients (C.chart i) x v v :=
          mul_le_mul_of_nonneg_left hl0 (Real.exp_nonneg _)
        _ ≤ (F.metric t).pullbackCoefficients (C.chart i) x v v := hl
    · calc
        (F.metric t).pullbackCoefficients (C.chart i) x v v ≤
            Real.exp ((2 * K) * (U - U')) *
              (F.metric 0).pullbackCoefficients (C.chart i) x v v := hu
        _ ≤ Real.exp ((2 * K) * (U - U')) * (b * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hu0 (Real.exp_nonneg _)
        _ = (Real.exp ((2 * K) * (U - U')) * b) * ‖v‖ ^ 2 :=
          (mul_assoc _ _ _).symm
  · intro i x hx y hy
    obtain ⟨hl, hu⟩ := C.distances i x hx y hy
    exact ⟨(mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hlower)
      (dist_nonneg : 0 ≤ dist x y)).trans hl,
      hu.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hupper) dist_nonneg)⟩

@[simp] theorem extendTime_chart
    (C : NormalChartCover F.metric p T' T A R ρ a b N)
    (hT : T' < 0 ∧ 0 < T) (hU : U' < 0 ∧ 0 < U) (hUJ : Ioo U' U ⊆ J)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hRic : ∀ i, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ t ∈ Ioo U' U,
      ∀ v : TangentSpace (𝓡 n) (C.chart i x),
        |(F.connection t).ricci (C.chart i x) v v| ≤
          K * (F.metric t).inner (C.chart i x) v v) :
    (C.extendTime hT hU hUJ ha hb hK hRic).chart = C.chart := rfl

@[simp] theorem extendTime_centre
    (C : NormalChartCover F.metric p T' T A R ρ a b N)
    (hT : T' < 0 ∧ 0 < T) (hU : U' < 0 ∧ 0 < U) (hUJ : Ioo U' U ⊆ J)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hRic : ∀ i, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ t ∈ Ioo U' U,
      ∀ v : TangentSpace (𝓡 n) (C.chart i x),
        |(F.connection t).ricci (C.chart i x) v v| ≤
          K * (F.metric t).inner (C.chart i x) v v) :
    (C.extendTime hT hU hUJ ha hb hK hRic).centre = C.centre := rfl

def extendTimeOfCurvatureBound [T2Space M]
    (C : NormalChartCover F.metric p T' T A R ρ a b N)
    (hT : T' < 0 ∧ 0 < T) (hU : U' < 0 ∧ 0 < U) (hUJ : Ioo U' U ⊆ J)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hcurv : ∀ i, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ t ∈ Ioo U' U,
      (F.connection t).curvatureTensorNorm (C.chart i x) ≤ K) :
    NormalChartCover F.metric p U' U A R ρ
      (Real.exp (-(2 * ((n : ℝ) ^ 3 * K)) * (U - U')) * a)
      (Real.exp ((2 * ((n : ℝ) ^ 3 * K)) * (U - U')) * b) N := by
  apply C.extendTime hT hU hUJ ha hb (by positivity)
  intro i x hx t ht v
  have h := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm (C.chart i x) v
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) (C.chart i x)) = n :=
    finrank_euclideanSpace_fin
  simp only [Fintype.card_fin, hdim] at h
  have hnonneg : 0 ≤ (F.metric t).inner (C.chart i x) v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((F.metric t).pos (C.chart i x) v hv).le
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hcurv i x hx t ht) (by positivity)) hnonneg)

@[simp] theorem extendTimeOfCurvatureBound_chart [T2Space M]
    (C : NormalChartCover F.metric p T' T A R ρ a b N)
    (hT : T' < 0 ∧ 0 < T) (hU : U' < 0 ∧ 0 < U) (hUJ : Ioo U' U ⊆ J)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hcurv : ∀ i, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ t ∈ Ioo U' U,
      (F.connection t).curvatureTensorNorm (C.chart i x) ≤ K) :
    (C.extendTimeOfCurvatureBound hT hU hUJ ha hb hK hcurv).chart = C.chart := rfl

def extendTimeOfCurvatureBoundOnBall [T2Space M]
    (C : NormalChartCover F.metric p T' T A R ρ a b N)
    (hT : T' < 0 ∧ 0 < T) (hU : U' < 0 ∧ 0 < U) (hUJ : Ioo U' U ⊆ J)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hρR : 2 * ρ < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo U' U, ∀ x ∈ (F.metric 0).ball p (A + R),
      (F.connection t).curvatureTensorNorm x ≤ K) :
    NormalChartCover F.metric p U' U A R ρ
      (Real.exp (-(2 * ((n : ℝ) ^ 3 * K)) * (U - U')) * a)
      (Real.exp ((2 * ((n : ℝ) ^ 3 * K)) * (U - U')) * b) N :=
  C.extendTimeOfCurvatureBound hT hU hUJ ha hb hK
    (fun i _x hx t ht => hcurv t ht _
      (C.image_mem_zeroBall hA hR i (Metric.closedBall_subset_ball hρR hx)))

@[simp] theorem extendTimeOfCurvatureBoundOnBall_chart [T2Space M]
    (C : NormalChartCover F.metric p T' T A R ρ a b N)
    (hT : T' < 0 ∧ 0 < T) (hU : U' < 0 ∧ 0 < U) (hUJ : Ioo U' U ⊆ J)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hρR : 2 * ρ < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo U' U, ∀ x ∈ (F.metric 0).ball p (A + R),
      (F.connection t).curvatureTensorNorm x ≤ K) :
    (C.extendTimeOfCurvatureBoundOnBall hT hU hUJ hA hR hρR ha hb hK hcurv).chart =
      C.chart := rfl

end NormalChartCover
end PoincareConjecture
