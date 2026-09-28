import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.BallTransfer

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem abs_pullback_inner_sub_le
    (G : PointedGeometricConvergence S) (k : ℕ) (t : ℝ)
    (x : G.limitCarrier.carrier) {ε : ℝ}
    (hclose : ∀ u w : G.limitCarrier.tangent x,
      G.limitCarrier.metricNorm (G.limitFlow.metricAt t) x u ≤ 1 →
      G.limitCarrier.metricNorm (G.limitFlow.metricAt t) x w ≤ 1 →
      |pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
          (G.embedding k) t x u w -
        G.limitCarrier.metricInner (G.limitFlow.metricAt t) x u w| < ε)
    (v : G.limitCarrier.tangent x) :
    |pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)
        t x v v - G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v| ≤
      ε * G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let C := S.carrier (G.subsequence k)
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  by_cases hv : v = 0
  · subst v
    simp [pullbackInnerValue, FlowCarrier.metricInner]
  let a := G.limitCarrier.metricNorm (G.limitFlow.metricAt t) x v
  have ha : 0 < a := Real.sqrt_pos.mpr ((G.limitFlow.metricAt t).pos x v hv)
  have ha2 : a ^ 2 = G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v :=
    Real.sq_sqrt ((G.limitFlow.metricAt t).pos x v hv).le
  have hi : a⁻¹ ^ 2 * a ^ 2 = 1 := by field_simp
  let u : G.limitCarrier.tangent x := a⁻¹ • v
  have hu : G.limitCarrier.metricNorm (G.limitFlow.metricAt t) x u = 1 := by
    change Real.sqrt _ = 1
    simp only [u, FlowCarrier.metricInner, map_smul, smul_apply, smul_eq_mul]
    rw [show a⁻¹ * (a⁻¹ * (G.limitFlow.metricAt t).inner x v v) = 1 by
      change a⁻¹ * (a⁻¹ * G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v) = 1
      rw [← ha2]
      nlinarith [hi]]
    exact Real.sqrt_one
  have hc := (hclose u u hu.le hu.le).le
  have hscale :
      pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)
          t x u u - G.limitCarrier.metricInner (G.limitFlow.metricAt t) x u u =
        a⁻¹ ^ 2 *
          (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)
            t x v v - G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v) := by
    simp only [u, pullbackInnerValue, FlowCarrier.metricInner, map_smul,
      smul_apply, smul_eq_mul]
    ring
  rw [hscale, abs_mul, abs_of_nonneg (sq_nonneg _)] at hc
  have h := mul_le_mul_of_nonneg_right hc (sq_nonneg a)
  rw [mul_comm (a⁻¹ ^ 2), mul_assoc, hi, mul_one, ha2] at h
  exact h

theorem eventually_pullback_inner_bounds
    (G : PointedGeometricConvergence S) {K : Set G.limitCarrier.carrier}
    (hK : @IsCompact G.limitCarrier.carrier G.limitCarrier.topologicalSpace K)
    {t : ℝ} (ht : t ∈ Ioo T' T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ v : G.limitCarrier.tangent x,
      (1 - ε) * G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v ≤
        pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)
          t x v v ∧
      pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)
          t x v v ≤
        (1 + ε) * G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  obtain ⟨N, _, hN⟩ := G.pullback_metric_converges j K {t} hK hj
    isCompact_singleton (singleton_subset_iff.mpr ht) ε hε
  filter_upwards [eventually_ge_atTop N] with k hk x hx v
  have h := abs_le.mp (G.abs_pullback_inner_sub_le k t x
    (hN k hk t (mem_singleton t) x hx) v)
  constructor <;> linarith [h.1, h.2]

theorem eventually_pullback_tangentNorm_bounds
    (G : PointedGeometricConvergence S) {K : Set G.limitCarrier.carrier}
    (hK : @IsCompact G.limitCarrier.carrier G.limitCarrier.topologicalSpace K)
    {t C : ℝ} (ht : t ∈ Ioo T' T) (hC : 1 < C) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ v : G.limitCarrier.tangent x,
      Real.sqrt (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
          (G.embedding k) t x v v) ≤
        C * G.limitCarrier.metricNorm (G.limitFlow.metricAt t) x v ∧
      G.limitCarrier.metricNorm (G.limitFlow.metricAt t) x v ≤
        C * Real.sqrt (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
          (G.embedding k) t x v v) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hupper : 0 < C ^ 2 - 1 := by nlinarith
  have hlower : 0 < 1 - C⁻¹ ^ 2 := by
    have hi := inv_pos.mpr hCpos
    have hi1 := (inv_lt_one₀ hCpos).mpr hC
    nlinarith
  let ε := min (C ^ 2 - 1) (1 - C⁻¹ ^ 2)
  filter_upwards [G.eventually_pullback_inner_bounds hK ht (lt_min hupper hlower)]
    with k hk x hx v
  let a := G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v
  let b := pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k) t x v v
  have ha : 0 ≤ a := by
    by_cases hv : v = 0
    · simp [a, hv, FlowCarrier.metricInner]
    · exact ((G.limitFlow.metricAt t).pos x v hv).le
  have hh := hk x hx v
  change (1 - ε) * a ≤ b ∧ b ≤ (1 + ε) * a at hh
  have he1 : ε ≤ C ^ 2 - 1 := min_le_left _ _
  have he2 : ε ≤ 1 - C⁻¹ ^ 2 := min_le_right _ _
  have hab : b ≤ C ^ 2 * a := hh.2.trans
    (mul_le_mul_of_nonneg_right (by linarith) ha)
  have hba : a ≤ C ^ 2 * b := by
    have hh' : C⁻¹ ^ 2 * a ≤ b :=
      (mul_le_mul_of_nonneg_right (by linarith) ha).trans hh.1
    have hm := mul_le_mul_of_nonneg_left hh' (sq_nonneg C)
    have hi : C ^ 2 * C⁻¹ ^ 2 = 1 := by field_simp
    simpa only [← mul_assoc, hi, one_mul] using hm
  change Real.sqrt b ≤ C * Real.sqrt a ∧ Real.sqrt a ≤ C * Real.sqrt b
  constructor
  · rw [← Real.sqrt_sq hCpos.le, ← Real.sqrt_mul (sq_nonneg C)]
    exact Real.sqrt_le_sqrt hab
  · rw [← Real.sqrt_sq hCpos.le, ← Real.sqrt_mul (sq_nonneg C)]
    exact Real.sqrt_le_sqrt hba

end PoincareConjecture.PointedGeometricConvergence
