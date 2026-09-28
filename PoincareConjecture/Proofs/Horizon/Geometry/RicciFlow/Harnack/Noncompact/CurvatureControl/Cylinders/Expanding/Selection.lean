import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Scalar











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow




theorem exists_expanding_cylinders_of_unbounded_time_scalar
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbad : ∀ K : ℝ, ∃ t ∈ Ioc a b, ∃ x : M,
      K < (t - a) * (F.connection t).scalarCurvature x) :
    ∃ (p : ℕ → M) (τ Q A : ℕ → ℝ),
      Tendsto A atTop atTop ∧ (∀ k, 0 < A k) ∧ (∀ k, 0 < Q k) ∧
      (∀ k, Icc (τ k + (-A k) / Q k) (τ k) ⊆ Icc a b) ∧
      (∀ k, τ k ∈ Icc a b) ∧
      (∀ k, (F.connection (τ k)).scalarCurvature (p k) = Q k) ∧
      (∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
        ∀ x ∈ (F.metric (τ k)).ball (p k) (A k / Real.sqrt (Q k)),
          (F.connection t).scalarCurvature x ≤ 4 * Q k) ∧
      (∀ r : ℝ, 0 < r → ∀ᶠ k in atTop, r / Real.sqrt (Q k) ≤ 1) := by
  classical
  let A : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hA (k : ℕ) : 0 < A k := by dsimp only [A]; positivity
  have hchoose (k : ℕ) : ∃ τ ∈ Icc a b, ∃ p : M, ∃ Q : ℝ,
      (64 * (((m + 1 : ℕ) : ℝ) + 8) * A k) ^ 2 < Q ∧
      0 < Q ∧ (F.connection τ).scalarCurvature p = Q ∧
      2 * A k ≤ Q * (τ - a) ∧
      ∀ t ∈ Icc (τ - A k / Q) τ, ∀ x : M,
        (F.metric τ).edist p x ≤ ENNReal.ofReal (A k / Real.sqrt Q) →
          (F.connection t).scalarCurvature x ≤ 4 * Q := by
    let D := (64 * (((m + 1 : ℕ) : ℝ) + 8) * A k) ^ 2
    obtain ⟨t, ht, x, hx⟩ := hbad (max (D * (b - a)) (2 * A k))
    have hthreshold : 2 * A k ≤ (F.connection t).scalarCurvature x * (t - a) := by
      have := (le_max_right (D * (b - a)) (2 * A k)).trans_lt hx
      nlinarith
    have hR : 0 < (F.connection t).scalarCurvature x := by
      nlinarith [hA k, ht.1]
    have hlarge : D < (F.connection t).scalarCurvature x := by
      have := (le_max_left (D * (b - a)) (2 * A k)).trans_lt hx
      nlinarith [ht.2]
    obtain ⟨τ, hτ, p, _, Q, hQeq, hQ, hQR, hQt, hcyl⟩ :=
      F.exists_scalarCurvature_large_cylinder hC hm hJ hcomplete hoperator x
        (r := 1) zero_lt_one (hA k) ⟨ht.1.le, ht.2⟩
        (by
          let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
            ⟨(F.metric t).toRiemannianMetric⟩
          have hself : (F.metric t).edist x x = 0 := Manifold.riemannianEDist_self
          rw [hself]
          exact bot_le)
        (by simpa only [div_one] using hlarge) hthreshold
    exact ⟨τ, ⟨hτ.1, hτ.2.trans ht.2⟩, p, Q,
      hlarge.trans_le hQR, hQ, hQeq.symm, hQt, hcyl⟩
  choose τ hτ p Q hlarge hQ hnormalize hthreshold hcylinder using hchoose
  have hsub (k : ℕ) : Icc (τ k + (-A k) / Q k) (τ k) ⊆ Icc a b := by
    have hback : A k / Q k ≤ τ k - a := by
      apply (div_le_iff₀ (hQ k)).mpr
      nlinarith [hthreshold k, hA k]
    intro t ht
    constructor
    · rw [neg_div] at ht
      linarith [ht.1]
    · exact ht.2.trans (hτ k).2
  have hAtop : Tendsto A atTop atTop := tendsto_atTop_add_const_right _ 1
    tendsto_natCast_atTop_atTop
  refine ⟨p, τ, Q, A, hAtop, hA, hQ, hsub, hτ, hnormalize, ?_, ?_⟩
  · intro k t ht x hx
    apply hcylinder k t (by simpa only [neg_div, sub_eq_add_neg] using ht) x
    exact (show (F.metric (τ k)).edist (p k) x < _ from hx).le
  · intro r hr
    filter_upwards [hAtop.eventually_ge_atTop r] with k hk
    have hscale : A k < Real.sqrt (Q k) := by
      have hfactor : 1 ≤ 64 * (((m + 1 : ℕ) : ℝ) + 8) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (m + 1)]
      have hmul : A k ≤ 64 * (((m + 1 : ℕ) : ℝ) + 8) * A k :=
        le_mul_of_one_le_left (hA k).le hfactor
      have hsquare := Real.sq_sqrt (hQ k).le
      nlinarith [hlarge k, Real.sqrt_nonneg (Q k), hA k]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (hQ k))).mpr
    simpa only [one_mul] using hk.trans hscale.le

end PoincareConjecture.RicciFlow
