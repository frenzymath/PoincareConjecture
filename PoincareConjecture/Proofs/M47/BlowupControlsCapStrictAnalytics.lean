import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticMargins
import PoincareConjecture.Proofs.M47.CanonicalScalarStability

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem exists_cap_strict_analytic_tolerance {g : RiemannianMetric 3 M}
    (N : CapCertificate g) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ bR bG bE : ℝ,
      bR < N.cap_constant ∧ bG < N.cap_constant ∧ bE < N.cap_constant ∧
      ∀ R G E : M → ℝ,
        (∀ x ∈ N.carrier,
          |R x - N.connection.scalarCurvature x| ≤ nu ∧
          |G x - scalarGradientNorm g N.connection x| ≤ nu ∧
          |E x - (N.connection.laplacian N.connection.scalarCurvature x +
            2 * N.connection.ricciNormSq x)| ≤ nu) →
        (∀ x ∈ N.carrier, 0 < R x) ∧
        (∀ x ∈ N.carrier, ∀ y ∈ N.carrier, R y ≤ bR * R x) ∧
        (∀ x ∈ N.carrier, G x ≤ bG * R x ^ (3 / 2 : ℝ)) ∧
        ∀ x ∈ N.carrier, |E x| ≤ bE * R x ^ 2 := by
  obtain ⟨m, hm, b, hb, hbC, hfloor, hratio⟩ := Proofs.M47.cap_uniform_scalar_lower N
  obtain ⟨o, ho⟩ := N.core_nonempty
  have hoc : o ∈ N.carrier := by
    have hclosed : o ∈ N.closed_core :=
      interior_subset (N.core_eq_interior_closed_core ▸ ho)
    exact (N.closed_core_eq_complement_end ▸ hclosed).1
  let upper := b * N.connection.scalarCurvature o
  have hrange (x : M) (hx : x ∈ N.carrier) :
      N.connection.scalarCurvature x ∈ Icc m upper :=
    ⟨hfloor x hx, hratio o hoc x hx⟩
  obtain ⟨nuR, hnuR, bR, hbR, hR⟩ := exists_cap_scalar_ratio_margin hm hb hbC
  obtain ⟨g0, hg0, hgradient⟩ := N.gradient_bound
  have hgC : max g0 0 < N.cap_constant := max_lt hg0 N.cap_constant_pos
  obtain ⟨nuG, hnuG, bG, _, hbG, hG⟩ := exists_cap_power_margin
    (M := upper) hm (le_max_right g0 0) hgC (show 0 ≤ (3 / 2 : ℝ) by norm_num)
  obtain ⟨e0, he0, hevolution⟩ := N.laplacian_bound
  have heC : max e0 0 < N.cap_constant := max_lt he0 N.cap_constant_pos
  obtain ⟨nuE, hnuE, bE, _, hbE, hE⟩ := exists_cap_power_margin
    (M := upper) hm (le_max_right e0 0) heC (show (0 : ℝ) ≤ 2 by norm_num)
  let nu := min nuR (min nuG nuE)
  have hnu : 0 < nu := lt_min hnuR (lt_min hnuG hnuE)
  have hnR : nu ≤ nuR := min_le_left _ _
  have hnG : nu ≤ nuG := (min_le_right _ _).trans (min_le_left _ _)
  have hnE : nu ≤ nuE := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨nu, hnu, bR, bG, bE, hbR, hbG, hbE, ?_⟩
  intro R G E hclose
  have hscalar (x : M) (hx : x ∈ N.carrier) (y : M) (hy : y ∈ N.carrier) :=
    hR _ _ (R x) (R y) (hfloor x hx) (hratio x hx y hy)
      ((hclose x hx).1.trans hnR) ((hclose y hy).1.trans hnR)
  refine ⟨fun x hx => (hscalar x hx x hx).1,
    fun x hx y hy => (hscalar x hx y hy).2, ?_, ?_⟩
  · intro x hx
    have hbound := (hgradient x hx).trans (mul_le_mul_of_nonneg_right
      (le_max_left g0 0) (Real.rpow_nonneg (N.scalar_pos x hx).le _))
    exact (hG _ (hrange x hx) _ (R x) (G x) hbound
      ((hclose x hx).1.trans hnG) ((hclose x hx).2.1.trans hnG)).2
  · intro x hx
    have hbound := (hevolution x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left e0 0) (sq_nonneg _))
    have hdiff := (abs_abs_sub_abs_le_abs_sub (E x)
      (N.connection.laplacian N.connection.scalarCurvature x +
        2 * N.connection.ricciNormSq x)).trans ((hclose x hx).2.2.trans hnE)
    have h := (hE _ (hrange x hx) _ (R x) |E x|
      (by simpa only [Real.rpow_two] using hbound)
      ((hclose x hx).1.trans hnE) hdiff).2
    simpa only [Real.rpow_two] using h

end PoincareConjecture.M47
