import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowCompleteness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem partialFlow_compactPullback_ellipticity (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
    {S B : ℝ} (hSF : S ≤ F.lifetime) (hB : 0 ≤ B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ t ∈ Ico 0 S, ∀ x ∈ K,
      ∀ e : StandardCapSpace → StandardCapSpace,
      (∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v)) →
      ∀ v : StandardCapSpace,
        a * ‖v‖ ^ 2 ≤ (F.flow.metric t).pullbackCoefficients e x v v ∧
          (F.flow.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2 := by
  have hcont : ContinuousOn g0.metric.euclideanCoefficients K :=
    fun x _ => (g0.metric.contDiffAt_euclideanCoefficients x).continuousAt.continuousWithinAt
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hcont
    (fun x _ v hv => g0.metric.pos x v hv)
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn
    (f := g0.metric.euclideanCoefficients) hcont
  have hupper (x : StandardCapSpace) (hx : x ∈ K) (v : StandardCapSpace) :
      g0.metric.inner x v v ≤ max b 0 * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖g0.metric.euclideanCoefficients x v v‖ := le_abs_self _
      _ ≤ ‖g0.metric.euclideanCoefficients x‖ * ‖v‖ * ‖v‖ :=
        (g0.metric.euclideanCoefficients x).le_opNorm₂ v v
      _ = ‖g0.metric.euclideanCoefficients x‖ * ‖v‖ ^ 2 := by ring
      _ ≤ max b 0 * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right ((hb x hx).trans (le_max_left _ _)) (sq_nonneg _)
  refine ⟨Real.exp (-6 * B * S) * a, Real.exp (6 * B * S) * max b 0,
    mul_pos (Real.exp_pos _) ha, by positivity, ?_⟩
  intro t ht x hx e he v
  have hcomparison := partialFlow_exp_bounds F P ⟨ht.1, ht.2.trans_le hSF⟩ hB
    (fun s hs y => hfull s ⟨hs.1, hs.2.trans_lt ht.2⟩ y)
    (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
  rw [← he v v] at hcomparison
  change Real.exp (-6 * B * t) * g0.metric.inner x v v ≤
      (F.flow.metric t).pullbackCoefficients e x v v ∧
    (F.flow.metric t).pullbackCoefficients e x v v ≤
      Real.exp (6 * B * t) * g0.metric.inner x v v at hcomparison
  have hnonneg : 0 ≤ g0.metric.inner x v v :=
    (mul_nonneg ha.le (sq_nonneg _)).trans (hlower x hx v)
  have htime := mul_le_mul_of_nonneg_left ht.2.le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hB)
  constructor
  · calc
      _ = Real.exp (-6 * B * S) * (a * ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-6 * B * S) * g0.metric.inner x v v :=
        mul_le_mul_of_nonneg_left (hlower x hx v) (Real.exp_pos _).le
      _ ≤ Real.exp (-6 * B * t) * g0.metric.inner x v v :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hnonneg
      _ ≤ _ := hcomparison.1
  · calc
      _ ≤ Real.exp (6 * B * t) * g0.metric.inner x v v := hcomparison.2
      _ ≤ Real.exp (6 * B * S) * g0.metric.inner x v v :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htime) hnonneg
      _ ≤ Real.exp (6 * B * S) * (max b 0 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hupper x hx v) (Real.exp_pos _).le
      _ = _ := by ring

end PoincareConjecture.M34
