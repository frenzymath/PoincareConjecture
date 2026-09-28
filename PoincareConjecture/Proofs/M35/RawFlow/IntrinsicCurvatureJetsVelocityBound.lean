import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsBounds
import PoincareConjecture.Proofs.M35.RawFlow.RawRadialVelocityBound
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicEvolution










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

private theorem velocity_jet_bound
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (j : ℕ) {C : ℝ} (hC : ∀ x, D.curvatureDerivativeNorm j x ≤ C)
    {r : ℝ} (hr : 0 ≤ r) :
    |iteratedDeriv (j + 1) (intrinsicRadialVelocity g hrotation hcomplete) r| ≤ 2 * C := by
  let v := intrinsicRadialVelocity g hrotation hcomplete
  let K := intrinsicCurvatureJet g hrotation hcomplete D 0
  have hp (s : ℝ) (hs : 0 < s) : |iteratedDeriv (j + 1) v s| ≤ 2 * C := by
    have heq : deriv v =ᶠ[𝓝 s] fun q => -2 * K q := by
      filter_upwards [eventually_gt_nhds hs] with q hq
      dsimp only [v, K]
      rw [(intrinsicRadialVelocity_hasDerivAt g hrotation hcomplete q).deriv,
        intrinsicRadialAcceleration_eq g hrotation hcomplete hq,
        intrinsicCurvatureJet_zero_eq g hrotation hcomplete D hq]
      ring
    have hh := heq.iteratedDeriv_eq j
    rw [← iteratedDeriv_succ', iteratedDeriv_const_mul_field] at hh
    rw [hh, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left
      (intrinsicCurvatureJet_iteratedDeriv_bound g hrotation hcomplete D j hC hs.le)
      (by norm_num)
  have hc := (intrinsicRadialVelocity_contDiff g hrotation hcomplete).continuous_iteratedDeriv
    (j + 1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl (j + 1))
  have hclosed : IsClosed {s : ℝ | |iteratedDeriv (j + 1) v s| ≤ 2 * C} :=
    isClosed_le hc.abs continuous_const
  exact closure_minimal (s := Ioi (0 : ℝ)) hp hclosed (by rwa [closure_Ioi])



theorem raw_intrinsic_velocity_jets_bounded_on_slab
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) :
    ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 0,
      |iteratedDeriv j (rawRadialVelocity P G hrotation t) r| ≤ C := by
  intro j
  cases j with
  | zero =>
      obtain ⟨C, hC, hCb⟩ := raw_intrinsic_radial_velocity_bounded P G hT.le hTlt
      refine ⟨C, hC, ?_⟩
      intro t ht r _
      rw [iteratedDeriv_zero, rawRadialVelocity_eq P G hrotation ⟨ht.1, ht.2.trans_lt hTlt⟩]
      exact hCb t ht _ r
  | succ j =>
      obtain ⟨C, hC, hCb⟩ := raw_curvature_derivatives_bounded_on_slab P H G hT hTlt j
      refine ⟨2 * C, by positivity, ?_⟩
      intro t ht r hr
      rw [rawRadialVelocity_eq P G hrotation ⟨ht.1, ht.2.trans_lt hTlt⟩]
      exact velocity_jet_bound _ _ _ (G.flow.connection t) j (hCb t ht) hr

end PoincareConjecture.M35.Uniqueness
