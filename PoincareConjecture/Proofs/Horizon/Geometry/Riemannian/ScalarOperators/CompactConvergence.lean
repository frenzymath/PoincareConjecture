import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.LocalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem mvfderiv_eq_chart_fderiv {f : M → ℝ} (a : M) {x : M}
    (hx : x ∈ (extChartAt (𝓡 n) a).source)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) f x v =
      fderiv ℝ (f ∘ (extChartAt (𝓡 n) a).symm) ((extChartAt (𝓡 n) a) x)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) x v) := by
  let c := extChartAt (𝓡 n) a
  let w := mfderiv (𝓡 n) (𝓡 n) c x v
  have hi : mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w = v := by
    have he := congrArg (fun L => L v)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx)
    simpa +instances only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using! he
  have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (c.symm (c x)) := by
    simpa only [c.left_inv hx] using hf
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) a).contMDiffAt
    (extChartAt_target_mem_nhds' (c.map_source hx))).mdifferentiableAt (by simp)
  have he := mvfderiv_comp_apply (c x) hf' hc w
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv] at he
  change fderiv ℝ (f ∘ c.symm) (c x) w =
    mvfderiv (𝓡 n) f (c.symm (c x)) (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w) at he
  rw [hi, c.left_inv hx] at he
  exact he.symm

theorem eventually_uniform_value_differential_error_of_chart_jets
    (g : RiemannianMetric n M) {f : ℕ → M → ℝ} {b : M → ℝ}
    (hb : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ b)
    (hs : ∀ K : Set M, IsCompact K → ∀ᶠ k in atTop, ∀ x ∈ K,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f k) x)
    (hjet : ∀ (a : M) (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ (extChartAt (𝓡 n) a).target →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f k ∘ (extChartAt (𝓡 n) a).symm))
        (iteratedFDeriv ℝ m (b ∘ (extChartAt (𝓡 n) a).symm)) atTop K)
    (K : Set M) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, |f k x - b x| ≤ ε ∧
      ∀ v : TangentSpace (𝓡 n) x,
        |mvfderiv (𝓡 n) (f k) x v - mvfderiv (𝓡 n) b x v| ≤ ε * g.tangentNorm x v := by
  classical
  let P : Set M → Prop := fun A => ∀ᶠ k in atTop, ∀ x ∈ A,
    |f k x - b x| ≤ ε ∧ ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) (f k) x v - mvfderiv (𝓡 n) b x v| ≤ ε * g.tangentNorm x v
  change P K
  refine hK.induction_on (p := P) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (by simp)
  · intro A B hAB hB
    exact hB.mono fun k hk x hx => hk x (hAB hx)
  · intro A B hA hB
    filter_upwards [hA, hB] with k hkA hkB x hx
    exact hx.elim (hkA x) (hkB x)
  · intro a _
    obtain ⟨r, C, hr, hC, htarget, hcompact, hbound⟩ := g.exists_compact_coordinate_bounds a
    let c := extChartAt (𝓡 n) a
    let A := Metric.closedBall (c a) r
    let U := c.source ∩ c ⁻¹' Metric.ball (c a) r
    have hc : ContinuousOn c c.source := by
      simpa only [c, extChartAt_source] using
        (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := a)).continuousOn
    have hU : IsOpen U := hc.isOpen_inter_preimage
      (isOpen_extChartAt_source (I := 𝓡 n) a) Metric.isOpen_ball
    have haU : a ∈ U := ⟨mem_extChartAt_source a, Metric.mem_ball_self hr⟩
    refine ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds haU), ?_⟩
    have hv : TendstoUniformlyOn (fun k => f k ∘ c.symm) (b ∘ c.symm) atTop A := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
            (hjet a 0 A (isCompact_closedBall _ _) htarget)
    have hd : TendstoUniformlyOn (fun k => fderiv ℝ (f k ∘ c.symm))
        (fderiv ℝ (b ∘ c.symm)) atTop A := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
            (Poincare.Analysis.Calculus.tendstoUniformlyOn_fderiv_jets 0
              (hjet a 1 A (isCompact_closedBall _ _) htarget))
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv ε hε,
      Metric.tendstoUniformlyOn_iff.mp hd (ε / C) (div_pos hε hC),
      hs (c.symm '' A) hcompact] with k hkv hkd hks x hx
    have hxA : c x ∈ A := Metric.ball_subset_closedBall hx.2
    have hximage : x ∈ c.symm '' A := ⟨c x, hxA, c.left_inv hx.1⟩
    constructor
    · simpa only [Function.comp_apply, c.left_inv hx.1, Real.dist_eq, abs_sub_comm] using
        (hkv (c x) hxA).le
    · intro v
      rw [mvfderiv_eq_chart_fderiv a hx.1 (hks x hximage) v,
        mvfderiv_eq_chart_fderiv a hx.1 (hb.mdifferentiable (by simp) x) v]
      let w : EuclideanSpace ℝ (Fin n) := mfderiv (𝓡 n) (𝓡 n) c x v
      have hw : ‖w‖ ≤ C * g.tangentNorm x v := by
        have he := (hbound (c x) hxA).2
        rw [c.left_inv hx.1] at he
        exact he v
      have hdn : ‖fderiv ℝ (f k ∘ c.symm) (c x) -
          fderiv ℝ (b ∘ c.symm) (c x)‖ ≤ ε / C := by
        simpa only [dist_eq_norm, norm_sub_rev] using (hkd (c x) hxA).le
      calc
        _ = ‖(fderiv ℝ (f k ∘ c.symm) (c x) -
            fderiv ℝ (b ∘ c.symm) (c x)) w‖ := by
          simp only [sub_apply, Real.norm_eq_abs]
          rfl
        _ ≤ ‖fderiv ℝ (f k ∘ c.symm) (c x) -
            fderiv ℝ (b ∘ c.symm) (c x)‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (ε / C) * (C * g.tangentNorm x v) :=
          mul_le_mul hdn hw (norm_nonneg _) (div_nonneg hε.le hC.le)
        _ = ε * g.tangentNorm x v := by field_simp

section Product

variable {m : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

omit [IsManifold (𝓡 n) ∞ M] in
theorem mvfderiv_product_comp_vertical {e : N × ℝ → M} {f : M → ℝ}
    {y : N} {s : ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e (y, s)))
    (he : MDifferentiableAt ((𝓡 m).prod 𝓘(ℝ, ℝ)) (𝓡 n) e (y, s)) :
    deriv (fun t => f (e (y, t))) s =
      mvfderiv (𝓡 n) f (e (y, s))
        (mfderiv ((𝓡 m).prod 𝓘(ℝ, ℝ)) (𝓡 n) e (y, s) (0, 1)) := by
  have hh := mvfderiv_comp_apply (y, s) hf he (0, 1)
  have hd := mfderiv_prod_eq_add_apply (v := (0, 1)) (hf.comp (y, s) he)
  simp only [map_zero, zero_add, mfderiv_eq_fderiv] at hd
  exact hd.symm.trans hh

omit [IsManifold (𝓡 n) ∞ M] in
theorem mvfderiv_product_comp_horizontal {e : N × ℝ → M} {f : M → ℝ}
    {y : N} {s : ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e (y, s)))
    (he : MDifferentiableAt ((𝓡 m).prod 𝓘(ℝ, ℝ)) (𝓡 n) e (y, s))
    (v : TangentSpace (𝓡 m) y) :
    mvfderiv (𝓡 m) (fun z => f (e (z, s))) y v =
      mvfderiv (𝓡 n) f (e (y, s))
        (mfderiv ((𝓡 m).prod 𝓘(ℝ, ℝ)) (𝓡 n) e (y, s) (v, 0)) := by
  have hh := mvfderiv_comp_apply (y, s) hf he (v, 0)
  have hd := mfderiv_prod_eq_add_apply (I := 𝓡 m) (I' := 𝓘(ℝ, ℝ))
    (I'' := 𝓘(ℝ, ℝ)) (v := (v, 0)) (hf.comp (y, s) he)
  simp only [map_zero, add_zero] at hd
  exact hd.symm.trans hh

end Product

end PoincareConjecture.RiemannianMetric
