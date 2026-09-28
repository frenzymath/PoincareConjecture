import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsWarping
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicWarpingBounds
import PoincareConjecture.Proofs.M35.RawFlow.InitialDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35.Uniqueness

private theorem scalar_ode_jet_bounds {A : Type*} {f K : A → ℝ → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hK : ∀ a, ContDiff ℝ ∞ (K a))
    (hKbounds : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r →
      |iteratedDeriv j (K a) r| ≤ C)
    (hf0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r → |f a r| ≤ C)
    (hf1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r → |deriv (f a) r| ≤ C)
    (hode : ∀ a r, 0 ≤ r → deriv (deriv (f a)) r = -(K a r * f a r)) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r → |iteratedDeriv j (f a) r| ≤ C := by
  classical
  choose B hB0 hB using hKbounds
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      rcases j with _ | _ | k
      · simpa only [iteratedDeriv_zero] using hf0
      · simpa only [zero_add, iteratedDeriv_one] using hf1
      · have hU : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            (i < k + 2 → ∀ a r, 0 ≤ r → |iteratedDeriv i (f a) r| ≤ C) := by
          intro i
          by_cases hi : i < k + 2
          · obtain ⟨C, hC, hCb⟩ := ih i hi
            exact ⟨C, hC, fun _ => hCb⟩
          · exact ⟨0, le_rfl, fun h => (hi h).elim⟩
        choose U hU0 hUb using hU
        let C := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * U (k - i)
        have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hU0 _))
        have hpos (a : A) (r : ℝ) (hr : 0 < r) :
            |iteratedDeriv (k + 2) (f a) r| ≤ C := by
          have heq : deriv (deriv (f a)) =ᶠ[𝓝 r] fun s => -(K a s * f a s) := by
            filter_upwards [eventually_gt_nhds hr] with s hs
            exact hode a s hs.le
          have hjet := Filter.EventuallyEq.iteratedDeriv_eq k heq
          have hrec : iteratedDeriv (k + 2) (f a) r =
              -iteratedDeriv k (fun s => K a s * f a s) r := by
            simpa only [iteratedDeriv_succ', iteratedDeriv_fun_neg] using hjet
          rw [hrec, abs_neg]
          have hmul := norm_iteratedFDeriv_mul_le (hK a) (hf a) r
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
          simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hmul
          apply hmul.trans
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hB i a r hr.le) (Nat.cast_nonneg _))
            (hUb (k - i) (by omega) a r hr.le) (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
        refine ⟨C, hC, ?_⟩
        intro a r hr
        have hcont := (hf a).continuous_iteratedDeriv (k + 2)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl (k + 2))
        have hclosed : IsClosed {s : ℝ | |iteratedDeriv (k + 2) (f a) s| ≤ C} :=
          isClosed_le hcont.abs continuous_const
        exact closure_minimal (s := Ioi (0 : ℝ)) (fun s hs => hpos a s hs)
          hclosed (by rwa [closure_Ioi])

theorem raw_intrinsic_warping_jets_bounded_on_slab
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
            (G.flow.metric t).inner x u v) :
    ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t (ht : t ∈ Icc 0 T), ∀ r ≥ 0,
      |iteratedDeriv j (intrinsicWarpingRadius (G.flow.metric t)
        (hrotation t ⟨ht.1, ht.2.trans_lt hTlt⟩)
        (G.complete P ⟨ht.1, ht.2.trans_lt hTlt⟩)) r| ≤ C := by
  let A := ↥(Icc (0 : ℝ) T)
  have htime (a : A) : a.1 ∈ Ico 0 G.lifetime := ⟨a.2.1, a.2.2.trans_lt hTlt⟩
  let f (a : A) := intrinsicWarpingRadius (G.flow.metric a.1)
    (hrotation a.1 (htime a)) (G.complete P (htime a))
  let K (a : A) := intrinsicCurvatureJet (G.flow.metric a.1)
    (hrotation a.1 (htime a)) (G.complete P (htime a)) (G.flow.connection a.1) 0
  have hf (a : A) : ContDiff ℝ ∞ (f a) :=
    intrinsicWarpingRadius_contDiff _ _ _
  have hKs (a : A) : ContDiff ℝ ∞ (K a) := intrinsicCurvatureJet_contDiff _ _ _ _ 0
  have hKb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r →
      |iteratedDeriv j (K a) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ := raw_curvature_derivatives_bounded_on_slab P H G hT hTlt j
    refine ⟨C, hC.le, fun a r hr => ?_⟩
    exact intrinsicCurvatureJet_iteratedDeriv_bound _ _ _ _ j (hCb a.1 a.2) hr
  have hscalar : 0 < H.scalar_constant := H.scalar_constant_pos
  have hf0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r → |f a r| ≤ C := by
    refine ⟨2 * H.scalar_constant + 1, by positivity, ?_⟩
    intro a r hr
    rcases hr.eq_or_lt with rfl | hr
    · simp only [f, intrinsicWarpingRadius_zero, abs_zero]
      positivity
    · have hcontrols := raw_intrinsic_warping_controls P H G (htime a)
        (hrotation a.1 (htime a)) r hr
      change 0 < f a r ∧ f a r ^ 2 ≤ 2 * H.scalar_constant ∧ _ at hcontrols
      rw [abs_of_pos hcontrols.1]
      nlinarith only [hcontrols.2.1, sq_nonneg (f a r - 1)]
  have hf1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 0 ≤ r → |deriv (f a) r| ≤ C := by
    refine ⟨1, zero_le_one, ?_⟩
    intro a r hr
    rcases hr.eq_or_lt with rfl | hr
    · rw [show deriv (f a) 0 = 1 from (intrinsicWarpingRadius_hasDerivAt_zero _ _ _).deriv]
      norm_num
    · have hcontrols := raw_intrinsic_warping_controls P H G (htime a)
        (hrotation a.1 (htime a)) r hr
      exact (abs_of_nonneg hcontrols.2.2.1).le.trans hcontrols.2.2.2.1
  have hode (a : A) (r : ℝ) (hr : 0 ≤ r) : deriv (deriv (f a)) r = -(K a r * f a r) :=
    intrinsicWarpingRadius_second_eq_curvature _ _ _ _ hr
  intro j
  obtain ⟨C, hC, hCb⟩ := scalar_ode_jet_bounds hf hKs hKb hf0 hf1 hode j
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht r hr
  exact (hCb ⟨t, ht⟩ r hr).trans (by linarith)

end PoincareConjecture.M35.Uniqueness
