import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeChartCorrection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeCircleEnergy
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64_corrected_curve_speed_le
    (g : RiemannianMetric n M) (T : E → M) (w : ℝ → E) {B : ℝ} (x : ℝ)
    (hT : MDifferentiableAt (𝓡 m) (𝓡 n) T (w x))
    (hw : DifferentiableAt ℝ w x)
    (hbound : ∀ v : E, g.tangentNorm (T (w x))
      (mfderiv (𝓡 m) (𝓡 n) T (w x) v) ≤ B * ‖v‖) :
    g.tangentNorm (T (w x)) (curveVelocity (T ∘ w) x) ≤ B * ‖deriv w x‖ := by
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 m) w x 1 = deriv w x := by
    simpa +instances only [mfderiv_eq_fderiv] using!
      (fderiv_apply_one_eq_deriv : fderiv ℝ w x 1 = deriv w x)
  unfold curveVelocity
  erw [mfderiv_comp_apply x hT hw.mdifferentiableAt (1 : ℝ), hd]
  exact hbound _

theorem m64_periodic_approximation_eventually_in_ball
    (w : ℕ → ℝ → E) (u : ℝ → E)
    (hperiod : ∀ j, Function.Periodic (w j) curvePeriod)
    (hlim : TendstoUniformlyOn w u atTop (Icc (0 : ℝ) curvePeriod))
    (c : E) {r : ℝ} (hr : 0 < r)
    (hu : ∀ x ∈ Icc (0 : ℝ) curvePeriod, dist (u x) c < r / 2) :
    ∃ k : ℕ, ∀ j ≥ k, ∀ x : ℝ, w j x ∈ closedBall c r := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hlim) (r / 2) (half_pos hr))
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  refine ⟨k, fun j hj x => ?_⟩
  let y := toIcoMod hP 0 x
  have hy : y ∈ Icc (0 : ℝ) curvePeriod :=
    Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)
  have heq : w j y = w j x := by
    simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
      ((hperiod j).zsmul (-toIcoDiv hP 0 x)) x
  rw [← heq]
  apply mem_closedBall.mpr
  have hdist := hk j hj y hy
  have htriangle := dist_triangle (w j y) (u y) c
  rw [dist_comm (w j y) (u y)] at htriangle
  linarith [hu y hy]

theorem m64ChartReadable_local_circle_approximation_uniform
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M)
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (U : Set M) (B : ℝ), IsOpen U ∧ p ∈ U ∧ 0 ≤ B ∧
      ∀ (gamma : ℝ → M), Function.Periodic gamma curvePeriod → (∀ x, gamma x ∈ U) →
        ∀ (w : ℕ → ℝ → E), (∀ j, ContDiff ℝ 1 (w j)) →
          (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∃ (k : ℕ) (f : ℕ → ℝ → M),
            (∀ j, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (f j)) ∧
            (∀ j, Function.Periodic (f j) curvePeriod) ∧
            (∀ x, Tendsto (fun j => f j x) atTop (𝓝 (gamma x))) ∧
            (∀ j x, f j x ∈ O) ∧
            TendstoUniformlyOn (fun j => e ∘ f j) (e ∘ gamma) atTop
              (Icc (0 : ℝ) curvePeriod) ∧
            ∀ j x, g.tangentNorm (f j x) (curveVelocity (f j) x) ≤
              B * ‖deriv (w (j + k)) x‖ := by
  obtain ⟨U, r, B, T, hU, hp, hr, hB, hfix, hmap, hT, hbound⟩ :=
    m64ChartReadable_local_correction_into g e he hread p O hO hpO
  refine ⟨U, B, hU, hp, hB, ?_⟩
  intro gamma hgammaP hgammaU w hw hwP hlim
  obtain ⟨k, hk⟩ := m64_periodic_approximation_eventually_in_ball w (e ∘ gamma) hwP
    hlim (e p) hr (fun x _ => (hfix _ (hgammaU x)).2)
  let f : ℕ → ℝ → M := fun j => T ∘ w (j + k)
  have hmem (j : ℕ) (x : ℝ) : w (j + k) x ∈ closedBall (e p) r :=
    hk _ (Nat.le_add_left k j) x
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hpoint (x : ℝ) : Tendsto (fun j => w j x) atTop (𝓝 (e (gamma x))) := by
    let y := toIcoMod hP 0 x
    have hy : y ∈ Icc (0 : ℝ) curvePeriod :=
      Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)
    have hwxy (j : ℕ) : w j y = w j x := by
      simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
        ((hwP j).zsmul (-toIcoDiv hP 0 x)) x
    have hgxy : gamma y = gamma x := by
      simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
        (hgammaP.zsmul (-toIcoDiv hP 0 x)) x
    simpa only [Function.comp_apply, hwxy, hgxy] using hlim.tendsto_at hy
  refine ⟨k, f, ?_, ?_, ?_, fun j x => hmap (hmem j x), ?_, ?_⟩
  · intro j x
    exact (hT _ (hmem j x)).comp x (hw (j + k)).contMDiff.contMDiffAt
  · intro j x
    change T (w (j + k) (x + curvePeriod)) = T (w (j + k) x)
    rw [hwP (j + k) x]
  · intro x
    have hinside : e (gamma x) ∈ closedBall (e p) r := by
      exact mem_closedBall.mpr ((hfix _ (hgammaU x)).2.le.trans (by linarith))
    have ht := ((hT _ hinside).continuousAt.tendsto).comp
      ((hpoint x).comp (tendsto_add_atTop_nat k))
    change Tendsto (fun j => T (w (j + k) x)) atTop (𝓝 (T (e (gamma x)))) at ht
    rw [(hfix _ (hgammaU x)).1] at ht
    exact ht
  · have htc : ContinuousOn (e ∘ T) (closedBall (e p) r) := fun y hy =>
      (he.continuous.continuousAt.comp (hT y hy).continuousAt).continuousWithinAt
    have huni := (isCompact_closedBall (e p) r).uniformContinuousOn_of_continuous htc
    have htail : TendstoUniformlyOn (fun j => w (j + k)) (e ∘ gamma) atTop
        (Icc (0 : ℝ) curvePeriod) := fun V hV =>
      (tendsto_add_atTop_nat k).eventually (hlim V hV)
    have hinside (x : ℝ) (_ : x ∈ Icc (0 : ℝ) curvePeriod) :
        e (gamma x) ∈ closedBall (e p) r :=
      mem_closedBall.mpr ((hfix _ (hgammaU x)).2.le.trans (by linarith))
    have hresult := huni.comp_tendstoUniformlyOn_eventually
      (Eventually.of_forall fun j x _ => hmem j x) hinside htail
    have hfixg (x : ℝ) : T (e (gamma x)) = gamma x := (hfix _ (hgammaU x)).1
    simpa only [f, Function.comp_def, hfixg] using hresult
  · intro j x
    exact m64_corrected_curve_speed_le g T (w (j + k)) x
      ((hT _ (hmem j x)).mdifferentiableAt one_ne_zero)
      ((hw (j + k)).differentiable (by simp) x) (hbound _ (hmem j x))

theorem m64ChartReadable_local_circle_approximation
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M)
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (U : Set M) (B : ℝ), IsOpen U ∧ p ∈ U ∧ 0 ≤ B ∧
      ∀ (gamma : ℝ → M), Function.Periodic gamma curvePeriod → (∀ x, gamma x ∈ U) →
        ∀ (w : ℕ → ℝ → E), (∀ j, ContDiff ℝ 1 (w j)) →
          (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∃ (k : ℕ) (f : ℕ → ℝ → M),
            (∀ j, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (f j)) ∧
            (∀ j, Function.Periodic (f j) curvePeriod) ∧
            (∀ x, Tendsto (fun j => f j x) atTop (𝓝 (gamma x))) ∧
            (∀ j x, f j x ∈ O) ∧
            ∀ j x, g.tangentNorm (f j x) (curveVelocity (f j) x) ≤
              B * ‖deriv (w (j + k)) x‖ := by
  obtain ⟨U, B, hU, hp, hB, happ⟩ :=
    m64ChartReadable_local_circle_approximation_uniform g e he hread p O hO hpO
  refine ⟨U, B, hU, hp, hB, ?_⟩
  intro gamma hP hU w hw hwP hlim
  obtain ⟨k, f, hf, hfP, hpoint, hO, -, hspeed⟩ := happ gamma hP hU w hw hwP hlim
  exact ⟨k, f, hf, hfP, hpoint, hO, hspeed⟩

end PoincareConjecture
