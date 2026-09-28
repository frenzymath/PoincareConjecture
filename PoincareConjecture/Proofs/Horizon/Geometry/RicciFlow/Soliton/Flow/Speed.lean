import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurvePasting
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hasDerivAt_gradient_energy (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {γ : ℝ → M} {t : ℝ}
    (hγ : IsMIntegralCurveAt (I := 𝓡 n) γ (D.gradient f) t) :
    HasDerivAt (fun s => g.inner (γ s) (D.gradient f (γ s)) (D.gradient f (γ s)))
      (2 * D.hessian f (γ t) (D.gradient f (γ t)) (D.gradient f (γ t))) t := by
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient f x) (D.gradient f x)) :=
    g.contMDiff_inner_gradient hf hf
  have hd := (((hq (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt _
    (mvfderiv (𝓡 n) (fun x => g.inner x (D.gradient f x) (D.gradient f x))
      (γ t) ((1 : ℝ) • D.gradient f (γ t))) t at hd
  simpa only [one_smul, D.mvfderiv_gradient_normSq (hf (γ t)), Function.comp_def] using hd

theorem gradient_energy_le_exp (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ}
    (hess : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v)
    {γ : ℝ → M} {a : ℝ} (ha : 0 < a)
    (horbit : IsMIntegralCurveOn (I := 𝓡 n) γ (D.gradient f) (Ioo (-a) a))
    {t : ℝ} (ht : t ∈ Ioo (-a) a) :
    g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)) ≤
      g.inner (γ 0) (D.gradient f (γ 0)) (D.gradient f (γ 0)) *
        Real.exp (2 * C * |t|) := by
  let q : ℝ → ℝ := fun s => g.inner (γ s) (D.gradient f (γ s)) (D.gradient f (γ s))
  let q' : ℝ → ℝ := fun s =>
    2 * D.hessian f (γ s) (D.gradient f (γ s)) (D.gradient f (γ s))
  have hq (s : ℝ) : 0 ≤ q s := by
    by_cases h : D.gradient f (γ s) = 0
    · simp [q, h]
    · exact (g.pos _ _ h).le
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hmem (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : s * t ∈ Ioo (-a) a :=
    (convex_Ioo (-a) a).smul_mem_of_zero_mem h0 ht hs
  have hderiv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r => q (r * t)) (q' (s * t) * t) s := by
    simpa only [Function.comp_def, id_eq, one_mul] using
      (D.hasDerivAt_gradient_energy hf
      (horbit.isMIntegralCurveAt (isOpen_Ioo.mem_nhds (hmem s hs)))).comp s
        ((hasDerivAt_id s).mul_const t)
  have hcont : ContinuousOn (fun s => q (s * t)) (Icc (0 : ℝ) 1) :=
    fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hbound (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) :
      ‖q' (s * t) * t‖ ≤ (2 * C * |t|) * ‖q (s * t)‖ + 0 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq _), add_zero]
    calc
      |q' (s * t) * t| = 2 *
          |D.hessian f (γ (s * t)) (D.gradient f (γ (s * t)))
            (D.gradient f (γ (s * t)))| * |t| := by
        simp [q', abs_mul]
      _ ≤ 2 * (C * q (s * t)) * |t| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hess _ _) (by norm_num))
          (abs_nonneg _)
      _ = (2 * C * |t|) * q (s * t) := by ring
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s hs => (hderiv s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (δ := q 0) (K := 2 * C * |t|) (ε := 0)
    (by simp [Real.norm_eq_abs, abs_of_nonneg (hq 0)]) hbound 1 (by simp)
  simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (hq t), sub_zero,
    gronwallBound_ε0, mul_one] using h

theorem gradient_speed_le_on_bounded_interval (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hess : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v)
    {γ : ℝ → M} {a A : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (horbit : IsMIntegralCurveOn (I := 𝓡 n) γ (D.gradient f) (Ioo (-a) a))
    {t : ℝ} (ht : t ∈ Ioo (-a) a) :
    g.tangentNorm (γ t) (D.gradient f (γ t)) ≤
      g.inner (γ 0) (D.gradient f (γ 0)) (D.gradient f (γ 0)) *
        Real.exp (2 * C * A) + 1 := by
  let q : M → ℝ := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  have hq (x : M) : 0 ≤ q x := by
    by_cases h : D.gradient f x = 0
    · simp [q, h]
    · exact (g.pos _ _ h).le
  have htA : |t| ≤ A := (abs_lt.mpr ht).le.trans haA
  have henergy : q (γ t) ≤ q (γ 0) * Real.exp (2 * C * A) :=
    (D.gradient_energy_le_exp hf hess ha horbit ht).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left htA (mul_nonneg (by norm_num) hC))) (hq _))
  change Real.sqrt (q (γ t)) ≤ q (γ 0) * Real.exp (2 * C * A) + 1
  have hB : 0 ≤ q (γ 0) * Real.exp (2 * C * A) :=
    mul_nonneg (hq _) (Real.exp_pos _).le
  exact (Real.sqrt_le_iff).mpr ⟨by linarith,
    by nlinarith [sq_nonneg (q (γ 0) * Real.exp (2 * C * A))]⟩

theorem edist_le_of_bounded_hessian_gradient_curve (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hess : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v)
    {γ : ℝ → M} {a A : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-a) a))
    (horbit : IsMIntegralCurveOn (I := 𝓡 n) γ (D.gradient f) (Ioo (-a) a))
    {t : ℝ} (ht : t ∈ Ioo (-a) a) :
    g.edist (γ 0) (γ t) ≤ ENNReal.ofReal (A *
      (g.inner (γ 0) (D.gradient f (γ 0)) (D.gradient f (γ 0)) *
        Real.exp (2 * C * A) + 1)) := by
  let B := g.inner (γ 0) (D.gradient f (γ 0)) (D.gradient f (γ 0)) *
    Real.exp (2 * C * A) + 1
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hB : 0 ≤ B := (Real.sqrt_nonneg _).trans
    (D.gradient_speed_le_on_bounded_interval hf hC hess ha haA horbit h0)
  have hspeed (s : ℝ) (hs : s ∈ Ioo (-a) a) :
      g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ B := by
    rw [(horbit.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hs)).hasMFDerivAt.mfderiv]
    change g.tangentNorm (γ s) ((1 : ℝ) • D.gradient f (γ s)) ≤ B
    rw [one_smul]
    exact D.gradient_speed_le_on_bounded_interval hf hC hess ha haA horbit hs
  rcases le_total 0 t with ht0 | ht0
  · have hsub : Icc 0 t ⊆ Ioo (-a) a := fun s hs =>
      ⟨h0.1.trans_le hs.1, hs.2.trans_lt ht.2⟩
    apply (g.edist_le_of_speed_le_on_Icc isOpen_Ioo hγ ht0 hsub
      (fun s hs => hspeed s (hsub hs))).trans
    apply ENNReal.ofReal_le_ofReal
    dsimp only [B] at *
    nlinarith [ht.2.trans_le haA]
  · have hsub : Icc t 0 ⊆ Ioo (-a) a := fun s hs =>
      ⟨ht.1.trans_le hs.1, hs.2.trans_lt h0.2⟩
    have hsym : g.edist (γ 0) (γ t) = g.edist (γ t) (γ 0) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_comm
    rw [hsym]
    apply (g.edist_le_of_speed_le_on_Icc isOpen_Ioo hγ ht0 hsub
      (fun s hs => hspeed s (hsub hs))).trans
    apply ENNReal.ofReal_le_ofReal
    dsimp only [B] at *
    nlinarith [ht.1]

theorem exists_compact_confinement_of_bounded_hessian [T3Space M]
    (D : LeviCivitaData g) (hc : MetricComplete g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hess : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v) (x : M) (A : ℝ) :
    ∃ K : Set M, IsCompact K ∧ ∀ (a : ℝ), 0 < a → a ≤ A →
      ∀ (γ : ℝ → M), γ 0 = x →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-a) a) →
        IsMIntegralCurveOn (I := 𝓡 n) γ (D.gradient f) (Ioo (-a) a) →
        ∀ t ∈ Ioo (-a) a, γ t ∈ K := by
  let R := A * (g.inner x (D.gradient f x) (D.gradient f x) *
    Real.exp (2 * C * A) + 1)
  refine ⟨{y | g.edist x y ≤ ENNReal.ofReal R},
    g.isCompact_closedBall_of_metricComplete hc x R, ?_⟩
  intro a ha haA γ h0 hγ horbit t ht
  subst x
  exact D.edist_le_of_bounded_hessian_gradient_curve hf hC hess ha haA hγ horbit ht

end PoincareConjecture.LeviCivitaData
