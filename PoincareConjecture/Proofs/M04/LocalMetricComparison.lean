import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M04.TensorNormBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set MeasureTheory

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem metric_comparison_at_of_curvature_bound {J : Set ℝ}
    (F : RicciFlow n M J) {s t K : ℝ}
    (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t) (hK : 0 ≤ K)
    (x : M)
    (hRm : ∀ τ ∈ Icc s t, (F.connection τ).curvatureTensorNorm x ≤ K)
    (v : TangentSpace (𝓡 n) x) :
    Real.exp (-2 * (n : ℝ) * K * (t - s)) *
        (F.metric s).inner x v v ≤ (F.metric t).inner x v v ∧
      (F.metric t).inner x v v ≤
        Real.exp (2 * (n : ℝ) * K * (t - s)) * (F.metric s).inner x v v := by
  let q := fun τ ↦ (F.metric τ).inner x v v
  let c := 2 * (n : ℝ) * K
  have hJI : Set.Icc s t ⊆ J := F.interval.out hs ht
  have hq0 (τ : ℝ) : 0 ≤ q τ := by
    by_cases hv : v = 0
    · simp [q, hv]
    · exact (F.metric τ).pos x v hv |>.le
  have hqD (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      HasDerivWithinAt q (-2 * (F.connection τ).ricci x v v) (Set.Icc s t) τ :=
    (F.equation τ (hJI hτ) x v v).mono hJI
  have hBound (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      -c * q τ ≤ -2 * (F.connection τ).ricci x v v ∧
        -2 * (F.connection τ).ricci x v v ≤ c * q τ := by
    have h := (abs_ricci_le_curvatureTensorNorm (F.connection τ) x v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hRm τ hτ) (Nat.cast_nonneg n)) (hq0 τ))
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK
    have h0 := mul_nonneg hnK (hq0 τ)
    obtain ⟨hl, hu⟩ := abs_le.mp h
    dsimp only [c, q] at *
    constructor <;> nlinarith
  let p := fun τ ↦ Real.exp (c * (τ - s)) * q τ
  let m := fun τ ↦ Real.exp (-(c * (τ - s))) * q τ
  have hpD (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      HasDerivWithinAt p
        (Real.exp (c * (τ - s)) * (c * q τ - 2 * (F.connection τ).ricci x v v))
        (Set.Icc s t) τ := by
    convert! ((((hasDerivAt_id τ).sub_const s).const_mul c).exp.hasDerivWithinAt.mul
      (hqD τ hτ)) using 1
    dsimp only [id, Pi.neg_apply]
    ring
  have hmD (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      HasDerivWithinAt m
        (Real.exp (-(c * (τ - s))) * (-2 * (F.connection τ).ricci x v v - c * q τ))
        (Set.Icc s t) τ := by
    convert! (((((hasDerivAt_id τ).sub_const s).const_mul c).neg.exp.hasDerivWithinAt).mul
      (hqD τ hτ)) using 1
    dsimp only [id, Pi.neg_apply]
    ring
  have hp : MonotoneOn p (Set.Icc s t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t)
      (fun τ hτ ↦ (hpD τ hτ).continuousWithinAt)
      (fun τ hτ ↦ (hpD τ (interior_subset hτ)).mono interior_subset)
    intro τ hτ
    apply mul_nonneg (Real.exp_pos _).le
    have h := (hBound τ (interior_subset hτ)).1
    linarith
  have hm : AntitoneOn m (Set.Icc s t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t)
      (fun τ hτ ↦ (hmD τ hτ).continuousWithinAt)
      (fun τ hτ ↦ (hmD τ (interior_subset hτ)).mono interior_subset)
    intro τ hτ
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have h := (hBound τ (interior_subset hτ)).2
    linarith
  have hp' : q s ≤ Real.exp (c * (t - s)) * q t := by
    simpa only [p, sub_self, mul_zero, Real.exp_zero, one_mul] using
      hp ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  have hm' : Real.exp (-(c * (t - s))) * q t ≤ q s := by
    simpa only [m, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] using
      hm ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  constructor
  · have h := mul_le_mul_of_nonneg_left hp' (Real.exp_pos (-(c * (t - s)))).le
    have he : Real.exp (-(c * (t - s))) * Real.exp (c * (t - s)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [← mul_assoc, he, one_mul] at h
    simpa only [c, q, neg_mul] using h
  · have h := mul_le_mul_of_nonneg_left hm' (Real.exp_pos (c * (t - s))).le
    have he : Real.exp (c * (t - s)) * Real.exp (-(c * (t - s))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [← mul_assoc, he, one_mul] at h
    exact h

theorem tangentNorm_comparison_at_of_curvature_bound {J : Set ℝ}
    (F : RicciFlow n M J) {s t K : ℝ}
    (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t) (hK : 0 ≤ K)
    (x : M)
    (hRm : ∀ τ ∈ Icc s t, (F.connection τ).curvatureTensorNorm x ≤ K)
    (v : TangentSpace (𝓡 n) x) :
    Real.exp (-(n : ℝ) * K * (t - s)) *
        (F.metric s).tangentNorm x v ≤ (F.metric t).tangentNorm x v ∧
      (F.metric t).tangentNorm x v ≤
        Real.exp ((n : ℝ) * K * (t - s)) * (F.metric s).tangentNorm x v := by
  have h := metric_comparison_at_of_curvature_bound F hs ht hst hK x hRm v
  have hN (g : RiemannianMetric n M) : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
  have hsq (g : RiemannianMetric n M) :
      (g.tangentNorm x v) ^ 2 = g.inner x v v := by
    apply Real.sq_sqrt
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hlow :
      (Real.exp (-(n : ℝ) * K * (t - s)) * (F.metric s).tangentNorm x v) ^ 2 ≤
        ((F.metric t).tangentNorm x v) ^ 2 := by
    calc
      _ = Real.exp (-2 * (n : ℝ) * K * (t - s)) * (F.metric s).inner x v v := by
        rw [mul_pow, hsq, pow_two, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by simpa only [hsq] using h.1
  have hupp :
      ((F.metric t).tangentNorm x v) ^ 2 ≤
        (Real.exp ((n : ℝ) * K * (t - s)) * (F.metric s).tangentNorm x v) ^ 2 := by
    calc
      _ ≤ Real.exp (2 * (n : ℝ) * K * (t - s)) * (F.metric s).inner x v v := by
        simpa only [hsq] using h.2
      _ = _ := by
        rw [mul_pow, hsq, pow_two, ← Real.exp_add]
        congr 2
        ring
  have hlow0 := mul_nonneg (Real.exp_pos (-(n : ℝ) * K * (t - s))).le (hN (F.metric s))
  have hupp0 := mul_nonneg (Real.exp_pos ((n : ℝ) * K * (t - s))).le (hN (F.metric s))
  constructor <;> nlinarith only [hlow, hupp, hlow0, hupp0, hN (F.metric t)]

theorem tangentNorm_comparison_on_initial_ball
    {T K α r : ℝ} (F : RicciFlow n M (Icc 0 T))
    (hK : 0 < K) (hT0 : 0 ≤ T) (hT : T ≤ α / K) (p : M)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    {x : M} (hx : x ∈ (F.metric 0).ball p r)
    (v : TangentSpace (𝓡 n) x) :
    (F.metric 0).tangentNorm x v ≤
        Real.exp ((n : ℝ) * α) * (F.metric t).tangentNorm x v ∧
      (F.metric t).tangentNorm x v ≤
        Real.exp ((n : ℝ) * α) * (F.metric 0).tangentNorm x v := by
  have h := tangentNorm_comparison_at_of_curvature_bound F ⟨le_rfl, hT0⟩ ht ht.1 hK.le x
    (fun τ hτ => hRm τ ⟨hτ.1, hτ.2.trans ht.2⟩ x hx) v
  simp only [sub_zero] at h
  have hKt : K * t ≤ α := by
    have hTK : T * K ≤ α := (le_div_iff₀ hK).mp hT
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hK.le]
  have hexp : Real.exp ((n : ℝ) * K * t) ≤ Real.exp ((n : ℝ) * α) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hKt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hN (g : RiemannianMetric n M) : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
  constructor
  · have hrev := mul_le_mul_of_nonneg_left h.1 (Real.exp_pos ((n : ℝ) * K * t)).le
    have he : Real.exp ((n : ℝ) * K * t) * Real.exp (-(n : ℝ) * K * t) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1; congr 1; ring
    rw [← mul_assoc, he, one_mul] at hrev
    exact hrev.trans (mul_le_mul_of_nonneg_right hexp (hN (F.metric t)))
  · exact h.2.trans (mul_le_mul_of_nonneg_right hexp (hN (F.metric 0)))

private theorem pathELength_eq_lintegral_tangentNorm
    (g : RiemannianMetric n M) (γ : ℝ → M) (a b : ℝ) :
    g.pathELength γ a b =
      ∫⁻ u in Icc a b,
        ENNReal.ofReal (g.tangentNorm (γ u)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) γ a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro u _
  dsimp only
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

theorem pathELength_le_of_tangentNorm_le
    (g h : RiemannianMetric n M) {U : Set M} {C a b : ℝ}
    (hC : 0 ≤ C)
    (hcomp : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm x v)
    (γ : ℝ → M) (hU : MapsTo γ (Icc a b) U) :
    g.pathELength γ a b ≤ ENNReal.ofReal C * h.pathELength γ a b := by
  rw [pathELength_eq_lintegral_tangentNorm, pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro u hu
  calc
    _ ≤ ENNReal.ofReal (C * h.tangentNorm (γ u)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1)) :=
      ENNReal.ofReal_le_ofReal (hcomp _ (hU hu) _)
    _ = _ := ENNReal.ofReal_mul hC

private theorem metric_edist_le_pathELength
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hab : a ≤ b) :
    g.edist (γ a) (γ b) ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

private theorem metric_edist_triangle
    (g : RiemannianMetric n M) (x y z : M) :
    g.edist x z ≤ g.edist x y + g.edist y z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

private theorem exists_contMDiff_path_length_lt
    (g : RiemannianMetric n M) {x y : M} {L : ℝ≥0∞}
    (hxy : g.edist x y < L) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ ∧ g.pathELength γ 0 1 < L := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hL, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hxy zero_lt_one
  exact ⟨γ, h0, h1, hγ, hL⟩

private theorem continuous_metric_edist [T2Space M]
    (g : RiemannianMetric n M) (p : M) :
    Continuous (fun x => g.edist p x) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  exact continuous_const.edist continuous_id

theorem initial_half_ball_closure_subset_initial_ball [T2Space M]
    (g : RiemannianMetric n M) (p : M) {r : ℝ} (hr : 0 < r) :
    closure (g.ball p (r / 2)) ⊆ g.ball p r := by
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  have hcont : Continuous (fun y => g.edist p y) :=
    continuous_const.edist continuous_id
  have hclosed : IsClosed {y | g.edist p y ≤ ENNReal.ofReal (r / 2)} := by
    exact isClosed_le hcont continuous_const
  have hhalf : g.ball p (r / 2) ⊆ {y | g.edist p y ≤ ENNReal.ofReal (r / 2)} := by
    intro y hy
    change g.edist p y < ENNReal.ofReal (r / 2) at hy
    exact le_of_lt hy
  have hcl : closure (g.ball p (r / 2)) ⊆
      {y | g.edist p y ≤ ENNReal.ofReal (r / 2)} :=
    closure_minimal hhalf hclosed
  intro y hy
  change g.edist p y < ENNReal.ofReal r
  exact (hcl hy).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hr).2 (by linarith))

end PoincareConjecture.M04
