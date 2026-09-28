import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleAnnuli

noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture.RiemannianMetric

private theorem quarter_gradient_scale_area_seed_le (n : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    modelVolume (n + 1) 1 (2 * r) / (7 * r / 12 - 55 * r / 96) *
      Real.exp (((n : ℝ) * (5 / r) / ((1 : ℝ) / 4) ^ 2) *
        (3 * (3 * r / 5) / 2 - 55 * r / 96)) ≤
      scaleSlabAreaConstant n * r ^ n := by
  have hexp : ((n : ℝ) * (5 / r) / ((1 : ℝ) / 4) ^ 2) *
      (3 * (3 * r / 5) / 2 - 55 * r / 96) ≤ 55 * n := by
    calc
      _ = (157 / 6 : ℝ) * n := by field_simp; ring
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hexp' : ((n : ℝ) * (5 / r) / ((1 : ℝ) / 4) ^ 2) *
      (11 * r / 6 - 55 * r / 48) = 55 * n := by field_simp; ring
  have hseed : modelVolume (n + 1) 1 (2 * r) / (7 * r / 12 - 55 * r / 96) =
      2 * modelVolume (n + 1) 1 (2 * r) / (7 * r / 6 - 55 * r / 48) := by
    field_simp
    ring
  calc
    _ ≤ modelVolume (n + 1) 1 (2 * r) / (7 * r / 12 - 55 * r / 96) *
        Real.exp (55 * n) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
      exact div_nonneg (modelVolume_nonneg _ zero_le_one (by positivity)) (by linarith)
    _ ≤ _ := by
      rw [hseed, ← hexp']
      exact scaleSlabArea_seed_le n hr hr1

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

theorem regularLevel_annular_bounds_with_dimensional_constant_of_quarter_gradient
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    {g : RiemannianMetric (m + 2) M} (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m + 2)) x),
      -1 ≤ D.sectionalCurvature x v w)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    (p : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hproper : IsProperMap ((Ioo (9 * r / 16) (15 * r / 16)).restrictPreimage f))
    (hspeed : ∀ x : M, f x ∈ Ioo (9 * r / 16) (15 * r / 16) →
      (1 / 4 : ℝ) ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1)
    (hhess : ∀ x : M, f x ∈ Ioo (9 * r / 16) (15 * r / 16) →
      ∀ v : TangentSpace (𝓡 (m + 2)) x,
        D.hessian f x v v ≤ (5 / r) * g.inner x v v)
    (hball : f ⁻¹' Icc (55 * r / 96) (9 * r / 10) ⊆ g.ball p (2 * r)) :
    let α := RiemannianMetric.scaleAnnularInductionConstant m
    (∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
      g.regularLevelArea hf t ≤ α * t ^ (m + 1)) ∧
    (∀ t ∈ Icc (7 * r / 12) (9 * r / 10), ∀ x, f x = t →
      ∀ v : TangentSpace (𝓡 (m + 2)) x,
        g.inner x (D.gradient f x) v = 0 →
        D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v) ∧
    ∀ x ∈ f ⁻¹' Icc (7 * r / 12) (9 * r / 10),
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1 := by
  let a₀ := 55 * r / 96
  let a := 7 * r / 12
  let b := 3 * r / 5
  let I := Ioo (9 * r / 16) (15 * r / 16)
  let C := RiemannianMetric.modelVolume (m + 2) 1 (2 * r) / (a - a₀) *
    Real.exp ((((m + 1 : ℕ) : ℝ) * (5 / r) / ((1 : ℝ) / 4) ^ 2) * (3 * b / 2 - a₀))
  let α₀ := max 1 (max (1 / ((1 : ℝ) / 4))
    (max (((5 / r) / ((1 : ℝ) / 4)) * (3 * b / 2)) (C / a ^ (m + 1))))
  let α := RiemannianMetric.scaleAnnularInductionConstant m
  have ha : 0 < a := by dsimp [a]; positivity
  have ha₀a : a₀ < a := by dsimp [a₀, a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hα : 0 < α := RiemannianMetric.scaleAnnularInductionConstant_pos m
  have hforty : (40 : ℝ) ≤ α := le_max_left _ _
  have hdim : 2 ^ (m + 1) * RiemannianMetric.scaleSlabAreaConstant (m + 1) ≤ α :=
    le_max_right _ _
  have hC : C ≤ RiemannianMetric.scaleSlabAreaConstant (m + 1) * r ^ (m + 1) :=
    RiemannianMetric.quarter_gradient_scale_area_seed_le (m + 1) hr hr1
  have hCα : C / a ^ (m + 1) ≤ α := by
    apply (div_le_iff₀ (pow_pos ha _)).mpr
    calc
      C ≤ RiemannianMetric.scaleSlabAreaConstant (m + 1) * r ^ (m + 1) := hC
      _ ≤ RiemannianMetric.scaleSlabAreaConstant (m + 1) * (2 * a) ^ (m + 1) := by
        apply mul_le_mul_of_nonneg_left _ (RiemannianMetric.scaleSlabAreaConstant_pos _).le
        apply pow_le_pow_left₀ hr.le
        dsimp [a]
        linarith
      _ = (2 ^ (m + 1) * RiemannianMetric.scaleSlabAreaConstant (m + 1)) * a ^ (m + 1) := by
        rw [mul_pow]
        ring
      _ ≤ α * a ^ (m + 1) := mul_le_mul_of_nonneg_right hdim (pow_nonneg ha.le _)
  have hH : ((5 / r) / ((1 : ℝ) / 4)) * (3 * b / 2) = 18 := by
    dsimp [b]
    field_simp
    ring
  have hα₀α : α₀ ≤ α := by
    dsimp [α₀]
    rw [hH]
    exact max_le (by linarith) (max_le (by norm_num; linarith)
      (max_le (by linarith) hCα))
  have hinside : Icc a₀ (3 * b / 2) ⊆ I := by
    intro t ht
    change 9 * r / 16 < t ∧ t < 15 * r / 16
    dsimp [a₀, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have heq : 3 * b / 2 = 9 * r / 10 := by dsimp [b]; ring
  have hparams := D.regularLevel_annular_bounds_of_gradient_hessian_bounds
    hc hsec hf isOpen_Ioo hproper (l := (1 : ℝ) / 4) (H := 5 / r)
    (by norm_num) (by positivity) ha ha₀a hab hinside
    (by positivity : 0 < 2 * r) p
    (fun x hx => by simpa only [D.gradient_eq_metric_gradient] using hspeed x hx)
    hhess (by simpa only [heq] using hball)
  change 0 < α₀ ∧ _ at hparams
  obtain ⟨hα₀, harea, hhess', hspeed'⟩ := hparams
  dsimp only
  rw [← heq]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (harea t ht).trans
      (mul_le_mul_of_nonneg_right hα₀α (pow_nonneg (ha.le.trans ht.1) _))
  · intro t ht x hx v hv
    apply (hhess' t ht x hx v hv).trans
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hα₀α (ha.le.trans ht.1))
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 2)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change 0 ≤ inner ℝ v v
    exact real_inner_self_nonneg
  · intro x hx
    exact ⟨(one_div_le_one_div_of_le hα₀ hα₀α).trans (hspeed' x hx).1,
      (hspeed' x hx).2⟩

end PoincareConjecture.LeviCivitaData
