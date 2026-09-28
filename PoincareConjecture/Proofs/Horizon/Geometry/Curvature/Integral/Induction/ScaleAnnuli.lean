import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleArea
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SlabNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.GeometricParameters

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

def scaleAnnularInductionConstant (m : ℕ) : ℝ :=
  max 40 (2 ^ (m + 1) * scaleSlabAreaConstant (m + 1))

theorem scaleAnnularInductionConstant_pos (m : ℕ) :
    0 < scaleAnnularInductionConstant m :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

private theorem normalized_scale_area_seed_le (n : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    modelVolume (n + 1) 1 (2 * r) / (7 * r / 12 - 55 * r / 96) *
      Real.exp (((n : ℝ) * (5 / (2 * r)) / ((1 : ℝ) / 8) ^ 2) *
        (3 * (3 * r / 5) / 2 - 55 * r / 96)) ≤
      scaleSlabAreaConstant n * r ^ n := by
  have hexp : ((n : ℝ) * (5 / (2 * r)) / ((1 : ℝ) / 8) ^ 2) *
      (3 * (3 * r / 5) / 2 - 55 * r / 96) ≤ 55 * n := by
    calc
      _ = (157 / 3 : ℝ) * n := by field_simp; ring
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

theorem exists_annular_induction_geometry_with_dimensional_constant
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          (1 : ℝ) / 2 * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    let a := 7 * r / 12
    let b := 3 * r / 5
    let α := scaleAnnularInductionConstant m
    let I := Ioo (9 * r / 16) (15 * r / 16)
    0 < a ∧ a < b ∧ 3 * b / 2 ≤ 1 ∧ 0 < α ∧
      ∃ (f : M → ℝ) (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f),
        IsProperMap (I.restrictPreimage f) ∧ Icc a (3 * b / 2) ⊆ I ∧
        (∀ x : M, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ t ∈ Icc a (3 * b / 2), g.regularLevelArea hf t ≤ α * t ^ (m + 1)) ∧
        (∀ t ∈ Icc a (3 * b / 2), ∀ x, f x = t →
          ∀ v : TangentSpace (𝓡 (m + 2)) x,
            g.inner x (D.gradient f x) v = 0 →
            D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v) ∧
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
          1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
            g.tangentNorm x (g.gradient f x) ≤ 1) ∧
        f ⁻¹' Icc a (3 * b / 2) ⊆ g.ball p (2 * r) ∧
        {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
          f ⁻¹' Icc a b := by
  let a₀ := 55 * r / 96
  let a := 7 * r / 12
  let b := 3 * r / 5
  let I := Ioo (9 * r / 16) (15 * r / 16)
  let C := modelVolume (m + 2) 1 (2 * r) / (a - a₀) *
    Real.exp ((((m + 1 : ℕ) : ℝ) * (5 / (2 * r)) / ((1 : ℝ) / 8) ^ 2) *
      (3 * b / 2 - a₀))
  let α₀ := max 1 (max (1 / ((1 : ℝ) / 8))
    (max (((5 / (2 * r)) / ((1 : ℝ) / 8)) * (3 * b / 2)) (C / a ^ (m + 1))))
  let α := scaleAnnularInductionConstant m
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha₀a : a₀ < a := by dsimp only [a₀, a]; linarith
  have hab : a < b := by dsimp only [a, b]; linarith
  have hα : 0 < α := scaleAnnularInductionConstant_pos m
  have hforty : (40 : ℝ) ≤ α := le_max_left _ _
  have hdim : 2 ^ (m + 1) * scaleSlabAreaConstant (m + 1) ≤ α := le_max_right _ _
  have hC : C ≤ scaleSlabAreaConstant (m + 1) * r ^ (m + 1) :=
    normalized_scale_area_seed_le (m + 1) hr hr1
  have hCα : C / a ^ (m + 1) ≤ α := by
    apply (div_le_iff₀ (pow_pos ha _)).mpr
    calc
      C ≤ scaleSlabAreaConstant (m + 1) * r ^ (m + 1) := hC
      _ ≤ scaleSlabAreaConstant (m + 1) * (2 * a) ^ (m + 1) := by
        apply mul_le_mul_of_nonneg_left _ (scaleSlabAreaConstant_pos _).le
        apply pow_le_pow_left₀ hr.le
        dsimp only [a]
        linarith
      _ = (2 ^ (m + 1) * scaleSlabAreaConstant (m + 1)) * a ^ (m + 1) := by
        rw [mul_pow]
        ring
      _ ≤ α * a ^ (m + 1) := mul_le_mul_of_nonneg_right hdim (pow_nonneg ha.le _)
  have hH : ((5 / (2 * r)) / ((1 : ℝ) / 8)) * (3 * b / 2) = 18 := by
    dsimp only [b]
    field_simp
    ring
  have hα₀α : α₀ ≤ α := by
    dsimp only [α₀]
    rw [hH]
    exact max_le (by linarith) (max_le (by norm_num; linarith)
      (max_le (by linarith) hCα))
  obtain ⟨f, hf, hproper, _, hband, hbounds⟩ :=
    g.exists_proper_regular_slab_with_scale_bounds D hc hsec p hr hr1 hascent
  have hnorm := D.normalized_wide_regular_slab hf hr
    (by positivity : 0 < r / 65536) (by linarith : r / 65536 < r / 128)
    (by positivity : 0 < 5 / r) p hproper hband hbounds
  dsimp only at hnorm
  have hτ : 1 / (2 * max r 1) = (1 : ℝ) / 2 := by rw [max_eq_right hr1]; norm_num
  rw [hτ] at hnorm
  obtain ⟨_, _, _, _, _, _, _, hF, hproperF, hregF, hbandF, hboundsF⟩ := hnorm
  let F := fun x => (1 : ℝ) / 2 * f x
  have hleft : (1 : ℝ) / 2 * (9 * r / 8) = 9 * r / 16 := by ring
  have hright : (1 : ℝ) / 2 * (15 * r / 8) = 15 * r / 16 := by ring
  rw [hleft, hright] at hproperF hregF hbandF
  have hinside : Icc a₀ (3 * b / 2) ⊆ I := by
    intro t ht
    change 9 * r / 16 < t ∧ t < 15 * r / 16
    dsimp only [a₀, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hsub : Icc a (3 * b / 2) ⊆ Icc a₀ (3 * b / 2) :=
    fun _ ht => ⟨ha₀a.le.trans ht.1, ht.2⟩
  have hball : F ⁻¹' Icc a₀ (3 * b / 2) ⊆ g.ball p (2 * r) := by
    intro x hx
    let := g.toMetricSpace
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm]
    exact (hbandF x (hinside hx)).2
  have hparams := D.regularLevel_annular_bounds_of_gradient_hessian_bounds
    hc hsec hF isOpen_Ioo hproperF (l := (1 : ℝ) / 8) (H := 5 / (2 * r))
    (a₀ := a₀) (a := a) (b := b) (by norm_num) (by positivity)
    ha ha₀a hab hinside (by positivity : 0 < 2 * r) p
    (fun x hx => ⟨by
      simpa only [D.gradient_eq_metric_gradient, show ((1 : ℝ) / 2) / 4 = 1 / 8 by norm_num]
        using (hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.1,
      (hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.2.1⟩)
    (fun x hx v => by
      have h := (hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.2.2 v
      convert h using 1
      ring) hball
  change 0 < α₀ ∧ _ at hparams
  obtain ⟨hα₀, harea, hhess, hspeed⟩ := hparams
  refine ⟨ha, hab, by linarith, hα, F, hF, hproperF,
    hsub.trans hinside, hregF, ?_, ?_, ?_, (preimage_mono hsub).trans hball, ?_⟩
  · intro t ht
    exact (harea t ht).trans
      (mul_le_mul_of_nonneg_right hα₀α (pow_nonneg (ha.le.trans ht.1) _))
  · intro t ht x hx v hv
    apply (hhess t ht x hx v hv).trans
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hα₀α (ha.le.trans ht.1))
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 2)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change 0 ≤ inner ℝ v v
    exact real_inner_self_nonneg
  · intro x hx
    exact ⟨(one_div_le_one_div_of_le hα₀ hα₀α).trans (hspeed x hx).1,
      (hspeed x hx).2⟩
  · intro x hx
    have hxlo : r < (g.edist p x).toReal := by linarith [hx.1]
    have hxhi : (g.edist p x).toReal < 2 * r := by linarith [hx.2]
    have happrox := abs_le.mp (hboundsF x hxlo hxhi).1
    change a ≤ F x ∧ F x ≤ b
    dsimp only [a, b, F]
    constructor <;> linarith [hx.1, hx.2]

end PoincareConjecture.RiemannianMetric
