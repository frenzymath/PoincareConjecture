import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.AreaGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.ModelBounds










noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric



def scaleSlabAreaConstant (n : ℕ) : ℝ :=
  96 * euclideanUnitBallVolume (n + 1) * 2 ^ (n + 1) * Real.exp (57 * (n : ℝ))

theorem scaleSlabAreaConstant_pos (n : ℕ) : 0 < scaleSlabAreaConstant n := by
  unfold scaleSlabAreaConstant
  positivity [euclideanUnitBallVolume_pos (n + 1)]

private theorem modelVolume_two_mul_le (n : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    modelVolume (n + 1) 1 (2 * r) ≤
      euclideanUnitBallVolume (n + 1) * 2 ^ (n + 1) *
        Real.exp (2 * (n : ℝ)) * r ^ (n + 1) := by
  have h := modelVolume_le_exp_mul_zero (n := n + 1) (κ := 1)
    zero_le_one (by positivity : 0 ≤ 2 * r)
  rw [modelVolume_zero_curvature (by omega : 1 ≤ n + 1)] at h
  simp only [Nat.add_sub_cancel, Real.sqrt_one, one_mul] at h
  calc
    _ ≤ euclideanUnitBallVolume (n + 1) * (2 * r) ^ (n + 1) *
        Real.exp ((n : ℝ) * (2 * r)) := h
    _ ≤ euclideanUnitBallVolume (n + 1) * (2 * r) ^ (n + 1) *
        Real.exp (2 * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
      exact mul_nonneg (euclideanUnitBallVolume_nonneg _) (pow_nonneg (by positivity) _)
    _ = _ := by rw [mul_pow]; ring


theorem scaleSlabArea_seed_le (n : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    2 * modelVolume (n + 1) 1 (2 * r) / (7 * r / 6 - 55 * r / 48) *
        Real.exp (((n : ℝ) * (5 / r) / ((1 : ℝ) / 4) ^ 2) *
          (11 * r / 6 - 55 * r / 48)) ≤ scaleSlabAreaConstant n * r ^ n := by
  have hexponent : ((n : ℝ) * (5 / r) / ((1 : ℝ) / 4) ^ 2) *
      (11 * r / 6 - 55 * r / 48) = 55 * n := by
    field_simp
    ring
  have hseed : 2 * modelVolume (n + 1) 1 (2 * r) /
      (7 * r / 6 - 55 * r / 48) = 96 * modelVolume (n + 1) 1 (2 * r) / r := by
    field_simp
    ring
  rw [hexponent, hseed]
  calc
    _ ≤ 96 * (euclideanUnitBallVolume (n + 1) * 2 ^ (n + 1) *
        Real.exp (2 * (n : ℝ)) * r ^ (n + 1)) / r * Real.exp (55 * n) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (modelVolume_two_mul_le n hr hr1) (by norm_num)) hr.le)
        (Real.exp_pos _).le
    _ = _ := by
      unfold scaleSlabAreaConstant
      rw [show (57 : ℝ) * n = 2 * n + 55 * n by ring, Real.exp_add, pow_succ]
      field_simp
      ring


private theorem regularLevelArea_le_scaleSlabAreaConstant
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : RiemannianMetric (n + 1) M} (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 (n + 1)) x,
      -1 ≤ D.sectionalCurvature x v w)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hproper : IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f))
    (p : M)
    (hspeed : ∀ x : M, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
      (1 : ℝ) / 4 ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 2)
    (hhess : ∀ x : M, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
      ∀ v : TangentSpace (𝓡 (n + 1)) x,
        D.hessian f x v v ≤ (5 / r) * g.inner x v v)
    (hball : f ⁻¹' Ioo (9 * r / 8) (15 * r / 8) ⊆ g.ball p (2 * r)) :
    ∀ t ∈ Icc (7 * r / 6) (11 * r / 6),
      g.regularLevelArea hf t ≤ scaleSlabAreaConstant n * t ^ n := by
  have hinside : Icc (55 * r / 48) (11 * r / 6) ⊆
      Ioo (9 * r / 8) (15 * r / 8) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have harea := D.regularLevelArea_le_of_gradient_hessian_bounds hc hsec hf
    isOpen_Ioo hproper (l := (1 : ℝ) / 4) (L := 2) (H := 5 / r)
    (a := 55 * r / 48) (d := 7 * r / 6) (b := 11 * r / 6)
    (by norm_num) (by norm_num) (by positivity)
    (by linarith) (by linarith) hinside (by positivity : 0 < 2 * r) p
    hspeed hhess (fun x hx => hball (hinside hx))
  intro t ht
  exact (harea t ht).trans ((scaleSlabArea_seed_le n hr hr1).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.le (by linarith [ht.1]) n)
      (scaleSlabAreaConstant_pos n).le))



theorem exists_proper_regular_slab_with_dimensional_area_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (n + 1) M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 (n + 1)) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          (1 : ℝ) / 2 * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    ∃ (f : M → ℝ) (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f),
      IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f) ∧
      (∀ x : M, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
        mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      (∀ x : M, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |f x - (g.edist p x).toReal| ≤ r / 65536 ∧
        (1 : ℝ) / 4 ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 2 ∧
        ∀ v : TangentSpace (𝓡 (n + 1)) x,
          D.hessian f x v v ≤ (5 / r) * g.inner x v v) ∧
      ∀ t ∈ Icc (7 * r / 6) (11 * r / 6),
        g.regularLevelArea hf t ≤
          PoincareConjecture.RiemannianMetric.scaleSlabAreaConstant n * t ^ n := by
  obtain ⟨f, hf, hproper, hreg, hband, hbounds⟩ :=
    g.exists_proper_regular_slab_with_scale_bounds D hc hsec p hr hr1 hascent
  refine ⟨f, hf, hproper, hreg, hband, hbounds, ?_⟩
  apply regularLevelArea_le_scaleSlabAreaConstant D hc hsec hf hr hr1 hproper p
  · intro x hx
    exact ⟨(hbounds x (hband x hx).1 (hband x hx).2).2.1,
      (hbounds x (hband x hx).1 (hband x hx).2).2.2.1⟩
  · intro x hx
    exact (hbounds x (hband x hx).1 (hband x hx).2).2.2.2
  · intro x hx
    let := g.toMetricSpace
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm]
    exact (hband x hx).2

end PoincareConjecture.RiemannianMetric
