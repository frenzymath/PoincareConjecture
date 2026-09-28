import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakDirichlet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Energy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.WeakEquation

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 12

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

def l2Forcing (D : LeviCivitaData g) (Ω : Set M) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] (H1Zero D Ω →L[ℝ] ℝ) :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ _) (toL2 D Ω)

@[simp] theorem l2Forcing_apply (f : Lp ℝ 2 g.volumeMeasure) (v : H1Zero D Ω) :
    l2Forcing D Ω f v = ⟪f, toL2 D Ω v⟫_ℝ := rfl

theorem norm_l2Forcing_apply_le (f : Lp ℝ 2 g.volumeMeasure) :
    ‖l2Forcing D Ω f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (norm_inner_le_norm f (toL2 D Ω v)).trans
    (mul_le_mul_of_nonneg_left (norm_toL2_le v) (norm_nonneg f))

def weakPoisson (D : LeviCivitaData g) (Ω : Set M) {P : ℝ}
    (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] H1Zero D Ω :=
  (weakDirichlet D Ω hP0 hP).comp (l2Forcing D Ω)

theorem weakPoisson_spec {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P)
    (f : Lp ℝ 2 g.volumeMeasure) (v : H1Zero D Ω) :
    gradientEnergy D Ω (weakPoisson D Ω hP0 hP f) v = ⟪f, toL2 D Ω v⟫_ℝ :=
  weakDirichlet_spec hP0 hP (l2Forcing D Ω f) v

theorem norm_weakPoisson_apply_le {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P)
    (f : Lp ℝ 2 g.volumeMeasure) :
    ‖weakPoisson D Ω hP0 hP f‖ ≤ (P + 1) * ‖f‖ :=
  (norm_weakDirichlet_apply_le hP0 hP _).trans
    (mul_le_mul_of_nonneg_left (norm_l2Forcing_apply_le f) (by positivity))

theorem existsUnique_weakPoisson {P : ℝ} (hP0 : 0 ≤ P)
    (hP : HasTestPoincare D Ω P) (f : Lp ℝ 2 g.volumeMeasure) :
    ∃! w : H1Zero D Ω, ∀ v : H1Zero D Ω,
      gradientEnergy D Ω w v = ⟪f, toL2 D Ω v⟫_ℝ :=
  existsUnique_weakDirichlet hP0 hP (l2Forcing D Ω f)

theorem integrable_l2_mul_laplacian (F : Lp ℝ 2 g.volumeMeasure) (f : EnergyTest D Ω) :
    Integrable (fun x ↦ F x * D.laplacian f x) g.volumeMeasure := by
  apply (L2.integrable_inner (𝕜 := ℝ) F f.laplacianLp).congr
  filter_upwards [f.laplacianLp_ae] with x hx
  change inner ℝ (F x) (f.laplacianLp x) = F x * D.laplacian f x
  rw [show f.laplacianLp x = D.laplacian f x from hx]
  simp [mul_comm]

theorem inner_laplacianLp_eq_integral (F : Lp ℝ 2 g.volumeMeasure) (f : EnergyTest D Ω) :
    ⟪F, f.laplacianLp⟫_ℝ = ∫ x, F x * D.laplacian f x ∂g.volumeMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.laplacianLp_ae] with x hx
  change inner ℝ (F x) (f.laplacianLp x) = F x * D.laplacian f x
  rw [show f.laplacianLp x = D.laplacian f x from hx]
  simp [mul_comm]

theorem testToL2_inner_laplacianLp {Ω' : Set M}
    (q : EnergyTest D Ω') (f : EnergyTest D Ω) :
    ⟪testToL2 D Ω' q, f.laplacianLp⟫_ℝ =
      ∫ x, q x * D.laplacian f x ∂g.volumeMeasure := by
  rw [inner_laplacianLp_eq_integral]
  apply integral_congr_ae
  filter_upwards [q.memLp.coeFn_toLp] with x hx
  rw [show (testToL2 D Ω' q) x = q x from hx]

theorem gradientEnergy_eq_neg_inner_laplacianLp [PreconnectedSpace M]
    (w : H1Zero D Ω) (f : EnergyTest D Ω) :
    gradientEnergy D Ω w (f : H1Zero D Ω) = -⟪toL2 D Ω w, f.laplacianLp⟫_ℝ := by
  rw [gradientEnergy_apply, inner_test_eq_inner_oneSubLaplacian, toL2_coe,
    EnergyTest.laplacianLp, inner_sub_right]
  ring

theorem weakPoisson_distributional [PreconnectedSpace M] {P : ℝ}
    (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P)
    (F : Lp ℝ 2 g.volumeMeasure) (f : EnergyTest D Ω) :
    ⟪toL2 D Ω (weakPoisson D Ω hP0 hP F), f.laplacianLp⟫_ℝ =
      -⟪F, testToL2 D Ω f⟫_ℝ := by
  have h := weakPoisson_spec hP0 hP F (f : H1Zero D Ω)
  rw [gradientEnergy_eq_neg_inner_laplacianLp, toL2_coe] at h
  linarith

def IsWeakHarmonicReplacement (q : Lp ℝ 2 g.volumeMeasure) (w : H1Zero D Ω) : Prop :=
  ∀ f : EnergyTest D Ω, ⟪q + toL2 D Ω w, f.laplacianLp⟫_ℝ = 0

theorem laplacianLp_inner_testToL2 [PreconnectedSpace M] {Ω' : Set M}
    (q : EnergyTest D Ω') (f : EnergyTest D Ω) :
    ⟪q.laplacianLp, testToL2 D Ω f⟫_ℝ =
      ⟪testToL2 D Ω' q, f.laplacianLp⟫_ℝ := by
  rw [real_inner_comm, testToL2_inner_laplacianLp, testToL2_inner_laplacianLp]
  exact D.integral_mul_laplacian_comm f.smooth q.smooth f.hasCompactSupport q.hasCompactSupport

theorem weakPoisson_isWeakHarmonicReplacement [PreconnectedSpace M] {P : ℝ}
    (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P) {Ω' : Set M}
    (q : EnergyTest D Ω') :
    IsWeakHarmonicReplacement (testToL2 D Ω' q)
      (weakPoisson D Ω hP0 hP q.laplacianLp) := by
  intro f
  rw [inner_add_left, weakPoisson_distributional, laplacianLp_inner_testToL2]
  ring

theorem existsUnique_weakHarmonicReplacement [PreconnectedSpace M] {P : ℝ}
    (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P) {Ω' : Set M}
    (q : EnergyTest D Ω') :
    ∃! w : H1Zero D Ω, IsWeakHarmonicReplacement (testToL2 D Ω' q) w := by
  refine ⟨weakPoisson D Ω hP0 hP q.laplacianLp,
    weakPoisson_isWeakHarmonicReplacement hP0 hP q, ?_⟩
  intro w hw
  apply weakDirichlet_unique_of_test hP0 hP (l2Forcing D Ω q.laplacianLp) w
  intro f
  have h := hw f
  rw [inner_add_left] at h
  rw [gradientEnergy_eq_neg_inner_laplacianLp, l2Forcing_apply, toL2_coe,
    laplacianLp_inner_testToL2]
  linarith

theorem inner_replacement_laplacianLp_eq_integral {Ω' : Set M}
    (q : EnergyTest D Ω') (w : H1Zero D Ω) (f : EnergyTest D Ω) :
    ⟪testToL2 D Ω' q + toL2 D Ω w, f.laplacianLp⟫_ℝ =
      ∫ x, (q x + (toL2 D Ω w) x) * D.laplacian f x ∂g.volumeMeasure := by
  rw [inner_laplacianLp_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (testToL2 D Ω' q) (toL2 D Ω w),
    q.memLp.coeFn_toLp] with x hadd hq
  rw [hadd, Pi.add_apply, show (testToL2 D Ω' q) x = q x from hq]

theorem integrable_replacement_mul_laplacian {Ω' : Set M}
    (q : EnergyTest D Ω') (w : H1Zero D Ω) (f : EnergyTest D Ω) :
    Integrable (fun x ↦ (q x + (toL2 D Ω w) x) * D.laplacian f x) g.volumeMeasure := by
  apply (integrable_l2_mul_laplacian (testToL2 D Ω' q + toL2 D Ω w) f).congr
  filter_upwards [Lp.coeFn_add (testToL2 D Ω' q) (toL2 D Ω w),
    q.memLp.coeFn_toLp] with x hadd hq
  rw [hadd, Pi.add_apply, show (testToL2 D Ω' q) x = q x from hq]

theorem isWeakHarmonicReplacement_iff_integral {Ω' : Set M}
    (q : EnergyTest D Ω') (w : H1Zero D Ω) :
    IsWeakHarmonicReplacement (testToL2 D Ω' q) w ↔
      ∀ f : EnergyTest D Ω,
        (∫ x, (q x + (toL2 D Ω w) x) * D.laplacian f x ∂g.volumeMeasure) = 0 := by
  unfold IsWeakHarmonicReplacement
  simp only [inner_replacement_laplacianLp_eq_integral]

end PoincareConjecture.LeviCivitaData.Dirichlet

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n]
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem existsUnique_weakPoisson_on_ball (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) (F : Lp ℝ 2 g.volumeMeasure) :
    ∃! w : H1Zero D (Metric.ball 0 R), ∀ v : H1Zero D (Metric.ball 0 R),
      gradientEnergy D (Metric.ball 0 R) w v = ⟪F, toL2 D (Metric.ball 0 R) v⟫_ℝ := by
  obtain ⟨P, hP0, hP⟩ := exists_metric_poincare_on_ball g D hR
  exact existsUnique_weakPoisson hP0 hP F

theorem existsUnique_weakHarmonicReplacement_on_ball (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    ∃! w : H1Zero D (Metric.ball 0 R),
      ∀ f : EnergyTest D (Metric.ball 0 R),
        (∫ x, (q x + (toL2 D (Metric.ball 0 R) w) x) *
          D.laplacian f x ∂g.volumeMeasure) = 0 := by
  let qtest : EnergyTest D (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    ⟨q, contMDiff_iff_contDiff.mpr hq, hqc, subset_univ _⟩
  obtain ⟨P, hP0, hP⟩ := exists_metric_poincare_on_ball g D hR
  obtain ⟨w, hw, huniq⟩ := existsUnique_weakHarmonicReplacement hP0 hP qtest
  refine ⟨w, (isWeakHarmonicReplacement_iff_integral qtest w).mp hw, ?_⟩
  intro w' hw'
  exact huniq w' ((isWeakHarmonicReplacement_iff_integral qtest w').mpr hw')

end PoincareConjecture.HarmonicCoordinates
