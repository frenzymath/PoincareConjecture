import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Minimization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.EnergyBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension










noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 12

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ}



theorem exists_coordinate_cutoffs_energy {R : ℝ} (hR : 0 < R) :
    ∃ q : Fin n → EuclideanSpace ℝ (Fin n) → ℝ, ∃ E : ℝ, 0 ≤ E ∧
      ∀ i : Fin n, ContDiff ℝ ∞ (q i) ∧ HasCompactSupport (q i) ∧
        tsupport (q i) ⊆ Metric.ball 0 R ∧
        (∀ x ∈ Metric.ball 0 (R / 2), q i x = x i) ∧
        Integrable (fun x => ‖fderiv ℝ (q i) x‖ ^ 2) volume ∧
        (∫ x, ‖fderiv ℝ (q i) x‖ ^ 2) ≤ E := by
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  let q : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x => χ x * x i
  have hq (i : Fin n) : ContDiff ℝ ∞ (q i) :=
    χ.contDiff.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hqc (i : Fin n) : HasCompactSupport (q i) := χ.hasCompactSupport.mul_right
  have hqs (i : Fin n) : tsupport (q i) ⊆ Metric.ball 0 R := by
    calc
      tsupport (q i) ⊆ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
        tsupport_mul_subset_left
      _ = Metric.closedBall 0 (3 * R / 4) := χ.tsupport_eq
      _ ⊆ Metric.ball 0 R := Metric.closedBall_subset_ball (by linarith)
  have hqi (i : Fin n) : Integrable (fun x => ‖fderiv ℝ (q i) x‖ ^ 2) volume :=
    (((hq i).fderiv_right (m := ∞) (by simp)).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (by
        simpa only [pow_two] using
          (((hqc i).fderiv ℝ).norm.mul_right :
            HasCompactSupport (fun x => ‖fderiv ℝ (q i) x‖ * ‖fderiv ℝ (q i) x‖)))
  have hEn (i : Fin n) : 0 ≤ ∫ x, ‖fderiv ℝ (q i) x‖ ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  refine ⟨q, ∑ i, ∫ x, ‖fderiv ℝ (q i) x‖ ^ 2,
    Finset.sum_nonneg (fun i _ => hEn i), fun i => ⟨hq i, hqc i, hqs i, ?_, hqi i, ?_⟩⟩
  · intro x hx
    have hχ : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp only [q, hχ, one_mul]
  · exact Finset.single_le_sum (fun j _ => hEn j) (Finset.mem_univ i)



theorem exists_uniform_weakHarmonicCoordinate_energy [NeZero n]
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ i : Fin n, ∃ w : H1Zero D (Metric.ball 0 (R / 2)),
          (∀ f : EnergyTest D (Metric.ball 0 (R / 2)),
            (∫ x, (x i + (toL2 D (Metric.ball 0 (R / 2)) w) x) *
              D.laplacian f x ∂g.volumeMeasure) = 0) ∧
          gradientEnergy D (Metric.ball 0 (R / 2)) w w ≤ C ∧
          ‖w‖ ^ 2 ≤ (Real.sqrt (b ^ n) * R ^ 2 * b / Real.sqrt (a ^ n) + 1) * C := by
  obtain ⟨q, E, hE, hq⟩ := exists_coordinate_cutoffs_energy (n := n) hR
  refine ⟨(Real.sqrt (b ^ n) / a) * E, by positivity, ?_⟩
  intro g D hell i
  have hRhalf : 0 < R / 2 := by positivity
  have hballs : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  let P := Real.sqrt (b ^ n) * R ^ 2 * b / Real.sqrt (a ^ n)
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hP : HasTestPoincare D (Metric.ball 0 (R / 2)) P := by
    have htwice : 2 * (R / 2) = R := by ring
    simpa only [htwice] using
      metric_poincare_of_ellipticity D hRhalf ha hb (fun x hx => hell x (hballs hx))
  obtain ⟨hqsmooth, hqc, hqs, hqeq, _, hqE⟩ := hq i
  let qtest : EnergyTest D (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    ⟨q i, contMDiff_iff_contDiff.mpr hqsmooth, hqc, subset_univ _⟩
  let w := weakPoisson D (Metric.ball 0 (R / 2)) hP0 hP qtest.laplacianLp
  have hweak : ∀ f : EnergyTest D (Metric.ball 0 (R / 2)),
      (∫ x, (q i x + (toL2 D (Metric.ball 0 (R / 2)) w) x) *
        D.laplacian f x ∂g.volumeMeasure) = 0 :=
    (isWeakHarmonicReplacement_iff_integral qtest w).mp
      (weakPoisson_isWeakHarmonicReplacement hP0 hP qtest)
  have henergy : gradientEnergy D (Metric.ball 0 (R / 2)) w w ≤
      (Real.sqrt (b ^ n) / a) * E := by
    calc
      _ ≤ ∫ x, g.inner x (D.gradient (q i) x) (D.gradient (q i) x) ∂g.volumeMeasure :=
        weakPoisson_gradientEnergy_le (subset_univ _) hP0 hP qtest
      _ ≤ (Real.sqrt (b ^ n) / a) * ∫ x, ‖fderiv ℝ (q i) x‖ ^ 2 :=
        integral_gradient_le_of_ellipticity D ha hell hqsmooth hqc hqs
      _ ≤ (Real.sqrt (b ^ n) / a) * E :=
        mul_le_mul_of_nonneg_left hqE (by positivity)
  refine ⟨w, ?_, henergy, ?_⟩
  · intro f
    calc
      _ = ∫ x, (q i x + (toL2 D (Metric.ball 0 (R / 2)) w) x) *
          D.laplacian f x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Metric.ball 0 (R / 2)
        · rw [hqeq x hx]
        · have hz := D.laplacian_eq_zero_of_notMem_tsupport
            (f := (f : EuclideanSpace ℝ (Fin n) → ℝ))
            (fun ht => hx (f.support_subset ht))
          simp only [hz, mul_zero]
      _ = 0 := hweak f
  · exact (norm_sq_le_gradientEnergy hP w).trans
      (mul_le_mul_of_nonneg_left henergy (by positivity))

end PoincareConjecture.HarmonicCoordinates
