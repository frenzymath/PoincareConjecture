import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerPlanePoisson
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.CompletedDerivativeBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

namespace PoincareConjecture.M60

open LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "gEucl" => RiemannianMetric.euclideanMetric 2

private theorem lp_integral_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (v : Lp ℝ 2 μ) : (∫ x, v x ^ 2 ∂μ) = ‖v‖ ^ 2 := by
  simpa only [Lp.norm_def] using (eLpNorm_toReal_sq_eq_integral (Lp.memLp v)).symm





theorem suPlane_poisson_hessian :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Lp ℝ 2 (gEucl).volumeMeasure),
      ∃ (u : Plane → ℝ) (p : Fin 2 → Plane → ℝ)
        (H : Fin 2 → Fin 2 → Plane → ℝ),
        MemLp u 2 volume ∧
        (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 2))) ∧
        (∀ i, HasWeakPartialDeriv i (p i) u (Metric.ball 0 2)) ∧
        (∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 1 →
          (∫ x in Metric.ball 0 1, ∑ i : Fin 2,
            p i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
              ∫ x in Metric.ball 0 1, F x * φ x) ∧
        (∀ i k, MemLp (H i k) 2 (volume.restrict (Metric.ball 0 (1 / 2)))) ∧
        (∀ i k, HasWeakPartialDeriv k (H i k) (p i) (Metric.ball 0 (1 / 2))) ∧
        (∫ x in Metric.ball 0 (1 / 2), ∑ k : Fin 2, ∑ i : Fin 2, H i k x ^ 2) ≤
          C * ‖F‖ ^ 2 := by
  let O : Set Plane := Metric.ball 0 2
  let V : Set Plane := Metric.ball 0 1
  let W : Set Plane := Metric.ball 0 (1 / 2)
  let K : Set Plane := Metric.closedBall 0 2
  have hK : IsCompact K := isCompact_closedBall _ _
  have hOK : O ⊆ K := Metric.ball_subset_closedBall
  have hVO : V ⊆ O := Metric.ball_subset_ball (by norm_num)
  have hVK : V ⊆ K := hVO.trans hOK
  have hVc : IsCompact (closure V) := by
    simpa only [V, closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)] using
      isCompact_closedBall (0 : Plane) (1 : ℝ)
  have hWc : IsCompact (closure W) := by
    simpa only [W, closure_ball (0 : Plane) (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      isCompact_closedBall (0 : Plane) (1 / 2 : ℝ)
  have hVOc : closure V ⊆ O :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num))
  have hWV : closure W ⊆ V :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨C, hC, hH⟩ := suWeak_local_hessian_integral_le suPlaneLaplaceForm
    Metric.isOpen_ball Metric.isOpen_ball hVc hVOc (subset_univ _)
    Metric.isOpen_ball hWc hWV
  refine ⟨57 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro F
  let D := (gEucl).euclideanLeviCivitaData
  obtain ⟨w, hw, hwL, hwE⟩ := suPlane_poisson_weak D (by norm_num : (0 : ℝ) < 1) F
  change H1Zero D V at w
  let u : Plane → ℝ := toL2 D V w
  let T (i : Fin 2) := coordinateDerivative (D := D) (Ω := V)
    (OpenPartialHomeomorph.refl Plane) contMDiffOn_id contMDiffOn_id hK (subset_univ _)
    (EuclideanSpace.single i 1)
  let p : Fin 2 → Plane → ℝ := fun i => T i w
  have hu : MemLp u 2 volume := by
    simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using Lp.memLp (toL2 D V w)
  have hpK (i : Fin 2) : MemLp (p i) 2 (volume.restrict K) := Lp.memLp (T i w)
  have hpO (i : Fin 2) : MemLp (p i) 2 (volume.restrict O) :=
    (hpK i).mono_measure (Measure.restrict_mono hOK le_rfl)
  have hpV (i : Fin 2) : MemLp (p i) 2 (volume.restrict V) :=
    (hpK i).mono_measure (Measure.restrict_mono hVK le_rfl)
  have hpweak (i : Fin 2) : HasWeakPartialDeriv i (p i) u O :=
    suPlane_coordinate_weak D hK Metric.isOpen_ball hOK w i
  have hF : MemLp (F : Plane → ℝ) 2 volume := by
    simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using Lp.memLp F
  have heq (φ : Plane → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφV : tsupport φ ⊆ V) :
      (∫ x in V, ∑ i : Fin 2, p i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in V, F x * φ x :=
    suPlane_poisson_equation D hK hVK (Subset.rfl) w F hw hφ hφc hφV
  obtain ⟨H, hHm, hHw, hHb⟩ := hH (hu.restrict O) (hF.restrict V) hpO hpweak (by
    intro φ hφ hφc hφV
    simpa [suPlaneLaplaceForm, Matrix.one_apply] using heq φ hφ hφc hφV)
  have hwN : ‖w‖ ^ 2 ≤ 20 * ‖F‖ ^ 2 := by
    have h := norm_sq_le_gradientEnergy (suPlane_test_poincare D (by norm_num)) w
    norm_num at h hwE
    nlinarith
  have hpN (i : Fin 2) : ‖T i w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    have h := HarmonicCoordinates.coordinateDerivative_refl_norm_sq_le_of_ellipticity
      (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num) D (by
        intro x _ v
        change 1 * ‖v‖ ^ 2 ≤ (gEucl).inner x v v ∧
          (gEucl).inner x v v ≤ 1 * ‖v‖ ^ 2
        simp) (Subset.rfl : V ⊆ Metric.ball 0 1) hK (EuclideanSpace.single i 1) w
    simpa [T] using h
  have hpI (i : Fin 2) : (∫ x in V, p i x ^ 2) ≤ 20 * ‖F‖ ^ 2 := by
    calc
      _ ≤ ∫ x in K, p i x ^ 2 := integral_mono_measure
        (Measure.restrict_mono hVK le_rfl) (Eventually.of_forall fun x => sq_nonneg _)
        (hpK i).integrable_sq
      _ = ‖T i w‖ ^ 2 := lp_integral_sq (T i w)
      _ ≤ ‖w‖ ^ 2 := hpN i
      _ ≤ _ := hwN
  have hpsum : (∫ x in V, ∑ i : Fin 2, p i x ^ 2) ≤ 40 * ‖F‖ ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => (hpV i).integrable_sq)]
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpI i
    simp only [Fin.sum_univ_two] at h ⊢
    linarith
  have huI : (∫ x in V, u x ^ 2) ≤ 16 * ‖F‖ ^ 2 := by
    calc
      _ ≤ ∫ x, u x ^ 2 := setIntegral_le_integral hu.integrable_sq
        (Eventually.of_forall fun x => sq_nonneg _)
      _ = ‖toL2 D V w‖ ^ 2 := by
        simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using
          lp_integral_sq (toL2 D V w)
      _ ≤ _ := by
        norm_num at hwL
        have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hwL
        nlinarith
  have hFI : (∫ x in V, F x ^ 2) ≤ ‖F‖ ^ 2 := by
    calc
      _ ≤ ∫ x, F x ^ 2 := setIntegral_le_integral hF.integrable_sq
        (Eventually.of_forall fun x => sq_nonneg _)
      _ = _ := by
        simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using lp_integral_sq F
  refine ⟨u, p, H, hu, hpO, hpweak, heq, hHm, hHw, ?_⟩
  calc
    _ ≤ C * ((∫ x in V, ∑ i : Fin 2, p i x ^ 2) +
        (∫ x in V, u x ^ 2) + ∫ x in V, F x ^ 2) := hHb
    _ ≤ C * (57 * ‖F‖ ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by ring

end PoincareConjecture.M60

end
