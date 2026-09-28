import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ProductCircleObservation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeTraceSubsequence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseLift
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Def19_12_PositiveDegree

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

theorem phase_horizontal_integral
    {L : LoopPlane → ℝ} (hL : ContDiff ℝ 1 L) {d : ℝ}
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d) :
    (∫ p in S, fderiv ℝ L p e0) = d := by
  let D := fun p : LoopPlane => fderiv ℝ L p e0
  have hD : Continuous D := (hL.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDi : IntegrableOn D S volume :=
    hD.continuousOn.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hslice (s : ℝ) : (∫ x in Icc (0 : ℝ) curvePeriod, D (annulusPoint x s)) = d := by
    have hc : Continuous (fun x => D (annulusPoint x s)) := by
      apply hD.comp
      unfold annulusPoint
      fun_prop
    have hd (x : ℝ) : HasDerivAt (fun y => L (annulusPoint y s)) (D (annulusPoint x s)) x :=
      (hL.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x
        (m64AnnulusPoint_horizontal_hasDerivAt s x)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hc.intervalIntegrable 0 curvePeriod)
    have hs := hshift 0 s
    simp only [zero_add] at hs
    rw [hs] at hFTC
    have hP : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
    simpa only [intervalIntegral.integral_of_le hP, ← integral_Icc_eq_integral_Ioc,
      add_sub_cancel_left] using hFTC
  rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable D hDi]
  simp only [hslice]
  simp

theorem phase_planar_current_integral {circumference : ℝ}
    (C : M62.CircleGeometry circumference) {L : LoopPlane → ℝ}
    (hL : ContDiff ℝ 1 L) {d : ℝ}
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d) :
    (∫ p in S, planarCircleCurrent (planarCircleObservation (C.quotient (L p)))
      (fderiv ℝ (fun q => planarCircleObservation (C.quotient (L q))) p e0)) =
        (curvePeriod / circumference) * d := by
  simp_rw [planarCircleCurrent_phase_derivative C L (hL.differentiable (by simp) _) e0]
  rw [integral_const_mul, phase_horizontal_integral hL hshift]

theorem circle_map_planar_current_integral {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (f : LoopPlane → C.Point)
    (hf : ContMDiff (𝓡 2) (𝓡 1) 1 f)
    (hper : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x, C.quotient (L0 x) = f (annulusPoint x 0))
    {d : ℝ} (hshift : ∀ x, L0 (x + curvePeriod) = L0 x + d) :
    (∫ p in S, planarCircleCurrent (planarCircleObservation (f p))
      (fderiv ℝ (planarCircleObservation ∘ f) p e0)) =
        (curvePeriod / circumference) * d := by
  obtain ⟨L, hL, hquot, -, hP⟩ := m64CircleAnnulus_exists_phase C f hf hper L0 hL0 hzero hshift
  have heq : planarCircleObservation ∘ f =
      fun p => planarCircleObservation (C.quotient (L p)) :=
    funext fun p => congrArg planarCircleObservation (hquot p).symm
  have h := phase_planar_current_integral C hL hP
  change (∫ p in S, planarCircleCurrent
    ((fun q => planarCircleObservation (C.quotient (L q))) p)
      (fderiv ℝ (fun q => planarCircleObservation (C.quotient (L q))) p e0)) = _ at h
  rw [← heq] at h
  exact h

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem classical_free_ramp_current_positive
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    (sigma : M64PeriodicDegreeOneLift) (f : LoopPlane → P.charts.Point)
    (hf : ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 f)
    (hper : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = gamma (sigma.map x)) :
    ∃ degree : ℕ, 0 < degree ∧
      (∫ p in S, planarCircleCurrent (planarCircleObservation (f p).2)
        (fderiv ℝ (fun q => planarCircleObservation (f q).2) p e0)) = curvePeriod * degree ∧
      0 < ∫ p in S, planarCircleCurrent (planarCircleObservation (f p).2)
        (fderiv ℝ (fun q => planarCircleObservation (f q).2) p e0) := by
  let := P.circle.chartedSpace
  let := P.charts.chartedSpace
  obtain ⟨lift⟩ := m63PositiveDegreeLift_nonempty P gamma hperiod hgamma hramp
  let L0 := lift.lift ∘ sigma.map
  have hL0 : Continuous L0 := lift.regular.continuous.comp (degreeOneLift_continuous sigma)
  have hzero (x : ℝ) : P.circle.quotient (L0 x) = (f (annulusPoint x 0)).2 := by
    rw [hlower]
    exact lift.quotient_eq (sigma.map x)
  have hshift (x : ℝ) : L0 (x + curvePeriod) = L0 x + (lift.degree : ℝ) * circumference := by
    dsimp only [L0, Function.comp_apply]
    rw [sigma.period_shift, lift.period_shift]
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) 1
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).of_le (by simp)
  have hcurrent := circle_map_planar_current_integral P.circle (fun p => (f p).2)
    (hsnd.comp hf) (fun x s => congrArg Prod.snd (hper x s)) L0 hL0 hzero hshift
  have heq : (curvePeriod / circumference) * ((lift.degree : ℝ) * circumference) =
      curvePeriod * lift.degree := by field_simp [P.circle.positive.ne']
  rw [heq] at hcurrent
  simp only [Function.comp_def] at hcurrent
  refine ⟨lift.degree, lift.degree_positive, hcurrent, ?_⟩
  rw [hcurrent]
  exact mul_pos (by unfold curvePeriod; positivity) (by exact_mod_cast lift.degree_positive)

end PoincareConjecture.M64
