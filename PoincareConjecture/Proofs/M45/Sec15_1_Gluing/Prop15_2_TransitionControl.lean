import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_TransitionJets
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_VanishingOperations
import PoincareConjecture.Proofs.M45.Sec15_1_GluingSupport.NativeJetConvergence
import PoincareConjecture.Proofs.M45.Ch9_Models.EvolvingCylinderQuadratic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

open SpacetimeBounds CoordinateTransition

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance transitionControlCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance transitionControlCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

variable {ι : Type*} {l : Filter ι}

theorem bounded_first_transition_derivative
    {A C : ι → E → MetricCoefficient 3} {phi : ι → E → E} {r s : ι → ℝ}
    (hE : PointJetsVanish (fun i p => A i p - M44.evolvingCylinderModelField (s i) p)
      (fun _ => 0) l)
    (hH : PointJetsVanish (fun i p => C i p - M44.evolvingCylinderModelField 0 p)
      (fun _ => 0) l)
    (hs : ∀ i, s i ∈ Icc (-1 : ℝ) 0) (hr : ∀ i, 1 ≤ r i)
    (hphi : ∀ i, phi i 0 = 0)
    (hmetric : ∀ i, ∀ v w : E, A i 0 v w = r i *
      C i (phi i 0) (fderiv ℝ (phi i) 0 v) (fderiv ℝ (phi i) 0 w)) :
    l.IsBoundedUnder (· ≤ ·) (fun i => ‖fderiv ℝ (phi i) 0‖) := by
  have hEn : Tendsto (fun i => ‖A i 0 - M44.evolvingCylinderModelField (s i) 0‖)
      l (𝓝 0) := by simpa only [norm_zero] using hE.values.norm
  have hHn : Tendsto (fun i => ‖C i 0 - M44.evolvingCylinderModelField 0 0‖)
      l (𝓝 0) := by simpa only [norm_zero] using hH.values.norm
  refine ⟨3, ?_⟩
  change ∀ᶠ i in l, ‖fderiv ℝ (phi i) 0‖ ≤ 3
  filter_upwards [hEn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hHn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hiA hiC
  have hAb := model_evolvingCylinder_perturbed_quadratic_bounds (hs i) (A i 0) hiA.le
  have hCb := model_evolvingCylinder_perturbed_quadratic_bounds
    (show (0 : ℝ) ∈ Icc (-1) 0 by norm_num) (C i 0) hiC.le
  have h := norm_le_of_pullback_quadratic_bounds (A i 0) (r i • C i 0)
    (fderiv ℝ (phi i) 0) (a := 1 / 2) (C := 9 / 2)
    (by norm_num) (by norm_num) (fun v => (hAb v).2) (fun v => ?_)
    (fun v w => ?_)
  · norm_num at h ⊢
    have hsqrt : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simpa only [hsqrt] using h
  · change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ r i * C i 0 v v
    have hc := (hCb v).1
    have hc0 : 0 ≤ C i 0 v v := le_trans (by positivity) hc
    nlinarith only [hc, hr i, mul_nonneg (sub_nonneg.mpr (hr i)) hc0]
  · simpa only [hphi i, smul_apply, smul_eq_mul] using (hmetric i v w).symm

theorem bounded_transition_jets_of_metric_convergence
    {A C : ι → E → MetricCoefficient 3} {A0 C0 : E → MetricCoefficient 3}
    {phi : ι → E → E} {U V : ι → Set E}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hx : ∀ i, (0 : E) ∈ U i) (hy : ∀ i, (0 : E) ∈ V i)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (U i))
    (hC : ∀ i, ContDiffOn ℝ ∞ (C i) (V i))
    (hAi : ∀ i y, y ∈ U i → (A i y).IsInvertible)
    (hCi : ∀ i y, y ∈ V i → (C i y).IsInvertible)
    (hCsym : ∀ i y, y ∈ V i → ∀ v w, C i y v w = C i y w v)
    (hphi : ∀ i, ContDiffOn ℝ ∞ (phi i) (U i))
    (hmap : ∀ i, MapsTo (phi i) (U i) (V i)) (hzero : ∀ i, phi i 0 = 0)
    (hmetric : ∀ i y, y ∈ U i → ∀ v w,
      A i y v w = C i (phi i y) (fderiv ℝ (phi i) y v) (fderiv ℝ (phi i) y w))
    (hAj : PointJetsConverge A (fun _ => 0) A0 0 l)
    (hCj : PointJetsConverge C (fun _ => 0) C0 0 l)
    (hA0 : ContDiffAt ℝ ∞ A0 0) (hC0 : ContDiffAt ℝ ∞ C0 0)
    (hA0i : (A0 0).IsInvertible) (hC0i : (C0 0).IsInvertible)
    (hfirst : l.IsBoundedUnder (· ≤ ·) (fun i => ‖fderiv ℝ (phi i) 0‖)) :
    ∀ m, FinitePointJetBounded m phi (fun _ => 0) l := by
  have hAs (i : ι) := (hA i).contDiffAt ((hU i).mem_nhds (hx i))
  have hCs (i : ι) := (hC i).contDiffAt ((hV i).mem_nhds (hy i))
  have hphs (i : ι) := (hphi i).contDiffAt ((hU i).mem_nhds (hx i))
  have hGA := hAj.christoffel hAs hA0 (fun i => hAi i 0 (hx i)) hA0i
  have hGC := hCj.christoffel hCs hC0 (fun i => hCi i 0 (hy i)) hC0i
  apply finitePointJetBounded_of_christoffel_hessian hphs
    (fun i => CoordinateExponential.contDiffAt_christoffelBilinear
      (hAs i) (hAi i 0 (hx i)))
    (fun i => by
      rw [hzero i]
      exact CoordinateExponential.contDiffAt_christoffelBilinear (hCs i) (hCi i 0 (hy i)))
    (fun m => hGA.finite_bound m)
    (fun m => by simpa only [hzero] using hGC.finite_bound m)
    (show l.IsBoundedUnder (· ≤ ·) (fun i => ‖phi i 0‖) from by
      refine ⟨0, ?_⟩
      change ∀ᶠ i in l, ‖phi i 0‖ ≤ 0
      exact Filter.Eventually.of_forall (fun i => by rw [hzero i, norm_zero]))
    hfirst
  intro i
  filter_upwards [(hU i).mem_nhds (hx i)] with y hyU
  exact fderiv_fderiv_eq_transitionHessianPolynomial_on
    (hU i) (hV i) (hA i) (hC i) (hAi i) (hCi i) (hCsym i) (hphi i) (hmap i)
    (fun p hp => surjective_of_pullback_isInvertible (hAi i p hp) (hmetric i p hp))
    (hmetric i) hyU

end PoincareConjecture.M45
