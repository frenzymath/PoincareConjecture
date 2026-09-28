import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerClassicalEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerHarmonic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65Euler

set_option maxHeartbeats 1800000 in

theorem weak_chart_classical_harmonic
    {gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (DE : LeviCivitaData gE)
    (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin 3) => y) (ball x (8 * R)))
    (hX : ContDiffOn ℝ ∞ X.value (ball x (8 * R)))
    (hweak : ∀ (k : Fin 3) (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ →
      tsupport φ ⊆ ball x R →
      (∫ z in closedBall x (2 * R), ∑ i : Fin 2,
        fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (X.derivative i z) k) =
        ∫ z in closedBall x (2 * R), φ z * ∑ i : Fin 2,
          (M65Gauss.connectionCoefficient DE (X.value z)
            (X.derivative i z) (X.derivative i z)) k) :
    (∑ i : Fin 2, M65Gauss.covariantHessianMap DE X.value x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  have h28 : closedBall x (2 * R) ⊆ ball x (8 * R) :=
    closedBall_subset_ball (by linarith)
  have h18 : ball x R ⊆ ball x (8 * R) := ball_subset_ball (by linarith)
  have h12 : ball x R ⊆ closedBall x (2 * R) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hD (i : Fin 2) :
      (fun z => fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        =ᵐ[volume.restrict (closedBall x (2 * R))] X.derivative i := by
    apply ae_restrict_of_ae_restrict_of_subset h28
    exact classical_derivative_eq_weak isOpen_ball X X.value
      (hX.of_le (by simp)) Filter.EventuallyEq.rfl i
  apply classical_harmonic_of_weak DE isOpen_ball X.value (hX.mono h18) _ (mem_ball_self hR)
  intro k φ hc hs
  let L (z : LoopPlane) := ∑ i : Fin 2,
    fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) *
      (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i)) k
  let Q (z : LoopPlane) := φ z * ∑ i : Fin 2,
    (M65Gauss.connectionCoefficient DE (X.value z)
      (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i))) k
  have hL0 (z : LoopPlane) (hz : z ∉ ball x R) : L z = 0 := by
    simp only [L, fderiv_of_notMem_tsupport ℝ (fun hm => hz (hs hm)),
      zero_apply, zero_mul, Finset.sum_const_zero]
  have hQ0 (z : LoopPlane) (hz : z ∉ ball x R) : Q z = 0 := by
    simp only [Q, image_eq_zero_of_notMem_tsupport (fun hm => hz (hs hm)), zero_mul]
  change (∫ z in ball x R, L z) = ∫ z in ball x R, Q z
  have hLc : (∫ z in ball x R, L z) = ∫ z in closedBall x (2 * R), L z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hL0,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hL0 z (fun hm => hz (h12 hm)))]
  have hQc : (∫ z in ball x R, Q z) = ∫ z in closedBall x (2 * R), Q z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hQ0,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hQ0 z (fun hm => hz (h12 hm)))]
  rw [hLc, hQc]
  calc
    _ = ∫ z in closedBall x (2 * R), ∑ i : Fin 2,
        fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (X.derivative i z) k := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hD] with z hz
      simp only [L, hz]
    _ = ∫ z in closedBall x (2 * R), φ z * ∑ i : Fin 2,
        (M65Gauss.connectionCoefficient DE (X.value z)
          (X.derivative i z) (X.derivative i z)) k := hweak k φ hc hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hD] with z hz
      simp only [Q, hz]

theorem minimum_representative_harmonic {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (heinj : Function.Injective e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    {U : Set LoopPlane} (hU : IsOpen U) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) (q : LoopPlane → M)
    (hqs : ContMDiffOn (𝓡 2) (𝓡 3) ∞ q U)
    (hq : q =ᵐ[volume.restrict U] F.value) {x : LoopPlane} (hx : x ∈ U) :
    m65PlaneTension D q x = 0 := by
  obtain ⟨R, ε, hR, hε, hRU, gE, DE, X, hX, _hXc, hsource, _hcap,
    hmetric, _hfields, hweak⟩ :=
    exists_weak_harmonic_chart g e he heinj hinj hU F hmin q hqs.continuousOn hq hx
  have hXinf : ContDiffOn ℝ ∞ X.value (ball x (8 * R)) := by
    have hh := (contMDiffOn_extChartAt (I := 𝓡 3) (x := q x)).comp
      (hqs.mono (ball_subset_closedBall.trans hRU))
      (fun z hz => by simpa only [mem_preimage, extChartAt_source] using hsource z hz)
    exact hh.contDiffOn.congr (fun z _ => hX z)
  have hzero := weak_chart_classical_harmonic DE x hR X hXinf
    (fun k φ hc hs => (hweak k φ hc hs).2)
  let c := chartAt (EuclideanSpace ℝ (Fin 3)) (q x)
  have hXeq : X.value = c ∘ q := by
    funext z
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp,
      Function.comp_apply, id_eq, c] using hX z
  have hmetric' : ∀ᶠ y in 𝓝 (c (q x)), ∀ a b : EuclideanSpace ℝ (Fin 3),
      gE.inner y a b = g.inner (c.symm y)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y a) (mfderiv (𝓡 3) (𝓡 3) c.symm y b) := by
    have hh := mem_of_superset (ball_mem_nhds _ hε) (fun y hy => (hmetric y hy).2)
    simpa +instances only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, id_eq, c] using! hh
  have hsum : m65PlaneTension D q x = mfderiv (𝓡 3) (𝓡 3) c.symm (c (q x))
      (∑ i : Fin 2, M65Gauss.covariantHessianMap DE X.value x
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
    rw [map_sum, m65PlaneTension_eq_hessianTrace]
    apply Finset.sum_congr rfl
    intro i _
    rw [hXeq]
    exact M65Gauss.planeHessian_chart D DE (q x) hU hqs hx
      (mem_chart_source _ _) hmetric' _ _
  rw [hsum, hzero, map_zero]

end PoincareConjecture.M65Euler
