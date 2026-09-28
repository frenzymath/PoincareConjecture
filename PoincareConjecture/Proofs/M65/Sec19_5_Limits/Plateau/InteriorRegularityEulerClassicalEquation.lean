import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerClassical
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.HessianTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Manifold

namespace PoincareConjecture.M65Euler

private theorem compact_test_mul_integrable {U : Set LoopPlane}
    {f : LoopPlane → ℝ} (hf : ContinuousOn f U)
    (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    IntegrableOn (fun z => φ z * f z) U := by
  have hI : Integrable (fun z => φ z * f z) := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left _ _).trans (subset_tsupport φ))).mp
    exact (φ.continuous.continuousOn.mul (hf.mono hs)).integrableOn_compact hc
  exact hI.integrableOn

private theorem coordinate_column_derivative {N : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin N)} {x : LoopPlane}
    (hu : ContDiffAt ℝ ∞ u x) (v w : LoopPlane) (k : Fin N) :
    fderiv ℝ (fun z => (fderiv ℝ u z v) k) x w =
      (fderiv ℝ (fderiv ℝ u) x w v) k := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hc := hd.clm_apply (differentiableAt_const v)
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x hc.hasFDerivAt
  have hproj : fderiv ℝ (fun z => (fderiv ℝ u z v) k) x w =
      (fderiv ℝ (fun z => fderiv ℝ u z v) x w) k :=
    congrArg (fun L => L w) hp.fderiv
  rw [hproj, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

set_option maxHeartbeats 1800000 in

theorem classical_harmonic_of_weak {N : ℕ}
    {g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))} (D : LeviCivitaData g)
    {U : Set LoopPlane} (hU : IsOpen U)
    (u : LoopPlane → EuclideanSpace ℝ (Fin N)) (hu : ContDiffOn ℝ ∞ u U)
    (hweak : ∀ (k : Fin N) (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, ∑ i : Fin 2, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) *
        (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)) k) =
      ∫ z in U, φ z * ∑ i : Fin 2, (M65Gauss.connectionCoefficient D (u z)
        (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))) k)
    {x : LoopPlane} (hx : x ∈ U) :
    (∑ i : Fin 2, M65Gauss.covariantHessianMap D u x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let W (i : Fin 2) (z : LoopPlane) := fderiv ℝ u z (b i)
  have hW (i : Fin 2) : ContDiffOn ℝ ∞ (W i) U :=
    (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  let Γ (i : Fin 2) (z : LoopPlane) := M65Gauss.connectionCoefficient D (u z) (W i z) (W i z)
  have hcoeff : ContinuousOn (fun z => M65Gauss.connectionCoefficient D (u z)) U :=
    (M65Gauss.contDiff_connectionCoefficient D).continuous.comp_continuousOn hu.continuousOn
  have hΓ (i : Fin 2) : ContinuousOn (Γ i) U :=
    (hcoeff.clm_apply (hW i).continuousOn).clm_apply (hW i).continuousOn
  ext k
  let row (i : Fin 2) (z : LoopPlane) := W i z k
  have hrow (i : Fin 2) : ContDiffOn ℝ ∞ (row i) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn (hW i)
  let Q (z : LoopPlane) := ∑ i : Fin 2, (fderiv ℝ (row i) z (b i) + Γ i z k)
  have hQ : ContinuousOn Q U := by
    apply continuousOn_finsetSum
    intro i _
    exact ((hrow i).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const |>.add
      ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn (hΓ i))
  have hAE : ∀ᵐ z ∂volume, z ∈ U → Q z = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hQ.locallyIntegrableOn hU.measurableSet)
    intro test htest hc hs
    let φ : 𝓢(LoopPlane, ℝ) := hc.toSchwartzMap htest
    have hI (i : Fin 2) := classical_scalar_weak_identity hU
      ((hrow i).of_le (by simp)) φ hc hs (b i)
    have hGI (i : Fin 2) : IntegrableOn (fun z => φ z * Γ i z k) U :=
      compact_test_mul_integrable
        ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn (hΓ i)) φ hc hs
    have hsumG : (∑ i : Fin 2, ∫ z in U, row i z * fderiv ℝ φ z (b i)) =
        ∑ i : Fin 2, ∫ z in U, φ z * Γ i z k := by
      rw [← integral_finsetSum _ fun i _ => (hI i).2.1,
        ← integral_finsetSum _ fun i _ => hGI i]
      calc
        _ = ∫ z in U, ∑ i : Fin 2, fderiv ℝ φ z (b i) * row i z := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = ∫ z in U, φ z * ∑ i : Fin 2, Γ i z k := hweak k φ hc hs
        _ = _ := by simp only [Finset.mul_sum]
    have hpoint : (fun z => test z • Q z) = fun z =>
        ∑ i : Fin 2, (fderiv ℝ (row i) z (b i) * φ z + φ z * Γ i z k) := by
      funext z
      simp only [Q, smul_eq_mul, Finset.mul_sum, mul_add]
      apply Finset.sum_congr rfl
      intro i _
      change test z * fderiv ℝ (row i) z (b i) + test z * Γ i z k =
        fderiv ℝ (row i) z (b i) * test z + test z * Γ i z k
      ring
    have hterm (i : Fin 2) :
        (∫ z in U, fderiv ℝ (row i) z (b i) * φ z + φ z * Γ i z k) =
          -(∫ z in U, row i z * fderiv ℝ φ z (b i)) + ∫ z in U, φ z * Γ i z k := by
      rw [integral_add (hI i).1 (hGI i), (hI i).2.2]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
      (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hs hm)), zero_smul])]
    have hTI (i : Fin 2) : IntegrableOn
        (fun z => fderiv ℝ (row i) z (b i) * φ z + φ z * Γ i z k) U :=
      (hI i).1.add (hGI i)
    rw [hpoint, integral_finsetSum _ fun i _ => hTI i]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsumG, neg_add_cancel]
  have hz : Q x = 0 := Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' hU.measurableSet).mpr hAE) hU hQ continuousOn_const hx
  have hux : ContDiffAt ℝ ∞ u x := (hu x hx).contDiffAt (hU.mem_nhds hx)
  have hQeq : Q x = (∑ i : Fin 2, M65Gauss.covariantHessianMap D u x (b i) (b i)) k := by
    change Q x = (EuclideanSpace.proj k)
      (∑ i : Fin 2, M65Gauss.covariantHessianMap D u x (b i) (b i))
    rw [map_sum]
    simp only [Q]
    apply Finset.sum_congr rfl
    intro i _
    rw [show fderiv ℝ (row i) x (b i) = (fderiv ℝ (fderiv ℝ u) x (b i) (b i)) k from
      coordinate_column_derivative hux (b i) (b i) k]
    rfl
  exact hQeq.symm.trans hz

end PoincareConjecture.M65Euler
