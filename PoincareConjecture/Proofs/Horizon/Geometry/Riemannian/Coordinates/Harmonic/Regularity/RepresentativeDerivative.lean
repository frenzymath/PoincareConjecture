import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateWeakDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}



theorem weak_directional_derivative_eq_fderiv_ae
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    {u U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hUs : ContDiffOn ℝ ∞ U O)
    (hU : U =ᵐ[volume.restrict O] u)
    (v : EuclideanSpace ℝ (Fin n)) (p : Lp ℝ 2 (volume.restrict O))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * fderiv ℝ φ x v) = -(∫ x in O, p x * φ x)) :
    (p : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict O]
      fun x => fderiv ℝ U x v := by
  have hd : ContinuousOn (fun x => fderiv ℝ U x v) O :=
    (hUs.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  have hp : LocallyIntegrable (p : EuclideanSpace ℝ (Fin n) → ℝ)
      (volume.restrict O) := (Lp.memLp p).locallyIntegrable (by norm_num)
  have hzero : ∀ᵐ x ∂volume.restrict O, x ∈ O →
      p x - fderiv ℝ U x v = 0 := by
    apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hp.locallyIntegrableOn O).sub (hd.locallyIntegrableOn hO.measurableSet))
    intro φ hφ hc hs
    have hφLp : MemLp φ 2 (volume.restrict O) :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hpφ : Integrable (fun x => φ x * p x) (volume.restrict O) :=
      hφLp.integrable_mul (Lp.memLp p)
    have hdφ : Integrable (fun x => φ x * fderiv ℝ U x v) volume := by
      apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
      exact (hφ.continuous.continuousOn.mul hd).continuous_of_tsupport_subset hO
        (tsupport_mul_subset_left.trans hs)
    have hleft : (∫ x in O, U x * fderiv ℝ φ x v) =
        -(∫ x in O, p x * φ x) :=
      (integral_congr_ae (hU.mul EventuallyEq.rfl)).trans (hweak φ hφ hc hs)
    have hparts := Poincare.Analysis.Elliptic.integral_mul_partial_test
      hO hUs v hφ hc hs
    have hpair : (∫ x in O, p x * φ x) =
        ∫ x in O, fderiv ℝ U x v * φ x := by linarith
    change (∫ x in O, φ x * (p x - fderiv ℝ U x v)) = 0
    simp_rw [mul_sub]
    rw [integral_sub hpφ hdφ.restrict]
    exact sub_eq_zero.mpr (by simpa only [mul_comm] using hpair)
  filter_upwards [hzero, ae_restrict_mem hO.measurableSet] with x hx hxO
  exact sub_eq_zero.mp (hx hxO)

open LeviCivitaData.Dirichlet



theorem localCoordinateDerivative_id_eq_fderiv_ae_of_volume
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} {D : LeviCivitaData g}
    {Ω K O : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hOK : O ⊆ K) (hO : IsOpen O)
    (u : H1Zero D Ω) {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hUs : ContDiffOn ℝ ∞ U O)
    (hU : U =ᵐ[volume.restrict O] (toL2 D Ω u : EuclideanSpace ℝ (Fin n) → ℝ))
    (i : Fin n) :
    (localCoordinateDerivative
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
      contMDiffOn_id contMDiffOn_id hK (by simp) hOK
      (EuclideanSpace.single i 1) u : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume.restrict O] fun x => fderiv ℝ U x (EuclideanSpace.single i 1) := by
  apply weak_directional_derivative_eq_fderiv_ae hO hUs hU
  intro φ hφ hc hs
  simpa only [OpenPartialHomeomorph.refl_apply, id_eq] using
    localCoordinateDerivative_weak
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
      contMDiffOn_id contMDiffOn_id hK (by simp) hOK hO u i hφ hc hs



theorem localCoordinateDerivative_id_eq_fderiv_ae
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} {D : LeviCivitaData g}
    {Ω K O : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hOK : O ⊆ K) (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (u : H1Zero D Ω) {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hUs : ContDiffOn ℝ ∞ U O)
    (hU : U =ᵐ[g.volumeMeasure.restrict Ω]
      (toL2 D Ω u : EuclideanSpace ℝ (Fin n) → ℝ))
    (i : Fin n) :
    (localCoordinateDerivative
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
      contMDiffOn_id contMDiffOn_id hK (by simp) hOK
      (EuclideanSpace.single i 1) u : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume.restrict O] fun x => fderiv ℝ U x (EuclideanSpace.single i 1) := by
  have hUO := ae_restrict_of_ae_restrict_of_subset hOΩ hU
  have hindicator := (ae_eq_restrict_iff_indicator_ae_eq hO.measurableSet).mp hUO
  have hcompact := g.ae_comp_on_compact
    (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
    contMDiffOn_id contMDiffOn_id hK (by simp) hindicator
  have hlocal := hcompact.filter_mono (ae_mono (Measure.restrict_mono hOK le_rfl))
  have hUvol : U =ᵐ[volume.restrict O]
      (toL2 D Ω u : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hlocal, ae_restrict_mem hO.measurableSet] with x hx hxO
    simpa only [OpenPartialHomeomorph.refl_apply, id_eq, indicator_of_mem hxO] using hx
  exact localCoordinateDerivative_id_eq_fderiv_ae_of_volume hK hOK hO u hUs hUvol i

end PoincareConjecture.HarmonicCoordinates
