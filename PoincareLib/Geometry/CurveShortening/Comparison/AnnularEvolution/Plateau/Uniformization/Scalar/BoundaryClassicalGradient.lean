import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.HalfSpaceGradient
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.Regularity.RepresentativeDerivative
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.ClassicalGradient
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Actual classical boundary derivatives from half-space H3 data

The continuous weak gradients supplied by H3 agree with the classical
interior differential by uniqueness of distributions. On a convex chart
region, the derivative-limit theorem then extends this actual derivative
to its closed boundary. No classical-gradient premise is assumed.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareMT.M64Uniformization

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => Set.preimage (fun p : Plane => p 0) (Ioi (0 : ℝ))

/-- A smooth interior representative of compactly supported half-space H3 data has a genuine
continuous extension of its classical differential on every open subregion of the
half-space. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project
construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalar_halfSpace_H3_classical_gradient
    {u U : Plane → ℝ} (hc : HasCompactSupport u) (hu : MemWkp 3 2 u Half)
    {O : Set Plane} (hO : IsOpen O) (hOH : O ⊆ Half)
    (hUs : ContDiffOn ℝ ∞ U O) (hU : U =ᵐ[volume.restrict O] u) :
    ∃ J : Plane → Plane →L[ℝ] ℝ, Continuous J ∧ EqOn (fderiv ℝ U) J O := by
  obtain ⟨G, hGc, hG⟩ := scalar_halfSpace_H3_continuous_gradient hc hu
  have hpart (i : Fin 2) : EqOn
      (fun x => fderiv ℝ U x (EuclideanSpace.single i 1)) (G i) O := by
    let v := chosenWeakPartial' 2 i u Half
    have hv : MemLp v 2 (volume.restrict O) :=
      (chosenWeakPartial'_memLp_of_mem hu.memW1p i).mono_measure
        (Measure.restrict_mono hOH le_rfl)
    let p : Lp ℝ 2 (volume.restrict O) := hv.toLp v
    have hp : (p : Plane → ℝ) =ᵐ[volume.restrict O] v := hv.coeFn_toLp
    have hw : HasWeakPartialDeriv i v u O :=
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i).restrict hO hOH
    have hpd : (p : Plane → ℝ) =ᵐ[volume.restrict O]
        fun x => fderiv ℝ U x (EuclideanSpace.single i 1) := by
      apply HarmonicCoordinates.weak_directional_derivative_eq_fderiv_ae hO hUs hU
      intro phi hphi hphic hphis
      calc
        _ = -(∫ x in O, v x * phi x) := hw phi hphi hphic hphis
        _ = -(∫ x in O, p x * phi x) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hp] with x hx
          rw [hx]
    have hpg : (p : Plane → ℝ) =ᵐ[volume.restrict O] G i :=
      hp.trans (ae_restrict_of_ae_restrict_of_subset hOH (hG i))
    apply Measure.eqOn_open_of_ae_eq (hpd.symm.trans hpg) hO
      ((hUs.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const)
      (hGc i).continuousOn
  let J : Plane → Plane →L[ℝ] ℝ := fun x => M60.suPlaneColumns (fun i => G i x)
  have hJ : Continuous J := by
    have h (i : Fin 2) :=
      (ContinuousLinearMap.smulRightL ℝ Plane ℝ (EuclideanSpace.proj i)).continuous.comp (hGc i)
    exact (h 0).add (h 1)
  refine ⟨J, hJ, ?_⟩
  intro x hx
  rw [← M60.suPlaneColumns_reconstruct (fderiv ℝ U x)]
  apply congrArg M60.suPlaneColumns
  funext i
  exact hpart i hx

/-- H3 supplies the actual classical derivative through a convex chart boundary whenever the
representative has its already-established continuous trace. The derivative is obtained from
the actual weak H3 data. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the
project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalar_halfSpace_H3_boundary_derivative
    {u U : Plane → ℝ} (hc : HasCompactSupport u) (hu : MemWkp 3 2 u Half)
    {O : Set Plane} (hO : IsOpen O) (hconv : Convex ℝ O) (hOH : O ⊆ Half)
    (hUs : ContDiffOn ℝ ∞ U O) (hU : U =ᵐ[volume.restrict O] u)
    (hUc : ContinuousOn U (closure O)) :
    ∃ J : Plane → Plane →L[ℝ] ℝ, Continuous J ∧
      EqOn (fderiv ℝ U) J O ∧
      ∀ x, HasFDerivWithinAt U (J x) (closure O) x := by
  obtain ⟨J, hJ, hUJ⟩ := scalar_halfSpace_H3_classical_gradient hc hu hO hOH hUs hU
  refine ⟨J, hJ, hUJ, ?_⟩
  intro x
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (hUs.differentiableOn (by simp)) hconv hO
    (fun y hy => (hUc y hy).mono subset_closure)
  apply ((hJ.continuousAt (x := x)).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hUJ hy).symm

end PoincareMT.M64Uniformization
