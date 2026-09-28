import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Operator
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.FluxIdentity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem divergence_testFlux_eq_laplacian
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {z : Spacetime n} (hz : z ∈ domain J e) :
    (∑ i, Canonical.spatialDeriv i
      (fun y => ∑ j, weightedPrincipal F e i j y * Canonical.spatialDeriv j φ y) z) =
    density F e z *
      (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1) := by
  have hA (i j) : DifferentiableAt ℝ (weightedPrincipal F e i j) z :=
    ((contDiffOn_weightedPrincipal F e he hei i j).contDiffAt
      ((isOpen_domain e).mem_nhds hz)).differentiableAt (by simp)
  have hDs (j) : ContDiff ℝ ∞ (Canonical.spatialDeriv j φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hD (j) : DifferentiableAt ℝ (Canonical.spatialDeriv j φ) z :=
    (hDs j).differentiable (by simp) z
  have hder (i) : Canonical.spatialDeriv i
      (fun y => ∑ j, weightedPrincipal F e i j y * Canonical.spatialDeriv j φ y) z =
      ∑ j, (Canonical.spatialDeriv i (weightedPrincipal F e i j) z *
        Canonical.spatialDeriv j φ z + weightedPrincipal F e i j z *
          Canonical.spatialDeriv i (Canonical.spatialDeriv j φ) z) := by
    change fderiv ℝ (fun y => ∑ j, weightedPrincipal F e i j y *
      Canonical.spatialDeriv j φ y) z (Canonical.spatialDirection i) = _
    rw [fderiv_fun_sum (fun j _ => (hA i j).fun_mul (hD j))]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hA i j) (hD j)]
    simp only [Canonical.spatialDeriv, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [laplacian_coordinateTest F e he hei hφ hz]
  simp only [hder, Finset.sum_add_distrib]
  have hb : (∑ i, ∑ j, Canonical.spatialDeriv i (weightedPrincipal F e i j) z *
      Canonical.spatialDeriv j φ z) =
      density F e z * ∑ j, drift F e j z * Canonical.spatialDeriv j φ z := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    dsimp only [drift]
    field_simp [(density_pos F e he hei hz.1).ne']
  rw [hb]
  simp only [weightedPrincipal_eq, mul_add, Finset.mul_sum, mul_assoc]
  ring

private theorem testFlux_tsupport_subset (φ : Spacetime n → ℝ) (i : Fin n) :
    tsupport (fun z => ∑ j, weightedPrincipal F e i j z * Canonical.spatialDeriv j φ z) ⊆
      tsupport φ := by
  apply closure_minimal ?_ (isClosed_tsupport φ)
  intro z hz
  by_contra hzφ
  have hd (j) : Canonical.spatialDeriv j φ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hzφ (tsupport_fderiv_apply_subset ℝ (Canonical.spatialDirection j) h))
  exact hz (by simp only [hd, mul_zero, Finset.sum_const_zero])

theorem integral_heat_flux_eq_coordinate_pairing
    {U : Set (Spacetime n)} (hU : IsOpen U) (hUD : U ⊆ domain J e)
    {u : Spacetime n → ℝ} {Cu Cw : ℝ≥0}
    (hu : LipschitzOnWith Cu u U)
    (hw : LipschitzOnWith Cw (fun z => density F e z * u z) U)
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    let w := fun z => density F e z * u z
    let Q := fun i z => ∑ j, weightedPrincipal F e i j z * Canonical.spatialDeriv j φ z
    Integrable (fun z => Canonical.timeDeriv w z * φ z +
      ∑ i, Canonical.spatialDeriv i u z * Q i z) ∧
    IntegrableOn (fun z => w z * (-Canonical.timeDeriv φ z -
      (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1))) U ∧
    (∫ z, Canonical.timeDeriv w z * φ z + ∑ i, Canonical.spatialDeriv i u z * Q i z) =
      ∫ z in U, w z * (-Canonical.timeDeriv φ z -
        (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1)) := by
  let w := fun z => density F e z * u z
  let Q := fun i z => ∑ j, weightedPrincipal F e i j z * Canonical.spatialDeriv j φ z
  obtain ⟨hleft, hright, heq⟩ := Canonical.integral_density_flux_eq_neg hU hu hw
    (fun i j => (contDiffOn_weightedPrincipal F e he hei i j).mono hUD) hφ hφc hφU
  let B := fun z => w z * Canonical.timeDeriv φ z +
    u z * ∑ i, Canonical.spatialDeriv i (Q i) z
  have hzero : ∀ z ∉ U, B z = 0 := by
    intro z hz
    have hzφ : z ∉ tsupport φ := fun h => hz (hφU h)
    have ht : Canonical.timeDeriv φ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hzφ (tsupport_fderiv_apply_subset ℝ (0, 1) h))
    have hs (i) : Canonical.spatialDeriv i (Q i) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hzφ
        (testFlux_tsupport_subset F e he hei φ i
          (tsupport_fderiv_apply_subset ℝ (Canonical.spatialDirection i) h)))
    simp only [B, ht, hs, Finset.sum_const_zero, mul_zero, add_zero]
  have hpoint : ∀ z ∈ U, -B z = w z * (-Canonical.timeDeriv φ z -
      (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1)) := by
    intro z hz
    dsimp only [B, Q]
    rw [divergence_testFlux_eq_laplacian F e he hei hφ (hUD hz)]
    dsimp only [w]
    ring
  have hpair := (hright.neg.integrableOn).congr_fun hpoint hU.measurableSet
  refine ⟨hleft, hpair, ?_⟩
  rw [heq, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← integral_neg]
  exact setIntegral_congr_fun hU.measurableSet hpoint

end PoincareConjecture.RicciFlow.BackwardCoordinates
