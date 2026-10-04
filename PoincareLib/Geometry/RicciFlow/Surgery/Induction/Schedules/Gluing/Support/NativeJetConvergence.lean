import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Convergence.PointJetConvergence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.ScalarFourJet
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.RicciJetNorm

/-!
# Native geometric operators on convergent neck jets

The finite-jet comparison in Morgan--Tian Proposition 15.2, pp. 353-354,
uses the smooth coordinate operators on the invertible metric locus.
See NativeJetConvergence.md for the exact local hypotheses.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M45

open SpacetimeBounds M44

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

/-- Koszul contraction with both vector slots retained as linear maps.
Source: equation (1.1), p. 4, in the coordinate proof of Proposition 15.2. -/
def jetChristoffelBilinear {n : ℕ} (J : MetricTwoJet n) :
    E n →L[ℝ] E n →L[ℝ] E n :=
  let flipL :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toLinearIsometry.toContinuousLinearMap
  (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) J.1.inverse).comp
    ((2⁻¹ : ℝ) • (J.2.1 + (flipL.comp J.2.1).flip - flipL.comp J.2.1.flip))

/-- The native operator is the actual coordinate Christoffel bilinear map.
Source: the Koszul formula in equation (1.1), p. 4. -/
theorem jetChristoffelBilinear_metricTwoJet {n : ℕ}
    (A : E n → MetricCoefficient n) (x : E n) :
    jetChristoffelBilinear (metricTwoJet A x) =
      CoordinateExponential.christoffelBilinear A x := rfl

/-- The bilinear Koszul operator is smooth at every invertible metric jet.
Source: the finite-jet argument in Proposition 15.2, pp. 353-354. -/
theorem contDiffAt_jetChristoffelBilinear {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@jetChristoffelBilinear n) J := by
  have hi : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  have hf : ContDiff ℝ ∞ (fun A : E n →L[ℝ] E n →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).contDiff
  have hf' : ContDiff ℝ ∞
      (fun A : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n →L[ℝ] ℝ)).contDiff
  unfold jetChristoffelBilinear
  fun_prop

namespace PointJetsConverge

variable {ι : Type*} {n : ℕ} {A : ι → E n → MetricCoefficient n}
  {x : ι → E n} {A0 : E n → MetricCoefficient n} {x0 : E n} {l : Filter ι}

/-- Packaging a metric two-jet shifts the convergent input orders by two.
Source: the finite-jet comparison in Proposition 15.2, pp. 353-354. -/
theorem metricTwoJet (h : PointJetsConverge A x A0 x0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (hs0 : ContDiffAt ℝ ∞ A0 x0) :
    PointJetsConverge (fun i => SpacetimeBounds.metricTwoJet (A i)) x
      (SpacetimeBounds.metricTwoJet A0) x0 l := by
  have hd := fun i => (hs i).fderiv_right (m := ∞) (by simp)
  have hd0 := hs0.fderiv_right (m := ∞) (by simp)
  exact h.prodMk (h.fderiv.prodMk h.fderiv.fderiv hd
    (fun i => (hd i).fderiv_right (m := ∞) (by simp)) hd0
    (hd0.fderiv_right (m := ∞) (by simp))) hs
    (fun i => (hd i).prodMk ((hd i).fderiv_right (m := ∞) (by simp))) hs0
    (hd0.prodMk (hd0.fderiv_right (m := ∞) (by simp)))

/-- Native Ricci jets converge on the actual and limiting invertible loci.
Source: Definition 1.8, p. 7, in Proposition 15.2, pp. 353-354. -/
theorem ricci (h : PointJetsConverge A x A0 x0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (hs0 : ContDiffAt ℝ ∞ A0 x0)
    (hi : ∀ i, (A i (x i)).IsInvertible) (hi0 : (A0 x0).IsInvertible) :
    PointJetsConverge (fun i => jetRicciBilinear ∘ SpacetimeBounds.metricTwoJet (A i)) x
      (jetRicciBilinear ∘ SpacetimeBounds.metricTwoJet A0) x0 l :=
  (h.metricTwoJet hs hs0).smooth_postcompose (fun i => contDiffAt_metricTwoJet (hs i))
    (fun i => contDiffAt_jetRicciBilinear (hi i)) (contDiffAt_metricTwoJet hs0)
    (contDiffAt_jetRicciBilinear hi0)

/-- Native scalar jets converge on the actual and limiting invertible loci.
Source: Definition 1.8, p. 7, in Proposition 15.2, pp. 353-354. -/
theorem scalar (h : PointJetsConverge A x A0 x0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (hs0 : ContDiffAt ℝ ∞ A0 x0)
    (hi : ∀ i, (A i (x i)).IsInvertible) (hi0 : (A0 x0).IsInvertible) :
    PointJetsConverge (fun i => jetScalarCurvature ∘ SpacetimeBounds.metricTwoJet (A i)) x
      (jetScalarCurvature ∘ SpacetimeBounds.metricTwoJet A0) x0 l :=
  (h.metricTwoJet hs hs0).smooth_postcompose (fun i => contDiffAt_metricTwoJet (hs i))
    (fun i => contDiffAt_jetScalarCurvature (hi i)) (contDiffAt_metricTwoJet hs0)
    (contDiffAt_jetScalarCurvature hi0)

/-- The full Christoffel bilinear maps have convergent jets, including their
vector slots. Source: the transition equation in Proposition 15.2, pp. 353-354. -/
theorem christoffel (h : PointJetsConverge A x A0 x0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (hs0 : ContDiffAt ℝ ∞ A0 x0)
    (hi : ∀ i, (A i (x i)).IsInvertible) (hi0 : (A0 x0).IsInvertible) :
    PointJetsConverge (fun i => CoordinateExponential.christoffelBilinear (A i)) x
      (CoordinateExponential.christoffelBilinear A0) x0 l :=
  (h.metricTwoJet hs hs0).smooth_postcompose (fun i => contDiffAt_metricTwoJet (hs i))
    (fun i => contDiffAt_jetChristoffelBilinear (hi i)) (contDiffAt_metricTwoJet hs0)
    (contDiffAt_jetChristoffelBilinear hi0)

end PointJetsConverge

end PoincareMT.M45
