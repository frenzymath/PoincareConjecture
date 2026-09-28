import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_PointJetConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarFourJet
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RicciJetNorm

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

open SpacetimeBounds M44

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

def jetChristoffelBilinear {n : ℕ} (J : MetricTwoJet n) :
    E n →L[ℝ] E n →L[ℝ] E n :=
  let flipL :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toLinearIsometry.toContinuousLinearMap
  (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) J.1.inverse).comp
    ((2⁻¹ : ℝ) • (J.2.1 + (flipL.comp J.2.1).flip - flipL.comp J.2.1.flip))

theorem jetChristoffelBilinear_metricTwoJet {n : ℕ}
    (A : E n → MetricCoefficient n) (x : E n) :
    jetChristoffelBilinear (metricTwoJet A x) =
      CoordinateExponential.christoffelBilinear A x := rfl

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

theorem ricci (h : PointJetsConverge A x A0 x0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (hs0 : ContDiffAt ℝ ∞ A0 x0)
    (hi : ∀ i, (A i (x i)).IsInvertible) (hi0 : (A0 x0).IsInvertible) :
    PointJetsConverge (fun i => jetRicciBilinear ∘ SpacetimeBounds.metricTwoJet (A i)) x
      (jetRicciBilinear ∘ SpacetimeBounds.metricTwoJet A0) x0 l :=
  (h.metricTwoJet hs hs0).smooth_postcompose (fun i => contDiffAt_metricTwoJet (hs i))
    (fun i => contDiffAt_jetRicciBilinear (hi i)) (contDiffAt_metricTwoJet hs0)
    (contDiffAt_jetRicciBilinear hi0)

theorem scalar (h : PointJetsConverge A x A0 x0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (hs0 : ContDiffAt ℝ ∞ A0 x0)
    (hi : ∀ i, (A i (x i)).IsInvertible) (hi0 : (A0 x0).IsInvertible) :
    PointJetsConverge (fun i => jetScalarCurvature ∘ SpacetimeBounds.metricTwoJet (A i)) x
      (jetScalarCurvature ∘ SpacetimeBounds.metricTwoJet A0) x0 l :=
  (h.metricTwoJet hs hs0).smooth_postcompose (fun i => contDiffAt_metricTwoJet (hs i))
    (fun i => contDiffAt_jetScalarCurvature (hi i)) (contDiffAt_metricTwoJet hs0)
    (contDiffAt_jetScalarCurvature hi0)

theorem christoffel (h : PointJetsConverge A x A0 x0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (hs0 : ContDiffAt ℝ ∞ A0 x0)
    (hi : ∀ i, (A i (x i)).IsInvertible) (hi0 : (A0 x0).IsInvertible) :
    PointJetsConverge (fun i => CoordinateExponential.christoffelBilinear (A i)) x
      (CoordinateExponential.christoffelBilinear A0) x0 l :=
  (h.metricTwoJet hs hs0).smooth_postcompose (fun i => contDiffAt_metricTwoJet (hs i))
    (fun i => contDiffAt_jetChristoffelBilinear (hi i)) (contDiffAt_metricTwoJet hs0)
    (contDiffAt_jetChristoffelBilinear hi0)

end PointJetsConverge

end PoincareConjecture.M45
