import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarFourJet









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M45

open M44 SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

noncomputable local instance constantScalarCoefficientNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricCoefficient n) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance constantScalarCoefficientNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricCoefficient n) := ContinuousLinearMap.toNormedSpace

noncomputable local instance constantScalarTwoJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricTwoJet n) := Prod.normedAddCommGroup

noncomputable local instance constantScalarTwoJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricTwoJet n) := Prod.normedSpace

set_option maxHeartbeats 800000 in



theorem model_jetScalarLaplacian_eq_zero_of_const {n : ℕ}
    (B : E n → MetricCoefficient n) (x : E n) (hB : ContDiffAt ℝ ∞ B x)
    (hinv : (B x).IsInvertible) (c : ℝ)
    (hscalar : jetScalarCurvature ∘ metricTwoJet B = fun _ => c) :
    jetScalarLaplacian (scalarMetricFourJet B x) = 0 := by
  have hJ := contDiffAt_metricTwoJet hB
  have hS := contDiffAt_jetScalarCurvature (J := metricTwoJet B x) hinv
  have hfirst (i : Fin n) : jetScalarFirst (scalarMetricFourJet B x) i = 0 := by
    have h := congrArg (fun L : E n →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i))
      (fderiv_comp x (hS.differentiableAt (by simp)) (hJ.differentiableAt (by simp)))
    rw [hscalar] at h
    simpa only [fderiv_const_apply, zero_apply, ContinuousLinearMap.comp_apply,
      jetScalarFirst, scalarMetricFourJet] using h.symm
  have hsecond (i j : Fin n) : jetScalarSecond (scalarMetricFourJet B x) i j = 0 := by
    have h := second_fderiv_comp_of_contDiffAt hJ hS
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
    rw [hscalar] at h
    have hconst : fderiv ℝ (fun _ : E n => c) = fun _ => 0 :=
      funext fun y => fderiv_const_apply (x := y) c
    rw [hconst] at h
    simpa only [fderiv_const_apply, zero_apply, jetScalarSecond, scalarMetricFourJet]
      using h.symm
  change (∑ i, ∑ j,
    EuclideanSpace.proj j ((B x).inverse (EuclideanSpace.proj i)) *
      jetScalarSecond (scalarMetricFourJet B x) i j) -
    (∑ i, EuclideanSpace.proj i
      (jetContractedChristoffel (scalarMetricFourJet B x).1) *
      jetScalarFirst (scalarMetricFourJet B x) i) = 0
  simp only [hfirst, hsecond, mul_zero, Finset.sum_const_zero, sub_self]

end PoincareConjecture.M45
