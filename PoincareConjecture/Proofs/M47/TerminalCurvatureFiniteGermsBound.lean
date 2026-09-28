import PoincareConjecture.Proofs.M47.TerminalCurvaturePositiveBound
import PoincareConjecture.Proofs.M47.TerminalCurvatureNullBound
import PoincareConjecture.Proofs.M47.TerminalCurvatureNullLine
import PoincareConjecture.Proofs.M47.TerminalCurvaturePrescribedSection









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47



theorem terminalCurvature_bound_of_finite_germs
    {epsilon1 epsilon A H : ℝ} (hM45 : M45SmallNeckScaleBound.{u} epsilon1)
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon1)
    (hcalibrated : epsilon ≤ 1 / 200) (hA : 0 < A)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u}) (hcomplete : MetricComplete g)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (p : M) (hscalar : D.scalarCurvature p ≠ 0)
    {ι : Type*} (U : ι → Opens M) [∀ i, ConnectedSpace (U i)]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow 3 (U i) (Icc (-tau i) 0))
    (hmetric : ∀ i (y : U i) (v w : TangentSpace (𝓡 3) y),
      ((F i).metric 0).inner y v w = g.inner y.val v w)
    (hlocalOperator : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ y,
      ((F i).connection t).NonnegativeCurvatureOperator y)
    (htriple : ∀ x y z : M, ∃ i, x ∈ U i ∧ y ∈ U i ∧ z ∈ U i)
    (hreadout : ∀ x, H ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = epsilon ∧
        D.scalarCurvature x ≤ A * D.scalarCurvature N.center) ∨ IsCompact (univ : Set M)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  classical
  by_cases hpositive : ∀ x (v w : TangentSpace (𝓡 3) x),
      LeviCivitaData.IsOrthonormalPair g x v w → 0 < D.sectionalCurvature x v w
  · exact terminalCurvature_positive_bound_of_neck_readout hM45 hepsilon hsmall hA
      D (hC.tensor_calculus 3 M g D) hcomplete hoperator hpositive hreadout
  push Not at hpositive
  obtain ⟨x, v, w, hframe, hbad⟩ := hpositive
  have hzero : D.curvatureTensor x v w v w = 0 := by
    have hbadnum : D.curvatureTensor x v w v w ≤ 0 := by
      simpa only [LeviCivitaData.sectionalCurvature, hframe.1, hframe.2.1,
        hframe.2.2, one_mul, zero_pow (by omega : 2 ≠ 0), sub_zero, div_one] using hbad
    exact le_antisymm hbadnum
      (D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x (hoperator x) v w)
  obtain ⟨hrank, _, ⟨cover⟩⟩ := terminalCurvature_null_line_of_finite_germs D hC
    U tau htau F hmetric hlocalOperator p hscalar x v w
      hframe.1 hframe.2.1 hframe.2.2 hzero (fun y => htriple p x y)
  have hsec : ∀ i t, t ∈ Icc (-tau i) 0 →
      ((F i).connection t).NonnegativeSectionalCurvature := fun i t ht y =>
    ((F i).connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hlocalOperator i t ht y)
  have hcover : ∀ y : M, ∃ i, y ∈ U i := by
    intro y
    obtain ⟨i, _, _, hy⟩ := htriple p p y
    exact ⟨i, hy⟩
  exact terminalCurvature_null_bound_of_neck_readout hcalibrated D hC hcomplete
    hoperator cover hrank
    (terminalCurvature_prescribed_parallel_section D hC hrank U tau htau F hmetric hsec hcover)
    hreadout

end PoincareConjecture.M47
