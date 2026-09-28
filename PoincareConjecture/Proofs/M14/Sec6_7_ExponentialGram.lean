import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialJacobiField
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingJacobian
import Mathlib.Topology.Instances.Matrix










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}



noncomputable def exponentialDifferential (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) (s : ℝ) : G.Horizontal x →L[ℝ] G.Horizontal (E.gamma Z s) := by
  classical
  exact if hs : (Z, s) ∈ E.domain then E.differential Z s hs else 0



theorem exponentialDifferential_eq (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) :
    exponentialDifferential E Z s = E.differential Z s hs := by
  simp only [exponentialDifferential, dif_pos hs]



noncomputable def exponentialGram (E : M14ExponentialFamily G T x)
    (v : Fin n → G.Horizontal x) (Z : G.Horizontal x) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  G.spacetime.horizontalMetric.inner (E.gamma Z s)
    (exponentialDifferential E Z s (v i)) (exponentialDifferential E Z s (v j))



noncomputable def exponentialJacobian (E : M14ExponentialFamily G T x)
    (v : Fin n → G.Horizontal x) (Z : G.Horizontal x) (s : ℝ) : ℝ :=
  Real.sqrt (max 0 (exponentialGram E v Z s).det)



theorem exponentialJacobian_nonneg (E : M14ExponentialFamily G T x)
    (v : Fin n → G.Horizontal x) (Z : G.Horizontal x) (s : ℝ) :
    0 ≤ exponentialJacobian E v Z s := Real.sqrt_nonneg _



theorem exponentialJacobian_eq_sqrt_det (E : M14ExponentialFamily G T x)
    (v : Fin n → G.Horizontal x) (Z : G.Horizontal x) (s : ℝ) :
    exponentialJacobian E v Z s = Real.sqrt (exponentialGram E v Z s).det := by
  unfold exponentialJacobian
  rw [max_comm, ← Real.sq_sqrt', Real.sqrt_sq (Real.sqrt_nonneg _)]

private theorem metric_pair_heq {p q : G.Point} (hp : p = q)
    {v w : G.Horizontal p} {v' w' : G.Horizontal q}
    (hv : HEq v v') (hw : HEq w w') :
    G.spacetime.horizontalMetric.inner p v w =
      G.spacetime.horizontalMetric.inner q v' w' := by
  cases hp
  cases hv
  cases hw
  rfl



theorem exponentialGram_eq_jacobi_pair
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Fin n → G.Horizontal x)
    {Z : G.Horizontal x} {b s : ℝ} (hb : (Z, b) ∈ E.domain) (hpos : 0 < b)
    (hs : s ∈ M14SqrtParameterInterval 0 (b ^ 2)) (i j : Fin n) :
    exponentialGram E v Z s i j =
      G.spacetime.horizontalMetric.inner ((E.square_path Z b hb hpos).curve s)
        ((initialValuePath_differentialData hM04 hM12
          (exponentialInitialValuePath E Z b hb hpos) (v i)).field s)
        ((initialValuePath_differentialData hM04 hM12
          (exponentialInitialValuePath E Z b hb hpos) (v j)).field s) := by
  have hs' : s ∈ Icc 0 b := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using hs
  have hsurv := (E.maximal_lifetime Z).out (E.domain_zero Z) hb hs'
  unfold exponentialGram
  rw [exponentialDifferential_eq E hsurv]
  exact (metric_pair_heq (exponential_square_curve_eq E Z hb hpos hs)
    (exponentialJacobiField_heq_differential hM04 hM12 E Z (v i) hb hpos hs hsurv)
    (exponentialJacobiField_heq_differential hM04 hM12 E Z (v j) hb hpos hs hsurv)).symm



theorem measureJacobian_eq_exponentialJacobian {τ : ℝ}
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    (D : M14MeasureJacobianData G T τ x E H)
    {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    D.jacobian Z = exponentialJacobian E D.sourceBasis Z (Real.sqrt τ) := by
  rw [D.jacobian_eq Z hZ]
  unfold M14MetricJacobianFromBasis exponentialJacobian
  congr 2
  apply congrArg Matrix.det
  funext i j
  unfold exponentialGram
  rw [exponentialDifferential_eq E (H.survivor Z hZ)]
  exact rescalingEndpointTangent_pair G H Z hZ (D.sourceBasis i) (D.sourceBasis j)

end PoincareConjecture.M14
