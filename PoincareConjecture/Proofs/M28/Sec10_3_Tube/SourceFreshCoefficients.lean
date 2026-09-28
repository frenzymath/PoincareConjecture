import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshCore
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderMetricBounds
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderFiniteJets
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.VaryingScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open tube PoincareConjecture.Proofs.M28.FiniteHessian

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E)




theorem normalizedSlice_fresh_coefficient_lower (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    {a : ℝ} (hfloor : a ≤ (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ * N.scale ^ 2)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (a * (1 - N.epsilon)) * ‖v‖ ^ 2 ≤
      (H.normalizedSliceMetric k).pullbackCoefficients (cylinderNeckChart N q s) 0 v v := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hnonneg : 0 ≤ (1 - N.epsilon) * ‖v‖ ^ 2 :=
    mul_nonneg (by linarith [N.epsilon_lt_half]) (sq_nonneg _)
  change _ ≤ RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric _ Q hQ)
    (cylinderNeckChart N q s) 0 v v
  rw [scaleSmoothMetric_cylinderNeckCoefficients]
  change _ ≤ (Q * N.scale ^ 2) * cylinderNeckCoefficients N q s 0 v v
  calc
    _ = a * ((1 - N.epsilon) * ‖v‖ ^ 2) := by ring
    _ ≤ (Q * N.scale ^ 2) * ((1 - N.epsilon) * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hfloor hnonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cylinderNeckCoefficients_quadratic_bounds N q hs v).1
      (mul_nonneg hQ.le (sq_nonneg _))





theorem hasUniformJetBoundsAt_normalizedSlice_fresh_coefficients
    {ι : Type*} (k : ι → ℕ)
    (N : ∀ i, EpsilonNeck
      ((E (k i + H.shift)).flow.metric (E (k i + H.shift)).time))
    (heps : ∀ i, (N i).epsilon = epsilon) (hepspos : 0 < epsilon)
    (hepssmall : epsilon ≤ 1) {B : ℝ}
    (hupper : ∀ i, (E (k i + H.shift)).flow.scalar
      ⟨(E (k i + H.shift)).time, (E (k i + H.shift)).basepoint⟩ * (N i).scale ^ 2 ≤ B)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (m : ℕ) (hm : m ≤ ⌊epsilon⁻¹⌋₊) :
    HasUniformJetBoundsAt m
      (fun i => (H.normalizedSliceMetric (k i)).pullbackCoefficients
        (cylinderNeckChart (N i) (q i) (s i))) (fun _ => 0) := by
  have hj := hasUniformJetBoundsAt_cylinderNeckCoefficients
    N hepspos hepssmall heps m hm q s hs
  have hc (i : ι) : ContDiffAt ℝ ∞ (cylinderNeckCoefficients (N i) (q i) (s i)) 0 := by
    apply (contDiffOn_cylinderNeckCoefficients (N i) (q i) (s i)).contDiffAt
    apply (isOpen_cylinderNeckChartDomain (N i) (q i) (s i)).mem_nhds
    apply zero_mem_cylinderNeckChartDomain
    simpa only [heps i] using hs i
  let c := fun i => (E (k i + H.shift)).flow.scalar
    ⟨(E (k i + H.shift)).time, (E (k i + H.shift)).basepoint⟩ * (N i).scale ^ 2
  have hcb (i : ι) : ‖c i‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (H.base_scalar_pos (k i))
      (sq_pos_of_pos (N i).scale_pos))]
    exact hupper i
  apply (hj.smul_family hc c hcb).congr_germ
  intro i
  filter_upwards [] with x
  exact (scaleSmoothMetric_cylinderNeckCoefficients (N i) _
    (H.base_scalar_pos (k i)) (q i) (s i) x).symm

end PoincareConjecture.M28.CounterexampleNeckFamily
