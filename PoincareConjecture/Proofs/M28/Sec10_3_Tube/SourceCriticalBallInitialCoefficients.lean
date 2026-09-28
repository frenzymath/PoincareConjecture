import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderMetricBounds
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderFiniteJets
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeInitialPair
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialNodeCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open tube
open PoincareConjecture.Proofs.M28.FiniteHessian

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem normalizedSlice_initial_scale_sq (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) :
    (E (k + H.shift)).flow.scalar
        ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ *
        ((T k).list.node 0).2.scale ^ 2 = ((4 * max C 2)⁻¹) ^ 2 := by
  have hs := congrArg (fun r : ℝ => r ^ 2) (H.tubeNodeScale_zero T k)
  simpa only [tubeNodeScale, mul_pow, Real.sq_sqrt (H.base_scalar_pos k).le] using hs

theorem normalizedSlice_initial_coefficients (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ)
    (q : UnitTwoSphere) (s : ℝ) :
    (H.normalizedSliceMetric k).pullbackCoefficients
        (cylinderNeckChart ((T k).list.node 0).2 q s) =
      fun x => ((4 * max C 2)⁻¹) ^ 2 •
        cylinderNeckCoefficients ((T k).list.node 0).2 q s x := by
  funext x
  change RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric _ _ _)
    (cylinderNeckChart ((T k).list.node 0).2 q s) x = _
  rw [scaleSmoothMetric_cylinderNeckCoefficients, H.normalizedSlice_initial_scale_sq]

theorem normalizedSlice_initial_coefficient_lower (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (((4 * max C 2)⁻¹) ^ 2 * (1 - epsilon)) * ‖v‖ ^ 2 ≤
      (H.normalizedSliceMetric k).pullbackCoefficients
        (cylinderNeckChart ((T k).list.node 0).2 q s) 0 v v := by
  have heps := (T k).initial_node_geometry.1
  have hsN : s ∈ Ioo (-((T k).list.node 0).2.epsilon⁻¹)
      ((T k).list.node 0).2.epsilon⁻¹ := by simpa only [heps] using hs
  have h := (cylinderNeckCoefficients_quadratic_bounds ((T k).list.node 0).2 q hsN v).1
  rw [heps] at h
  rw [H.normalizedSlice_initial_coefficients]
  simpa only [smul_apply, smul_eq_mul, mul_assoc] using
    mul_le_mul_of_nonneg_left h (sq_nonneg ((4 * max C 2)⁻¹))

theorem hasUniformJetBoundsAt_normalizedSlice_initial_coefficients
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    {ι : Type*} (k : ι → ℕ) (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (m : ℕ) (hm : m ≤ ⌊epsilon⁻¹⌋₊) :
    HasUniformJetBoundsAt m
      (fun i => (H.normalizedSliceMetric (k i)).pullbackCoefficients
        (cylinderNeckChart ((T (k i)).list.node 0).2 (q i) (s i)))
      (fun _ => (0 : EuclideanSpace ℝ (Fin 3))) := by
  let : AddMonoid (SpacetimeBounds.MetricCoefficient 3) :=
    (inferInstance : NormedAddCommGroup (SpacetimeBounds.MetricCoefficient 3)).toAddMonoid
  let N := fun i => ((T (k i)).list.node 0).2
  have heps (i : ι) : (N i).epsilon = epsilon := (T (k i)).initial_node_geometry.1
  have heps0 := (T 0).initial_node_geometry.1
  have hpos : 0 < epsilon := heps0 ▸ ((T 0).list.node 0).2.epsilon_pos
  have hsmall : epsilon ≤ 1 := by
    have h := heps0 ▸ ((T 0).list.node 0).2.epsilon_lt_half
    linarith
  have hj := hasUniformJetBoundsAt_cylinderNeckCoefficients N hpos hsmall heps m hm q s hs
  have hc (i : ι) : ContDiffAt ℝ ∞ (cylinderNeckCoefficients (N i) (q i) (s i)) 0 := by
    apply (contDiffOn_cylinderNeckCoefficients (N i) (q i) (s i)).contDiffAt
    apply (isOpen_cylinderNeckChartDomain (N i) (q i) (s i)).mem_nhds
    apply zero_mem_cylinderNeckChartDomain
    simpa only [heps i] using hs i
  let L : SpacetimeBounds.MetricCoefficient 3 →L[ℝ] SpacetimeBounds.MetricCoefficient 3 :=
    ((4 * max C 2)⁻¹) ^ 2 • ContinuousLinearMap.id ℝ (SpacetimeBounds.MetricCoefficient 3)
  have hscaled := hj.clm (G := SpacetimeBounds.MetricCoefficient 3) hc L
  apply hscaled.congr_germ
  intro i
  filter_upwards [] with x
  change ((4 * max C 2)⁻¹) ^ 2 • cylinderNeckCoefficients (N i) (q i) (s i) x = _
  exact (congrFun (H.normalizedSlice_initial_coefficients T (k i) (q i) (s i)) x).symm

end PoincareConjecture.M28.CounterexampleNeckFamily
