import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Slice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.GradientEnergyTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem exists_ricci_quadratic_bound_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (a b : ℝ) (hb : b < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b,
      ∀ x : L.convergence.limit.carrier.carrier,
      ∀ v : TangentSpace (𝓡 3) x,
        |(L.convergence.limit.flow.connection t).ricci x v v| ≤
          C * (L.convergence.limit.flow.metric t).inner x v v := by
  obtain ⟨B, hB, hcurv⟩ := L.convergence.limit.bounded_curvature_on_past_of_bound_at
    hC L.scalar_curvature_nonnegative_time_derivative hb (hbound b hb)
  refine ⟨27 * B, by positivity, ?_⟩
  intro t ht x v
  have hv : 0 ≤ (L.convergence.limit.flow.metric t).inner x v v := by
    by_cases h : v = 0
    · simp [h]
    · exact ((L.convergence.limit.flow.metric t).pos x v h).le
  have hric := (L.convergence.limit.flow.connection t).abs_ricci_quadratic_le_curvatureTensorNorm x v
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  simp only [Fintype.card_fin, hdim] at hric
  norm_num at hric
  exact hric.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hcurv t ht.2 x))
      (by norm_num : (0 : ℝ) ≤ 27)) hv)

theorem exists_hessian_quadratic_bound_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (a b : ℝ) (hb : b < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b,
      ∀ x : L.convergence.limit.carrier.carrier,
      ∀ v : TangentSpace (𝓡 3) x,
        |(L.convergence.limit.flow.connection t).hessian
          (fun y => L.potential (y, t)) x v v| ≤
            C * (L.convergence.limit.flow.metric t).inner x v v := by
  obtain ⟨C, hC0, hRic⟩ := L.exists_ricci_quadratic_bound_on_Icc hC hbound a b hb
  have hbpos : 0 < -2 * b := by linarith
  refine ⟨1 / (-2 * b) + C, add_nonneg (one_div_nonneg.mpr hbpos.le) hC0, ?_⟩
  intro t ht x v
  have ht0 : t < 0 := ht.2.trans_lt hb
  have hv : 0 ≤ (L.convergence.limit.flow.metric t).inner x v v := by
    by_cases h : v = 0
    · simp [h]
    · exact ((L.convergence.limit.flow.metric t).pos x v h).le
  have hscale : |1 / (2 * t)| ≤ 1 / (-2 * b) := by
    rw [abs_div, abs_one, abs_of_neg (by linarith : 2 * t < 0)]
    apply one_div_le_one_div_of_le (by linarith : 0 < -2 * b)
    linarith [ht.2]
  have hess := L.soliton_equation t ht0 x v v
  have heq : (L.convergence.limit.flow.connection t).hessian
      (fun y => L.potential (y, t)) x v v =
      -(1 / (2 * t)) * (L.convergence.limit.flow.metric t).inner x v v -
        (L.convergence.limit.flow.connection t).ricci x v v := by linarith
  rw [heq]
  calc
    _ ≤ |-(1 / (2 * t)) * (L.convergence.limit.flow.metric t).inner x v v| +
        |(L.convergence.limit.flow.connection t).ricci x v v| := abs_sub _ _
    _ ≤ (1 / (-2 * b)) * (L.convergence.limit.flow.metric t).inner x v v +
        C * (L.convergence.limit.flow.metric t).inner x v v := by
      rw [abs_mul, abs_neg, abs_of_nonneg hv]
      exact add_le_add (mul_le_mul_of_nonneg_right hscale hv) (hRic t ht x v)
    _ = _ := by ring

theorem continuousOn_potential_gradient_norm
    (L : AncientAsymptoticSolitonLimitData S)
    (x : L.convergence.limit.carrier.carrier) :
    ContinuousOn (fun t => (L.convergence.limit.flow.metric t).tangentNorm x
      ((L.convergence.limit.flow.connection t).gradient
        (fun y => L.potential (y, t)) x)) (Iio 0) := by
  intro t ht
  exact ((L.convergence.limit.flow.hasDerivAt_gradient_normSq
    (by simpa only [interior_Iio] using ht) L.potential_smooth x).continuousAt.sqrt).continuousWithinAt

theorem exists_potential_gradient_norm_bound_on_Icc
    (L : AncientAsymptoticSolitonLimitData S)
    (x : L.convergence.limit.carrier.carrier) (a b : ℝ) (hb : b < 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc a b,
      (L.convergence.limit.flow.metric t).tangentNorm x
        ((L.convergence.limit.flow.connection t).gradient
          (fun y => L.potential (y, t)) x) ≤ A := by
  have hc := (L.continuousOn_potential_gradient_norm x).mono
    (show Icc a b ⊆ Iio 0 from fun _ ht => ht.2.trans_lt hb)
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨max A 0, le_max_right _ _, fun t ht =>
    (hA (mem_image_of_mem _ ht)).trans (le_max_left _ _)⟩

theorem exists_tangentNorm_comparison_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (a b : ℝ) (hb : b < 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ∀ x : L.convergence.limit.carrier.carrier,
      ∀ v : TangentSpace (𝓡 3) x,
        (L.convergence.limit.flow.metric s).tangentNorm x v ≤
          A * (L.convergence.limit.flow.metric t).tangentNorm x v := by
  obtain ⟨C, hC0, hRic⟩ := L.exists_ricci_quadratic_bound_on_Icc hC hbound a b hb
  refine ⟨Real.exp (C * (b - a)), Real.exp_pos _, ?_⟩
  intro s hs t ht x v
  have hsub : Icc a b ⊆ Iio 0 := fun _ hr => hr.2.trans_lt hb
  have hd : |s - t| ≤ b - a := abs_le.mpr ⟨by linarith [hs.1, ht.2],
    by linarith [hs.2, ht.1]⟩
  exact (L.convergence.limit.flow.tangentNorm_le_exp_of_ricci_bound
    (convex_Icc a b) hsub x v C (fun r hr => hRic r hr x v) ht hs).trans
      (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hC0)) (Real.sqrt_nonneg _))



theorem exists_potential_gradient_norm_bound_in_reference_metric_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (x : L.convergence.limit.carrier.carrier) (a b : ℝ) (hb : b < 0)
    (s : ℝ) (hs : s ∈ Icc a b) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc a b,
      (L.convergence.limit.flow.metric s).tangentNorm x
        ((L.convergence.limit.flow.connection t).gradient
          (fun y => L.potential (y, t)) x) ≤ A := by
  obtain ⟨A, hA, hgrad⟩ := L.exists_potential_gradient_norm_bound_on_Icc x a b hb
  obtain ⟨B, hB, hcompare⟩ := L.exists_tangentNorm_comparison_on_Icc hC hbound a b hb
  exact ⟨B * A, mul_nonneg hB.le hA, fun t ht =>
    (hcompare s hs t ht x _).trans (mul_le_mul_of_nonneg_left (hgrad t ht) hB.le)⟩



theorem exists_hessian_and_base_gradient_bounds_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (a b : ℝ) (hb : b < 0) (s : ℝ) (hs : s ∈ Icc a b) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      (∀ t ∈ Icc a b, ∀ x : L.convergence.limit.carrier.carrier,
        ∀ v : TangentSpace (𝓡 3) x,
          |(L.convergence.limit.flow.connection t).hessian
            (fun y => L.potential (y, t)) x v v| ≤
              C * (L.convergence.limit.flow.metric t).inner x v v) ∧
      (∀ t ∈ Icc a b,
        (L.convergence.limit.flow.metric s).tangentNorm L.convergence.limit.base
          ((L.convergence.limit.flow.connection t).gradient
            (fun y => L.potential (y, t)) L.convergence.limit.base) ≤ A) := by
  obtain ⟨C, hC0, hhess⟩ := L.exists_hessian_quadratic_bound_on_Icc hC hbound a b hb
  obtain ⟨A, hA, hgrad⟩ := L.exists_potential_gradient_norm_bound_in_reference_metric_on_Icc
    hC hbound L.convergence.limit.base a b hb s hs
  exact ⟨C, A, hC0, hA, hhess, hgrad⟩

end PoincareConjecture.AncientAsymptoticSolitonLimitData
