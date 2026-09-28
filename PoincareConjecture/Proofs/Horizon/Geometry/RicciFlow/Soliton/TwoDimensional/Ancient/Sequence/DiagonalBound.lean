import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.LengthBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Endpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem backwardLIntegrand_const (K : AncientKappaSolution 2 M) (p : M) (s : ℝ) :
    backwardLIntegrand K.flow 0 (fun _ => p) s =
      Real.sqrt s * (K.flow.connection (-s)).scalarCurvature p := by
  simp [backwardLIntegrand, curveVelocity, mfderiv_const, zero_sub]
  left
  exact congrArg (fun t => (K.flow.connection t).scalarCurvature p) (zero_sub s)

theorem continuousOn_backwardLIntegrand_const (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} :
    ContinuousOn (backwardLIntegrand K.flow 0 (fun _ => p)) (Icc 0 τ) := by
  have hmap : MapsTo (fun s : ℝ => -s) (Icc 0 τ) (Iic 0) := by
    intro s hs
    change -s ≤ 0
    linarith [hs.1]
  have hR := (K.flow.continuousOn_scalarCurvature_ancient_surface p).comp
    continuous_neg.continuousOn hmap
  have heq := funext (K.backwardLIntegrand_const p)
  rw [heq]
  exact Real.continuous_sqrt.continuousOn.mul hR

noncomputable def constantBackwardTimePath (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) : BackwardTimePath K.flow 0 0 τ where
  curve := fun _ => p
  nonnegative := le_rfl
  ordered := hτ
  terminal_mem := by simp
  time_mem s hs := by simpa using hs.1
  continuous := continuousOn_const
  regular := contMDiffOn_const
  l_integrable := (K.continuousOn_backwardLIntegrand_const p).intervalIntegrable_of_Icc hτ.le

theorem reducedLength_self_le_of_scalar_le (K : AncientKappaSolution 2 M)
    (p : M) {τ C : ℝ} (hτ : 0 < τ) (hC : 0 ≤ C)
    (hR : ∀ s ∈ Icc 0 τ, (K.flow.connection (-s)).scalarCurvature p ≤ C) :
    reducedLength K.flow 0 p p τ ≤ C * τ / 2 := by
  have hpath := K.reducedLength_le_path (K.constantBackwardTimePath p hτ) rfl rfl
  have hbound : backwardLLength K.flow 0 0 τ (fun _ => p) ≤
      τ * (Real.sqrt τ * C) := by
    have h := intervalIntegral.integral_mono_on hτ.le
      (K.constantBackwardTimePath p hτ).l_integrable (intervalIntegrable_const)
      (fun s hs => show backwardLIntegrand K.flow 0 (fun _ => p) s ≤ Real.sqrt τ * C from by
        rw [K.backwardLIntegrand_const]
        exact (mul_le_mul_of_nonneg_left (hR s hs) (Real.sqrt_nonneg s)).trans
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs.2) hC))
    simpa only [backwardLLength, constantBackwardTimePath,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  calc
    reducedLength K.flow 0 p p τ ≤
        backwardLLength K.flow 0 0 τ (fun _ => p) / (2 * Real.sqrt τ) := hpath
    _ ≤ (τ * (Real.sqrt τ * C)) / (2 * Real.sqrt τ) :=
      div_le_div_of_nonneg_right hbound (mul_nonneg (by norm_num) hsq.le)
    _ = C * τ / 2 := by field_simp

theorem exists_reducedLength_self_linear_bound (K : AncientKappaSolution 2 M) (p : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Ioc (0 : ℝ) 1,
      reducedLength K.flow 0 p p τ ≤ C * τ / 2 := by
  have hmap : MapsTo (fun s : ℝ => -s) (Icc (0 : ℝ) 1) (Iic 0) := by
    intro s hs
    change -s ≤ 0
    linarith [hs.1]
  have hR := (K.flow.continuousOn_scalarCurvature_ancient_surface p).comp
    continuous_neg.continuousOn hmap
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hR
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (K.flow.connection (-s)).scalarCurvature p ≤ C := hC ⟨s, hs, rfl⟩
  have hC0 : 0 ≤ C := by
    have hR0 := (K.flow.connection (-0)).scalar_nonnegative_of_nonnegative_curvatureOperator p
      (K.nonnegative_curvature_operator (-0) (by norm_num) p)
    have h := hbound 0 (by simp)
    exact hR0.trans h
  refine ⟨C, hC0, fun τ hτ => K.reducedLength_self_le_of_scalar_le p hτ.1 hC0 ?_⟩
  intro s hs
  exact hbound s ⟨hs.1, hs.2.trans hτ.2⟩

theorem tendsto_reducedLength_self_zero (K : AncientKappaSolution 2 M) (p : M) :
    Tendsto (fun τ => reducedLength K.flow 0 p p τ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := K.exists_reducedLength_self_linear_bound p
  have ht : Tendsto (fun τ : ℝ => τ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun τ : ℝ => C * τ / 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ht.const_mul C).div_const 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun τ => K.reducedLength_nonneg p p τ)
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with τ hτ
    exact hC τ hτ

end PoincareConjecture.AncientKappaSolution
