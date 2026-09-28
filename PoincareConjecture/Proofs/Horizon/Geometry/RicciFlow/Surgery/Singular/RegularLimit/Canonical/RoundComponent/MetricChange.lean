import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Parametrization



noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SingularRoundComponent

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ}



def normalizedMetricAt (N : SingularRoundComponent g epsilon) (h : RiemannianMetric 3 M) :
    RiemannianMetric 3 N.model.carrier :=
  RiemannianMetric.Induced.pullbackMetric (rescaledMetric h N.scale N.scale_pos)
    N.forward N.forward_smooth N.forward_mfderiv_injective

@[simp] theorem normalizedMetricAt_self (N : SingularRoundComponent g epsilon) :
    N.normalizedMetricAt g = N.normalizedMetric := rfl

theorem normalizedMetricAt_inner (N : SingularRoundComponent g epsilon)
    (h : RiemannianMetric 3 M) (x : N.model.carrier) (v w : TangentSpace (𝓡 3) x) :
    (N.normalizedMetricAt h).inner x v w = N.scale * h.inner (N.forward x)
      (mfderiv (𝓡 3) (𝓡 3) N.forward x v) (mfderiv (𝓡 3) (𝓡 3) N.forward x w) := rfl

theorem normalizedMetricAt_pullbackCoefficients_eq
    (N : SingularRoundComponent g epsilon) (h : RiemannianMetric 3 M)
    {f : E → N.model.carrier} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) {x : E} (hx : x ∈ U) :
    (N.normalizedMetricAt h).pullbackCoefficients f x =
      N.scale • h.pullbackCoefficients (N.forward ∘ f) x := by
  ext v w
  change N.scale * h.inner (N.forward (f x))
    (mfderiv (𝓡 3) (𝓡 3) N.forward (f x) (mfderiv (𝓡 3) (𝓡 3) f x v))
    (mfderiv (𝓡 3) (𝓡 3) N.forward (f x) (mfderiv (𝓡 3) (𝓡 3) f x w)) =
    N.scale * h.inner (N.forward (f x))
      (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) x v)
      (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) x w)
  rw [mfderiv_comp x ((N.forward_smooth (f x)).mdifferentiableAt (by simp))
    ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
  rfl

theorem normalizedMetricAt_pullback_jet_eq
    (N : SingularRoundComponent g epsilon) (h : RiemannianMetric 3 M)
    {f : E → N.model.carrier} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) {x : E} (hx : x ∈ U) (j : ℕ) :
    iteratedFDeriv ℝ j ((N.normalizedMetricAt h).pullbackCoefficients f) x =
      N.scale • iteratedFDeriv ℝ j (h.pullbackCoefficients (N.forward ∘ f)) x := by
  have heq : (N.normalizedMetricAt h).pullbackCoefficients f =ᶠ[𝓝 x]
      (fun y => N.scale • h.pullbackCoefficients (N.forward ∘ f) y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact N.normalizedMetricAt_pullbackCoefficients_eq h hU hf hy
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  apply iteratedFDeriv_const_smul_apply'
  exact (h.contDiffAt_pullbackCoefficients
    ((N.forward_smooth (f x)).comp x (hf.contMDiffAt (hU.mem_nhds hx)))).of_le
    (by exact_mod_cast le_top)



theorem normalizedMetricAt_pullback_difference_jet_eq
    (N : SingularRoundComponent g epsilon) (h₁ h₂ : RiemannianMetric 3 M)
    {f : E → N.model.carrier} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) {x : E} (hx : x ∈ U) (j : ℕ) :
    iteratedFDeriv ℝ j ((N.normalizedMetricAt h₁).pullbackCoefficients f -
      (N.normalizedMetricAt h₂).pullbackCoefficients f) x =
      N.scale • (iteratedFDeriv ℝ j (h₁.pullbackCoefficients (N.forward ∘ f)) x -
        iteratedFDeriv ℝ j (h₂.pullbackCoefficients (N.forward ∘ f)) x) := by
  change iteratedFDeriv ℝ j (fun y => (N.normalizedMetricAt h₁).pullbackCoefficients f y -
    (N.normalizedMetricAt h₂).pullbackCoefficients f y) x = _
  have hfy := hf.contMDiffAt (hU.mem_nhds hx)
  rw [fun_iteratedFDeriv_sub_apply
    (((N.normalizedMetricAt h₁).contDiffAt_pullbackCoefficients hfy).of_le
      (by exact_mod_cast le_top))
    (((N.normalizedMetricAt h₂).contDiffAt_pullbackCoefficients hfy).of_le
      (by exact_mod_cast le_top)),
    N.normalizedMetricAt_pullback_jet_eq h₁ hU hf hx,
    N.normalizedMetricAt_pullback_jet_eq h₂ hU hf hx, smul_sub]

end PoincareConjecture.SingularRoundComponent
