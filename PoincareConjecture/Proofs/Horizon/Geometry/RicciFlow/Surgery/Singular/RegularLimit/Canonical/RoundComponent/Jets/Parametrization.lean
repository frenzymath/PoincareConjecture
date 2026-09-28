import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.Component

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

theorem forward_mfderiv_invertible (N : SingularRoundComponent g epsilon)
    (x : N.model.carrier) : (mfderiv (𝓡 3) (𝓡 3) N.forward x).IsInvertible := by
  let L : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) N.forward x
  have hi : Function.Injective L := N.forward_mfderiv_injective x
  have hs : Function.Surjective L := LinearMap.surjective_of_injective
    (f := L.toLinearMap) hi
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem forward_comp_mfderiv_invertible (N : SingularRoundComponent g epsilon)
    {f : E → N.model.carrier} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : E} (hx : x ∈ U) :
    (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) x).IsInvertible := by
  rw [mfderiv_comp x ((N.forward_smooth (f x)).mdifferentiableAt (by simp))
    ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
  exact (N.forward_mfderiv_invertible (f x)).comp (hi x hx)

theorem normalizedMetric_pullbackCoefficients_eq
    (N : SingularRoundComponent g epsilon)
    {f : E → N.model.carrier} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) {x : E} (hx : x ∈ U) :
    N.normalizedMetric.pullbackCoefficients f x =
      N.scale • g.pullbackCoefficients (N.forward ∘ f) x := by
  ext v w
  change N.scale * g.inner (N.forward (f x))
    (mfderiv (𝓡 3) (𝓡 3) N.forward (f x) (mfderiv (𝓡 3) (𝓡 3) f x v))
    (mfderiv (𝓡 3) (𝓡 3) N.forward (f x) (mfderiv (𝓡 3) (𝓡 3) f x w)) =
    N.scale * g.inner (N.forward (f x))
      (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) x v)
      (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) x w)
  rw [mfderiv_comp x ((N.forward_smooth (f x)).mdifferentiableAt (by simp))
    ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
  rfl

theorem normalizedMetric_pullback_jet_eq (N : SingularRoundComponent g epsilon)
    {f : E → N.model.carrier} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) {x : E} (hx : x ∈ U) (j : ℕ) :
    iteratedFDeriv ℝ j (N.normalizedMetric.pullbackCoefficients f) x =
      N.scale • iteratedFDeriv ℝ j (g.pullbackCoefficients (N.forward ∘ f)) x := by
  have heq : N.normalizedMetric.pullbackCoefficients f =ᶠ[𝓝 x]
      (fun y => N.scale • g.pullbackCoefficients (N.forward ∘ f) y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact N.normalizedMetric_pullbackCoefficients_eq hU hf hy
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  apply iteratedFDeriv_const_smul_apply'
  exact (g.contDiffAt_pullbackCoefficients
    ((N.forward_smooth (f x)).comp x (hf.contMDiffAt (hU.mem_nhds hx)))).of_le
    (by exact_mod_cast le_top)

end PoincareConjecture.SingularRoundComponent
