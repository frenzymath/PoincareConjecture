import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]



theorem localDiffeomorphAt_of_smooth_bijective_derivative
    {f : E -> E} (hf : ContDiff Real ∞ f) {a : E}
    (ha : Function.Bijective (fderiv Real f a)) :
    IsLocalDiffeomorphAt 𝓘(Real, E) 𝓘(Real, E) ∞ f a := by
  let U : Set E := {x | IsUnit (fderiv Real f x)}
  have hU : IsOpen U := Units.isOpen.preimage (hf.fderiv_right (m := ∞) (by simp)).continuous
  let A := ContinuousLinearEquiv.ofBijective (fderiv Real f a)
    (LinearMap.ker_eq_bot.mpr ha.1) (LinearMap.range_eq_top.mpr ha.2)
  have hd : HasFDerivAt f A.toContinuousLinearMap a :=
    (hf.differentiable (by simp) a).hasFDerivAt
  let Q := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  let H := Q.restr U
  have hHa : a ∈ H.source := by
    rw [Q.restr_source' U hU]
    exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),
      ContinuousLinearMap.isUnit_iff_bijective.mpr ha⟩
  have hHi : ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ H.symm H.target := by
    intro y hy
    have hz := H.map_target hy
    have hu' : H.symm y ∈ U := interior_subset hz.2
    have hu : IsUnit (fderiv Real f (H.symm y)) := hu'
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hu
    let B := ContinuousLinearEquiv.ofBijective (fderiv Real f (H.symm y))
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    have hdB : HasFDerivAt H B.toContinuousLinearMap (H.symm y) :=
      (hf.differentiable (by simp) _).hasFDerivAt
    exact (H.contDiffAt_symm hy hdB hf.contDiffAt).contMDiffWithinAt.mono (subset_univ _)
  let d : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := {
    toPartialEquiv := H.toPartialEquiv
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := hf.contMDiff.contMDiffOn
    contMDiffOn_invFun := hHi }
  exact ⟨d, hHa, fun _ _ => rfl⟩

end Poincare.Manifold.Schoenflies
