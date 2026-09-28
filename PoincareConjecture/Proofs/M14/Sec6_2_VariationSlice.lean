import PoincareConjecture.Proofs.M14.Sec6_2_VariationPaths

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

def variationPathBetween (V : M14LVariationData G p R) {u : ℝ}
    (hu : u ∈ V.parameterDomain) {x' y' : G.Point}
    (hx : V.family a u = x') (hy : V.family b u = y') :
    M14BackwardPath G T a b x' y' := by
  have hmaps : MapsTo (fun τ : ℝ => (Real.sqrt τ, u)) (Icc a b) V.squareDomain :=
    fun _ hτ => V.square_contains ⟨⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩, hu⟩
  have hagrees (τ : ℝ) (hτ : τ ∈ Icc a b) :
      V.squareFamily (Real.sqrt τ) u = V.family τ u := by
    simpa only [Real.sq_sqrt (p.tau_nonneg.trans hτ.1)] using V.square_agrees (Real.sqrt τ)
      ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩ u hu
  refine {
    tau_nonneg := p.tau_nonneg
    tau_lt := p.tau_lt
    base_time := hx ▸ V.family_time u hu a ⟨le_rfl, p.tau_lt.le⟩
    endpoint_time := hy ▸ V.family_time u hu b ⟨p.tau_lt.le, le_rfl⟩
    curve := fun τ => V.family τ u
    curve_start := hx
    curve_end := hy
    curve_time := V.family_time u hu
    curve_continuous := ?_
    curve_regular := ?_
    horizontal_velocity := V.family_velocity u
    derivative_eq := V.family_derivative u hu
    action_integrable := V.action_integrable u hu }
  · exact (V.square_smooth.continuousOn.comp
      (Real.continuous_sqrt.prodMk continuous_const).continuousOn hmaps).congr
        (fun τ hτ => (hagrees τ hτ).symm)
  · have hsqrt : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1 Real.sqrt (Ioo a b) := by
      intro τ hτ
      exact (Real.contDiffAt_sqrt
        (ne_of_gt (p.tau_nonneg.trans_lt hτ.1))).contMDiffAt.contMDiffWithinAt
    exact ((V.square_smooth.of_le (by simp)).comp
      (hsqrt.prodMk contMDiffOn_const) (hmaps.mono_left Ioo_subset_Icc_self)).congr
        (fun τ hτ => (hagrees τ (Ioo_subset_Icc_self hτ)).symm)

end PoincareConjecture.M14
