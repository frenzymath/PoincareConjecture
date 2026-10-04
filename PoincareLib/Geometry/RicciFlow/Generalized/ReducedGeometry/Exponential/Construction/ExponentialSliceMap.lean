import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Construction.SliceLift
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Construction.ExponentialSlices

/-!
# The actual exponential endpoint in its selected time slice

Morgan-Tian Definition 6.25 and Proposition 6.28, pp. 116-117.
The actual endpoint defines a smooth slice map on the open survival
slice. A supplied target point only totalizes it outside survival.
The inclusion chain rule identifies its actual manifold differential
with the frozen horizontal exponential differential.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The actual slice endpoint on survival, totalized by an arbitrary
point of that same slice elsewhere. All geometric assertions retain
survival membership, Definition 6.25 and Proposition 6.28, pp. 116-117. -/
noncomputable def exponentialSliceMap (E : M14ExponentialFamily G T x)
    (τ : ℝ) (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point) (Z : G.Horizontal x) :
    (G.slices (T - τ)).Point := by
  classical
  exact if hZ : (Z, Real.sqrt τ) ∈ E.domain then
    ⟨E.gamma Z (Real.sqrt τ), by simpa only [Real.sq_sqrt hτ] using E.clock Z _ hZ⟩
  else q₀

/-- On survival the total slice map is exactly the actual exponential
endpoint, Proposition 6.28, p. 117. -/
theorem exponentialSliceMap_val (E : M14ExponentialFamily G T x)
    {τ : ℝ} (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt τ) ∈ E.domain) :
    (exponentialSliceMap E τ hτ q₀ Z).val = E.gamma Z (Real.sqrt τ) := by
  simp only [exponentialSliceMap, dif_pos hZ]

/-- The actual slice endpoint is smooth near every surviving vector,
including physical boundary times, Proposition 6.28, p. 117. -/
theorem exponentialSliceMap_contMDiffAt (E : M14ExponentialFamily G T x)
    {τ : ℝ} (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt τ) ∈ E.domain) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffAt (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞ (exponentialSliceMap E τ hτ q₀) Z := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  apply contMDiffAt_slice_of_inclusion
  apply (exponentialFamily_gamma_slice_contMDiffAt E hZ).congr_of_eventuallyEq
  filter_upwards [(exponentialFamily_domain_slice_isOpen E (Real.sqrt τ)).mem_nhds hZ]
    with A hA
  exact exponentialSliceMap_val E hτ q₀ hA

/-- The supplied actual slice tangent equivalence carries the slice
map's actual differential to the frozen horizontal exponential
differential, Proposition 6.28, p. 117. -/
theorem exponentialSliceMap_differential_val (E : M14ExponentialFamily G T x)
    {τ : ℝ} (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt τ) ∈ E.domain) (W : G.Horizontal x) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ((G.slices (T - τ)).tangentEquiv (exponentialSliceMap E τ hτ q₀ Z)
      (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n) (exponentialSliceMap E τ hτ q₀) Z W)).val =
        (E.differential Z (Real.sqrt τ) hZ W).val := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let f := exponentialSliceMap E τ hτ q₀
  have hf := (exponentialSliceMap_contMDiffAt E hτ q₀ hZ).mdifferentiableAt (by simp)
  have hi := (G.slices (T - τ)).inclusion_smooth.mdifferentiableAt
    (x := f Z) (by simp)
  have hchain := mfderiv_comp_apply Z hi hf W
  have heq : ((Subtype.val : (G.slices (T - τ)).Point → G.Point) ∘ f) =ᶠ[𝓝 Z]
      (fun A => E.gamma A (Real.sqrt τ)) := by
    filter_upwards [(exponentialFamily_domain_slice_isOpen E (Real.sqrt τ)).mem_nhds hZ]
      with A hA
    exact exponentialSliceMap_val E hτ q₀ hA
  have hd := congrArg (fun L : G.Horizontal x →L[ℝ] SpacetimeModelVector n => L W)
    (heq.mfderiv_eq (I := 𝓘(ℝ, G.Horizontal x)) (I' := spacetimeModel n))
  rw [(G.slices (T - τ)).tangentEquiv_eq]
  exact hchain.symm.trans (hd.trans (E.differential_pointwise_mfderiv Z (Real.sqrt τ) hZ W).symm)

end PoincareMT.M14
