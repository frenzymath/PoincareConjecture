import PoincareConjecture.Proofs.M14.Sec6_3_SliceLift
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialSlices

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

noncomputable def exponentialSliceMap (E : M14ExponentialFamily G T x)
    (τ : ℝ) (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point) (Z : G.Horizontal x) :
    (G.slices (T - τ)).Point := by
  classical
  exact if hZ : (Z, Real.sqrt τ) ∈ E.domain then
    ⟨E.gamma Z (Real.sqrt τ), by simpa only [Real.sq_sqrt hτ] using E.clock Z _ hZ⟩
  else q₀

theorem exponentialSliceMap_val (E : M14ExponentialFamily G T x)
    {τ : ℝ} (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt τ) ∈ E.domain) :
    (exponentialSliceMap E τ hτ q₀ Z).val = E.gamma Z (Real.sqrt τ) := by
  simp only [exponentialSliceMap, dif_pos hZ]

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

end PoincareConjecture.M14
