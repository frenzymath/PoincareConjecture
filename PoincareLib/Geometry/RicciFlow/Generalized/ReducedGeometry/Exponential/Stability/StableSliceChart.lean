import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StableInjectivity
import Mathlib.Topology.IsLocalHomeomorph

/-!
# The stable endpoint map as a smooth slice chart

Morgan-Tian Proposition 6.28, p. 117, and Lemma 6.71, p. 141. The supplied
local inverses and the derived stable injectivity produce one open partial
homeomorphism on the full stable carrier, with its actual smooth inverse.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

/-- The actual slice endpoint map is a local homeomorphism on its stable
carrier, Morgan-Tian Proposition 6.28, p. 117. -/
theorem stable_slice_isLocalHomeomorphOn (H : M14StableSet G T τ x E) :
    IsLocalHomeomorphOn H.endpoint_slice_map H.carrier := by
  intro Z hZ
  obtain ⟨U, V, inv, hU, hV, hZU, _, hUc, hUV, hcont, _, hmap,
    _, _, hleft, hright⟩ := H.local_inverse Z hZ
  let e : OpenPartialHomeomorph (G.Horizontal x) (G.slices (T - τ)).Point :=
    { toFun := H.endpoint_slice_map
      invFun := inv
      source := U
      target := V
      map_source' := fun W hW => hUV ▸ (show H.endpoint_slice_map W ∈
        H.endpoint_slice_map '' U from ⟨W, hW, rfl⟩)
      map_target' := hmap
      left_inv' := hleft
      right_inv' := hright
      continuousOn_toFun := H.endpoint_slice_continuous.mono hUc
      continuousOn_invFun := hcont
      open_source := hU
      open_target := hV }
  exact ⟨e, hZU, rfl⟩

/-- Restricting the endpoint map to the open stable carrier gives an open
map, Morgan-Tian Proposition 6.28, p. 117. -/
theorem stable_slice_isOpenMap (H : M14StableSet G T τ x E) :
    IsOpenMap (H.carrier.domRestrict H.endpoint_slice_map) := by
  apply IsOpenMap.of_nhds_le
  intro Z
  have hsub := H.carrier_open.isOpenEmbedding_subtypeVal.map_nhds_eq Z
  have hmap : Filter.map (H.carrier.domRestrict H.endpoint_slice_map) (𝓝 Z) =
      𝓝 (H.endpoint_slice_map Z) := by
    rw [show H.carrier.domRestrict H.endpoint_slice_map =
      H.endpoint_slice_map ∘ Subtype.val from rfl, ← Filter.map_map, hsub]
    exact (stable_slice_isLocalHomeomorphOn H).map_nhds_eq Z.property
  exact hmap.ge

/-- The actual stable endpoint chart used for change of variables in
Morgan-Tian Lemma 6.71, p. 141. -/
noncomputable def stableSliceChart (H : M14StableSet G T τ x E) :
    OpenPartialHomeomorph (G.Horizontal x) (G.slices (T - τ)).Point :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((stable_slice_endpoint_injective H).toPartialEquiv H.endpoint_slice_map H.carrier)
    H.endpoint_slice_continuous (stable_slice_isOpenMap H) H.carrier_open

/-- The stable chart has the exact frozen source, Proposition 6.28, p. 117. -/
theorem stableSliceChart_source (H : M14StableSet G T τ x E) :
    (stableSliceChart H).source = H.carrier := rfl

/-- The stable chart has the actual endpoint image as target,
Morgan-Tian Lemma 6.71, p. 141. -/
theorem stableSliceChart_target (H : M14StableSet G T τ x E) :
    (stableSliceChart H).target = H.endpoint_slice_map '' H.carrier := rfl

/-- The stable chart preserves the supplied endpoint map even outside its
source; only source values are used in Lemma 6.71, p. 141. -/
theorem stableSliceChart_apply (H : M14StableSet G T τ x E) (Z : G.Horizontal x) :
    stableSliceChart H Z = H.endpoint_slice_map Z := rfl

/-- The stable endpoint chart is smooth for the selected horizontal metric,
Morgan-Tian Proposition 6.28, p. 117. -/
theorem stableSliceChart_smooth (H : M14StableSet G T τ x E) :
    M14EndpointSliceSmooth G (stableSliceChart H) (stableSliceChart H).source :=
  H.endpoint_slice_smooth

/-- Local smooth inverses agree with the global stable inverse by
injectivity, giving the smooth inverse in Proposition 6.28, p. 117. -/
theorem stableSliceChart_symm_smooth (H : M14StableSet G T τ x E) :
    M14InverseSliceSmooth G (stableSliceChart H).symm (stableSliceChart H).target := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let e := stableSliceChart H
  change ContMDiffOn (𝓡 n) (𝓘(ℝ, G.Horizontal x)) ∞ e.symm e.target
  intro q hq
  have hZ : e.symm q ∈ H.carrier := e.map_target hq
  obtain ⟨U, V, inv, _, hV, _, hqV, hUc, _, _, _, hmap,
    _, hsmooth, _, hright⟩ := H.local_inverse (e.symm q) hZ
  change ContMDiffOn (𝓡 n) (𝓘(ℝ, G.Horizontal x)) ∞ inv V at hsmooth
  have heq : H.endpoint_slice_map (e.symm q) = q := e.right_inv hq
  rw [heq] at hqV
  have hagree : (e.symm : (G.slices (T - τ)).Point → G.Horizontal x) =ᶠ[𝓝 q] inv := by
    filter_upwards [e.open_target.mem_nhds hq, hV.mem_nhds hqV] with w hw hVw
    apply stable_slice_endpoint_injective H (e.map_target hw) (hUc (hmap w hVw))
    exact (e.right_inv hw).trans (hright w hVw).symm
  exact ((hsmooth.contMDiffAt (hV.mem_nhds hqV)).congr_of_eventuallyEq
    hagree).contMDiffWithinAt

end PoincareMT.M14
