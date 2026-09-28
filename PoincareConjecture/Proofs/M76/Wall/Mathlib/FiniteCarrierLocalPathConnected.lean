import PoincareConjecture.Proofs.M76.Mathlib.MinimalFaceRadialTransport
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.LocallyPathConnected











set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_open_pathConnected_nhds_of_finite
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (x : K.space) {N : Set K.space} (hN : N ∈ 𝓝 x) :
    ∃ V : Set K.space, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧ V ⊆ N := by
  obtain ⟨O, hO, hxO, hfaces⟩ := K.exists_open_face_hulls_contain_point hK x
  obtain ⟨W, hW, hWN⟩ := (mem_nhds_subtype K.space x N).mp hN
  obtain ⟨U, hUW, hU, hxU⟩ := _root_.mem_nhds_iff.mp hW
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hO.inter hU) x ⟨hxO, hxU⟩
  let T : Set E := K.space ∩ ball (x : E) r
  have hTstar : StarConvex ℝ (x : E) T := by
    apply starConvex_iff_segment_subset.mpr
    intro y hy z hz
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy.1
    have hxs := hfaces s hs ⟨y, hys, (hball hy.2).1⟩
    exact ⟨K.convexHull_subset_space hs
      ((convex_convexHull ℝ _).segment_subset hxs hys hz),
      (convex_ball (x : E) r).segment_subset (mem_ball_self hr) hy.2 hz⟩
  have hT : IsPathConnected T := hTstar.isPathConnected ⟨x.property, mem_ball_self hr⟩
  let V : Set K.space := (Subtype.val : K.space → E) ⁻¹' ball (x : E) r
  have hV : IsOpen V := isOpen_ball.preimage continuous_subtype_val
  have himage : (Subtype.val : K.space → E) '' V = T := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · intro hy
      exact ⟨⟨y, hy.1⟩, hy.2, rfl⟩
  have hVconn : IsPathConnected V := by
    apply Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
    rw [himage]
    exact hT
  refine ⟨V, hV, mem_ball_self hr, hVconn, ?_⟩
  intro y hy
  exact hWN (hUW (hball hy).2)




theorem locallyPathConnectedSpace_of_finite
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    LocallyPathConnectedSpace K.space := by
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_self]
  intro N hN
  obtain ⟨V, hV, hxV, hconn, hVN⟩ :=
    K.exists_open_pathConnected_nhds_of_finite hK x hN
  exact ⟨V, hV.mem_nhds hxV, hconn, hVN⟩

end Geometry.SimplicialComplex
