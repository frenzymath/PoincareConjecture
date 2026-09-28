import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.LocallyPathConnected

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace OpenPartialHomeomorph

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_relative_path_connected_nhds_of_affine_nonneg
    (H : OpenPartialHomeomorph X E) {R : Set X} (ell : E →ᴬ[ℝ] ℝ)
    (hhalf : ∀ y ∈ H.source, y ∈ R ↔ 0 ≤ ell (H y))
    (x : R) (hxH : (x : X) ∈ H.source) {N : Set R} (hN : N ∈ 𝓝 x) :
    ∃ V : Set R, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧ V ⊆ N := by
  obtain ⟨W, hW, hWN⟩ := (mem_nhds_subtype R x N).mp hN
  obtain ⟨U, hUW, hU, hxU⟩ := mem_nhds_iff.mp hW
  have hopen : IsOpen (H.target ∩ H.symm ⁻¹' U) := H.isOpen_inter_preimage_symm hU
  have hxmodel : H x ∈ H.target ∩ H.symm ⁻¹' U :=
    ⟨H.map_source hxH, by
      change H.symm (H x) ∈ U
      rw [H.left_inv hxH]
      exact hxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (H x) hxmodel
  let T : Set E := ball (H x) r ∩ (ell : E → ℝ) ⁻¹' Ici 0
  have hTtarget : T ⊆ H.target := fun _ hz => (hball hz.1).1
  have hTconn : IsPathConnected T :=
    ((convex_ball (H x) r).inter
      (Convex.affine_preimage ell.toAffineMap (convex_Ici (0 : ℝ)))).isPathConnected
        ⟨H x, mem_ball_self hr, (hhalf x hxH).mp x.property⟩
  let V : Set R := (Subtype.val : R → X) ⁻¹'
    (H.source ∩ H ⁻¹' ball (H x) r)
  have hV : IsOpen V :=
    (H.isOpen_inter_preimage isOpen_ball).preimage continuous_subtype_val
  have himage : (Subtype.val : R → X) '' V = H.symm '' T := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨H z, ⟨hz.2, (hhalf z hz.1).mp z.property⟩, H.left_inv hz.1⟩
    · rintro y ⟨z, hz, rfl⟩
      have hzH := hTtarget hz
      have hyR : H.symm z ∈ R := by
        apply (hhalf _ (H.map_target hzH)).mpr
        rw [H.right_inv hzH]
        exact hz.2
      refine ⟨⟨H.symm z, hyR⟩, ?_, rfl⟩
      change H.symm z ∈ H.source ∧ H (H.symm z) ∈ ball (H x) r
      exact ⟨H.map_target hzH, by rw [H.right_inv hzH]; exact hz.1⟩
  have hVconn : IsPathConnected V := by
    apply Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
    rw [himage]
    exact hTconn.image' (H.symm.continuousOn.mono hTtarget)
  refine ⟨V, hV, ⟨hxH, mem_ball_self hr⟩, hVconn, ?_⟩
  intro y hy
  apply hWN
  apply hUW
  have h := (hball hy.2).2
  simpa only [mem_preimage, H.left_inv hy.1] using h

end OpenPartialHomeomorph

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.locallyPathConnectedSpace
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : PLDomain e R) : LocallyPathConnectedSpace R := by
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_self]
  intro N hN
  have hlocal : ∃ V : Set R, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧ V ⊆ N := by
    by_cases hxB : (x : X) ∈ frontier R
    · obtain ⟨ell, v, H, _, hxH, _, _, hhalf⟩ := hR.halfspace x hxB
      exact H.exists_relative_path_connected_nhds_of_affine_nonneg ell hhalf x hxH hN
    · have hxR : (x : X) ∈ interior R :=
        (mem_interior_iff_notMem_frontier x.property).mpr hxB
      obtain ⟨j, hxj⟩ := hR.cover x
      let H := (e j).restrOpen (interior R) isOpen_interior
      let ell : V3 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ V3 0
      have hhalf : ∀ y ∈ H.source, y ∈ R ↔ 0 ≤ ell (H y) := by
        intro y hy
        exact iff_of_true (interior_subset hy.2) le_rfl
      exact H.exists_relative_path_connected_nhds_of_affine_nonneg ell hhalf x
        ⟨hxj, hxR⟩ hN
  obtain ⟨V, hV, hxV, hconn, hVN⟩ := hlocal
  exact ⟨V, hV.mem_nhds hxV, hconn, hVN⟩

end PoincareConjecture.M76
