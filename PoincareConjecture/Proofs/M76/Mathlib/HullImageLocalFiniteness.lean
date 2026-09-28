import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHullImage
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false

open Set Topology

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem local_faces_hullImage (K : SimplicialComplex ℝ E)
    (e : OpenPartialHomeomorph E F) (hsource : K.space ⊆ e.source)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ ((↑) : ↥(e '' (s : Set E)) → F))
    (hhull : ∀ s ∈ K.faces,
      e '' convexHull ℝ (s : Set E) = convexHull ℝ (e '' (s : Set E)))
    (hK : ∀ x ∈ K.space, ∃ U ∈ 𝓝 x,
      {s : K.faces | (convexHull ℝ (s.val : Set E) ∩ U).Nonempty}.Finite) :
    ∀ y ∈ (K.hullImage e (e.injOn.mono hsource) hind hhull).space, ∃ V ∈ 𝓝 y,
      {t : (K.hullImage e (e.injOn.mono hsource) hind hhull).faces |
        (convexHull ℝ (t.val : Set F) ∩ V).Nonempty}.Finite := by
  classical
  intro y hy
  rw [K.hullImage_space] at hy
  obtain ⟨x, hxK, rfl⟩ := hy
  obtain ⟨U, hxU, hU⟩ := hK x hxK
  have hx := hsource hxK
  have hy := e.map_source hx
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (e x) :=
    (e.continuousAt_symm hy).preimage_mem_nhds (by simpa only [e.left_inv hx] using hxU)
  refine ⟨e.target ∩ e.symm ⁻¹' U,
    Filter.inter_mem (e.open_target.mem_nhds hy) hpre, ?_⟩
  have hfinite := hU.image (fun s : K.faces => s.val.image e)
  apply (hfinite.preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
  intro t ht
  have htface := (K.hullImage_faces e (e.injOn.mono hsource) hind hhull).subset t.property
  obtain ⟨s, hs, he⟩ := htface
  refine ⟨⟨s, hs⟩, ?_, he⟩
  obtain ⟨z, hzT, hzV⟩ := ht
  change s.image e = t.val at he
  rw [← he, Finset.coe_image, ← hhull s hs] at hzT
  obtain ⟨w, hw, hwz⟩ := hzT
  refine ⟨w, hw, ?_⟩
  have hwsource := hsource (K.convexHull_subset_space hs hw)
  simpa only [mem_preimage, ← hwz, e.left_inv hwsource] using hzV.2

end Geometry.SimplicialComplex
