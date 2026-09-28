import PoincareConjecture.Proofs.M76.Mathlib.InfiniteDerivedSubdivision
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false

open Set Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K D : SimplicialComplex ℝ E} {c : Finset E → E}

theorem finite_center_chain_faces_meeting
    (hc : ∀ s ∈ K.faces, c s ∈ convexHull ℝ (s : Set E))
    (hD : ∀ t ∈ D.faces, ∃ a : Finset (Finset E), a.Nonempty ∧
      (∀ s ∈ a, s ∈ K.faces) ∧ (∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s) ∧ t = a.image c)
    {U : Set E}
    (hU : {s : K.faces | (convexHull ℝ (s.val : Set E) ∩ U).Nonempty}.Finite) :
    {t : D.faces | (convexHull ℝ (t.val : Set E) ∩ U).Nonempty}.Finite := by
  classical
  have hfinite := hU.biUnion fun s _ =>
    (s.val.powerset.powerset.image (fun a : Finset (Finset E) => a.image c)).finite_toSet
  apply (hfinite.preimage (f := (Subtype.val : D.faces → Finset E))
    Subtype.val_injective.injOn).subset
  intro t ht
  obtain ⟨a, ha, hfaces, hchain, he⟩ := hD t.val t.property
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  have ham (s : Finset E) (hs : s ∈ a) : s ⊆ m := by
    rcases hchain s hs m hm with h | h
    · exact h
    · exact hmax hs h
  have hsub : convexHull ℝ (t.val : Set E) ⊆ convexHull ℝ (m : Set E) := by
    rw [he]
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact convexHull_mono (ham s hs) (hc s (hfaces s hs))
  refine mem_iUnion₂.mpr ⟨⟨m, hfaces m hm⟩, ?_, ?_⟩
  · obtain ⟨x, hxt, hxU⟩ := ht
    exact ⟨x, hsub hxt, hxU⟩
  · exact Finset.mem_image.mpr ⟨a,
      Finset.mem_powerset.mpr (fun s hs => Finset.mem_powerset.mpr (ham s hs)), he.symm⟩

theorem locallyFinite_center_chain_faces
    (hc : ∀ s ∈ K.faces, c s ∈ convexHull ℝ (s : Set E))
    (hD : ∀ t ∈ D.faces, ∃ a : Finset (Finset E), a.Nonempty ∧
      (∀ s ∈ a, s ∈ K.faces) ∧ (∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s) ∧ t = a.image c)
    (hK : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E))) :
    LocallyFinite (fun t : D.faces => convexHull ℝ (t.val : Set E)) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hK x
  exact ⟨U, hxU, finite_center_chain_faces_meeting hc hD hU⟩

end Geometry.SimplicialComplex
