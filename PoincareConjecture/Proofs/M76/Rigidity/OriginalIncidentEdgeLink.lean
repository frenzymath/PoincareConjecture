import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBaseSets

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem edge_dual_subset_vertex_link (p : (T.marked 2).vertices)
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 2) (hps : (p : T.index → ℝ × V3) ∈ s) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ⊆ ((T.vertexBlock p).link p).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  have hpK : {(p : T.index → ℝ × V3)} ∈ T.ambient.faces :=
    T.ambient.down_closed (T.marked_le 2 hs)
      (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty _)
  have hstar : N.closedStar p = N := (T.vertexBlock_centered_chart p).2.2.1
  change (T.ambient.barycentricDualBlock s).space ⊆ (N.link p).space
  intro x hx
  obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hx
  have hfN : f ∈ N.faces := T.ambient.barycentricDualBlock_antitone
    (Finset.singleton_subset_iff.mpr hps) hf
  have hpnot : (p : T.index → ℝ × V3) ∉ f := by
    intro hpf
    obtain ⟨u, hu, hsu, hup⟩ := hf.2 p hpf
    have he : (⟨u, hu⟩ : T.ambient.faces) = ⟨{(p : T.index → ℝ × V3)}, hpK⟩ :=
      T.ambient.faceCentroid_injective (by
        simpa only [Finset.centroid_singleton, id_eq] using hup)
    have huone : u = {(p : T.index → ℝ × V3)} := congrArg Subtype.val he
    have hle := Finset.card_le_card hsu
    rw [huone, Finset.card_singleton, hcard] at hle
    omega
  have hfst : f ∈ (N.closedStar p).faces := hstar.symm ▸ hfN
  exact (N.link p).convexHull_subset_space ⟨hfN, hpnot, hfst.2⟩ hxf

end PoincareConjecture.M76.OriginalProperDiskTriangulation
