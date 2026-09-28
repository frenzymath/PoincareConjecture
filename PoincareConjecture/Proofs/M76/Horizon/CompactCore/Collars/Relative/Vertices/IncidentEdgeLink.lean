import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.Blocks

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "I" => Icc (-1 : ℝ) 1

open Classical in



theorem edge_dual_subset_vertex_link (p : (T.marked 2).vertices)
    {s : Finset E} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 2) (hps : (p : E) ∈ s) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ⊆ ((T.vertexBlock p).link p).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  have hpK : {(p : E)} ∈ T.ambient.faces :=
    T.ambient.down_closed (T.marked_le 2 hs)
      (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty _)
  have hstar : N.closedStar p = N := (T.vertexBlock_chart p).2.2.1
  change (T.ambient.barycentricDualBlock s).space ⊆ (N.link p).space
  intro x hx
  obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hx
  have hfN : f ∈ N.faces := T.ambient.barycentricDualBlock_antitone
    (Finset.singleton_subset_iff.mpr hps) hf
  have hpnot : (p : E) ∉ f := by
    intro hpf
    obtain ⟨u, hu, hsu, hup⟩ := hf.2 p hpf
    have he : (⟨u, hu⟩ : T.ambient.faces) = ⟨{(p : E)}, hpK⟩ :=
      T.ambient.faceCentroid_injective (by
        simpa only [Finset.centroid_singleton, id_eq] using hup)
    have huone : u = {(p : E)} := congrArg Subtype.val he
    have hle := Finset.card_le_card hsu
    rw [huone, Finset.card_singleton, hcard] at hle
    omega
  have hfst : f ∈ (N.closedStar p).faces := hstar.symm ▸ hfN
  exact (N.link p).convexHull_subset_space ⟨hfN, hpnot, hfst.2⟩ hxf


end Geometry.SimplicialComplex.CoorientedSurfaceStars

