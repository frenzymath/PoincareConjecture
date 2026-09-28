import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

theorem mem_frontier_iff_of_open_agreement
    {X : Type*} [TopologicalSpace X] {A B U : Set X}
    (hU : IsOpen U) (hAB : ∀ y ∈ U, y ∈ A ↔ y ∈ B)
    {x : X} (hx : x ∈ U) : x ∈ frontier A ↔ x ∈ frontier B := by
  have heq : A ∩ U = B ∩ U := by
    ext y
    exact ⟨fun h => ⟨(hAB y h.2).mp h.1, h.2⟩,
      fun h => ⟨(hAB y h.2).mpr h.1, h.2⟩⟩
  have hf : frontier A ∩ U = frontier B ∩ U := by
    rw [← frontier_inter_open_inter hU, heq, frontier_inter_open_inter hU]
  exact ⟨fun h => (hf.subset ⟨h, hx⟩).1, fun h => (hf.symm.subset ⟨h, hx⟩).1⟩

theorem halfspace_of_open_agreement
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {A B U : Set X}
    (he : PLDomain e A) (hU : IsOpen U)
    (hAB : ∀ y ∈ U, y ∈ B ↔ y ∈ A)
    {x : X} (hx : x ∈ U) (hxB : x ∈ frontier B) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (G : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ x ∈ G.source ∧ ell (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ G.source, y ∈ B ↔ 0 ≤ ell (G y) := by
  have hxA := (mem_frontier_iff_of_open_agreement hU hAB hx).mp hxB
  obtain ⟨ell, v, T, hv, hxT, hz, hT, hhalf⟩ := he.halfspace x hxA
  refine ⟨ell, v, T.restrOpen U hU, hv, ⟨hxT, hx⟩, hz, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right T (hT i) hU
  · intro y hy
    exact (hAB y hy.2).trans (hhalf y hy.1)

theorem plDomain_of_two_open_agreements
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {A B N U V : Set X}
    (heA : PLDomain e A) (heB : PLDomain e B) (hN : IsClosed N)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : frontier N ⊆ U ∪ V)
    (hNA : ∀ y ∈ U, y ∈ N ↔ y ∈ A)
    (hNB : ∀ y ∈ V, y ∈ N ↔ y ∈ B) : PLDomain e N := by
  refine ⟨heA.cover, heA.compatible, hN, ?_⟩
  intro x hx
  rcases hcover hx with hxU | hxV
  · exact halfspace_of_open_agreement heA hU hNA hxU hx
  · exact halfspace_of_open_agreement heB hV hNB hxV hx

end PoincareConjecture.M76.HamiltonIntervalTorus
