import Mathlib.Topology.Connected.Clopen



set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

theorem isPreconnected_closed_of_preconnected_frontier
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {B : Set X}
    (hB : IsClosed B) (hfront : IsPreconnected (frontier B)) : IsPreconnected B := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcover hBU hBV
  by_contra hmeet
  have hdis : Disjoint (B ∩ U) (B ∩ V) := by
    apply disjoint_left.mpr
    exact fun x hx hy => hmeet ⟨x, hx.1, hx.2, hy.2⟩
  have hfrontB : frontier B ⊆ B := hB.frontier_subset
  have hside (U V : Set X) (hU : IsClosed U) (hV : IsClosed V)
      (hcover : B ⊆ U ∪ V) (hBU : (B ∩ U).Nonempty) (hBV : (B ∩ V).Nonempty)
      (hdis : Disjoint (B ∩ U) (B ∩ V))
      (hno : ¬ (frontier B ∩ V).Nonempty) : False := by
    have heq : B ∩ V = interior B ∩ Uᶜ := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, fun hu => disjoint_left.mp hdis ⟨hx.1, hu⟩ hx⟩
        exact not_not.mp ((mem_frontier_iff_notMem_interior hx.1).not.mp
          (fun hf => hno ⟨x, hf, hx.2⟩))
      · intro hx
        exact ⟨interior_subset hx.1, (hcover (interior_subset hx.1)).resolve_left hx.2⟩
    have hclopen : IsClopen (B ∩ V) :=
      ⟨hB.inter hV, heq ▸ isOpen_interior.inter hU.isOpen_compl⟩
    have hall := hclopen.eq_univ hBV
    obtain ⟨x, hx⟩ := hBU
    exact disjoint_left.mp hdis hx (hall.symm ▸ mem_univ x)
  by_cases hv : (frontier B ∩ V).Nonempty
  · have hu : ¬ (frontier B ∩ U).Nonempty := by
      intro hu
      obtain ⟨x, hx, hxU, hxV⟩ := isPreconnected_closed_iff.mp hfront U V hU hV
        (hfrontB.trans hcover) hu hv
      exact hmeet ⟨x, hfrontB hx, hxU, hxV⟩
    exact hside V U hV hU (union_comm U V ▸ hcover) hBV hBU hdis.symm hu
  · exact hside U V hU hV hcover hBU hBV hdis hv

theorem isPreconnected_compl_of_preconnected_frontier
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {O : Set X}
    (hO : IsOpen O) (hfront : IsPreconnected (frontier O)) : IsPreconnected Oᶜ := by
  apply isPreconnected_closed_of_preconnected_frontier hO.isClosed_compl
  rwa [frontier_compl]

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
