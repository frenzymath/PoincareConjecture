import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.EdgeFaceIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.NormalArcEdgeContacts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem tetrahedral_triangle_inter_card_two
    {E : Type*} [DecidableEq E] {s u t : Finset E}
    (hst : s ⊆ t) (hut : u ⊆ t) (hs : s.card = 3) (hu : u.card = 3)
    (ht : t.card = 4) (hsu : s ≠ u) : (s ∩ u).card = 2 := by
  have hc := Finset.card_union_add_card_inter s u
  have hle := Finset.card_le_card (Finset.union_subset hst hut)
  have hint := Finset.card_le_card (Finset.inter_subset_left (s₂ := u) (s₁ := s))
  have hne : (s ∩ u).card ≠ 3 := by
    intro h
    have he : s ∩ u = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub : s ⊆ u := he ▸ Finset.inter_subset_right
    exact hsu (Finset.eq_of_subset_of_card_le hsub (by omega))
  omega

theorem physical_normal_arcs_inter_eq_rims
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s u t : Finset E} (hsK : s ∈ K.faces) (huK : u ∈ K.faces)
    (hst : s ⊆ t) (hut : u ⊆ t) (hs3 : s.card = 3) (hu3 : u.card = 3)
    (ht4 : t.card = 4) (hsu : s ≠ u)
    (Q P : OpenPartialHomeomorph X V3) (A B : E →ᴬ[ℝ] V3)
    (hmapQ : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hmapP : MapsTo g (convexHull ℝ (u : Set E)) P.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (hB : EqOn (P ∘ g) B (convexHull ℝ (u : Set E)))
    {d f r q : Set V3} (hd : d ⊆ Q.target) (hf : f ⊆ P.target)
    (hds : Q.symm '' d ⊆ g '' convexHull ℝ (s : Set E))
    (hfu : P.symm '' f ⊆ g '' convexHull ℝ (u : Set E))
    (hr : r = d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))))
    (hq : q = f ∩ intrinsicFrontier ℝ (convexHull ℝ (B '' (u : Set E)))) :
    (Q.symm '' d) ∩ (P.symm '' f) = (Q.symm '' r) ∩ (P.symm '' q) := by
  have hcard := tetrahedral_triangle_inter_card_two hst hut hs3 hu3 ht4 hsu
  apply Subset.antisymm
  · rintro x ⟨hxd, hxf⟩
    obtain ⟨y, hy, hyx⟩ := hds hxd
    obtain ⟨z, hz, hzx⟩ := hfu hxf
    have hzy : z = y := hgi (K.convexHull_subset_space huK hz)
      (K.convexHull_subset_space hsK hy) (hzx.trans hyx.symm)
    have hyedge : y ∈ convexHull ℝ ((s ∩ u : Finset E) : Set E) := by
      rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hsK huK]
      exact ⟨hy, hzy ▸ hz⟩
    have hxedge : x ∈ g '' convexHull ℝ ((s ∩ u : Finset E) : Set E) := ⟨y, hyedge, hyx⟩
    have hxQ := original_edge_chart_mem_triangle_frontier K g hgi hsK hs3 Q A
      hmapQ hA Finset.inter_subset_left hcard hxedge
    have hxP := original_edge_chart_mem_triangle_frontier K g hgi huK hu3 P B
      hmapP hB Finset.inter_subset_right hcard hxedge
    obtain ⟨v, hv, hvx⟩ := hxd
    obtain ⟨w, hw, hwx⟩ := hxf
    have hQx : Q x = v := hvx ▸ Q.right_inv (hd hv)
    have hPx : P x = w := hwx ▸ P.right_inv (hf hw)
    exact ⟨⟨v, hr.symm ▸ ⟨hv, hQx ▸ hxQ⟩, hvx⟩,
      ⟨w, hq.symm ▸ ⟨hw, hPx ▸ hxP⟩, hwx⟩⟩
  · exact inter_subset_inter (image_mono (hr ▸ inter_subset_left))
      (image_mono (hq ▸ inter_subset_left))

end PoincareConjecture.M76
