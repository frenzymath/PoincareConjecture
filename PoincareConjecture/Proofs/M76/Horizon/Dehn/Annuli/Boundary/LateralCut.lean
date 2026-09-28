import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Boundary.LateralRim
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DerivedCutBoundary



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {A L : SimplicialComplex ℝ E} [Fintype A.faces]
  {n : ℕ} {p : Fin (n + 3) → E}

theorem BoundaryCircleBlockData.joint_mem_closed_complement_iff
    (D : BoundaryCircleBlockData A L p)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hLA : L ≤ A)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 2)
    (hpi : Function.Injective p)
    (hedge : ∀ j, ({p j, p (finRotate (n + 3) j)} : Finset E) ∈ L.faces)
    (j : Fin (n + 3)) (x : signedTubeSheet 0) :
    (D.joint j x : E) ∈
        (A.barycentricSubdivision.closedFaceComplement (A.barycentricNeighborhood L)).space ↔
      x.val.2 = -1 ∨ x.val.2 = 1 := by
  obtain ⟨t, ht, hne, hex, hends⟩ := D.joint_mem_endpoints_iff hpure hcofaces hpi
    (fun j ↦ hLA (hedge j)) j
  have hnext : j ≠ finRotate (n + 3) j := by
    intro heq
    have hh : (0 : Fin (n + 3)) = 1 := add_left_cancel
      (show j + 0 = j + 1 by simpa only [finRotate_apply, add_zero] using heq)
    have := congrArg Fin.val hh
    norm_num at this
  have hcut := A.marked_edge_dual_inter_closedFaceComplement L hpure hfull hLcard
    (hedge j) (Finset.card_pair (hpi.ne hnext))
  have himage : (fun s : Finset E ↦ s.centroid ℝ id) ''
      {s | s ∈ A.faces ∧ s.card = 3 ∧ ({p j, p (finRotate (n + 3) j)} : Finset E) ⊆ s} =
      ({(t false).centroid ℝ id, (t true).centroid ℝ id} : Set E) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      rcases hex s hs.1 hs.2.1 hs.2.2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨t false, ht false, rfl⟩
      · exact ⟨t true, ht true, rfl⟩
  rw [himage] at hcut
  have hmem : (D.joint j x : E) ∈
      (A.barycentricDualBlock {p j, p (finRotate (n + 3) j)}).space :=
    (D.joint j x).property
  exact ((and_iff_right hmem).symm.trans (Set.ext_iff.mp hcut _)).trans (hends x)

theorem BoundaryCircleBlockData.map_mem_closed_complement_iff
    (D : BoundaryCircleBlockData A L p)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hLA : L ≤ A)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 2)
    (hpi : Function.Injective p) (hpv : range p = L.vertices)
    (hpf : ∀ s : Finset E, s ∈ L.faces ↔ s.Nonempty ∧
      ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)})
    (hlinks : ∀ v ∈ L.vertices, IsConnected (A.link v).space)
    (j : Fin (n + 3)) (x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1)) :
    (D.map j x : E) ∈
        (A.barycentricSubdivision.closedFaceComplement (A.barycentricNeighborhood L)).space ↔
      x.val.1.2 = -1 ∨ x.val.1.2 = 1 := by
  classical
  let next := finRotate (n + 3)
  have hpL (k : Fin (n + 3)) : p k ∈ L.vertices := hpv ▸ mem_range_self k
  have hpA (k : Fin (n + 3)) : p k ∈ A.vertices := hLA (hpL k)
  have hedge (k : Fin (n + 3)) : ({p k, p (next k)} : Finset E) ∈ L.faces :=
    (hpf _).mpr ⟨Finset.insert_nonempty _ _, k, subset_rfl⟩
  by_cases hzero : x.val.2 = 0
  · have hx : x = ⟨(x.val.1, 0), x.property.1, le_rfl, zero_le_one⟩ :=
      Subtype.ext (Prod.ext rfl hzero)
    have hv := D.lower j ⟨x.val.1, x.property.1⟩
    have hm : (D.map j x : E) = D.joint ((finRotate (n + 3)).symm j)
        ⟨x.val.1, x.property.1⟩ :=
      (congrArg (fun y ↦ (D.map j y : E)) hx).trans hv
    rw [hm]
    exact D.joint_mem_closed_complement_iff hpure hcofaces hLA hfull hLcard hpi hedge _ _
  by_cases hone : x.val.2 = 1
  · have hx : x = ⟨(x.val.1, 1), x.property.1, zero_le_one, le_rfl⟩ :=
      Subtype.ext (Prod.ext rfl hone)
    have hv := D.upper j ⟨x.val.1, x.property.1⟩
    have hm : (D.map j x : E) = D.joint j ⟨x.val.1, x.property.1⟩ :=
      (congrArg (fun y ↦ (D.map j y : E)) hx).trans hv
    rw [hm]
    exact D.joint_mem_closed_complement_iff hpure hcofaces hLA hfull hLcard hpi hedge _ _
  have hrim := D.map_mem_vertex_rim_iff hpure hcofaces hpA
    (fun k ↦ hlinks _ (hpL k)) j x
  constructor
  · intro hcut
    obtain ⟨u, hu, hdu⟩ := mem_iUnion₂.mp
      ((A.vertex_dual_inter_closedFaceComplement L hpure (p j)).subset
        ⟨(D.map j x).property, hcut⟩)
    have hne : p j ≠ u := fun heq ↦ hu.2 (heq ▸ hpL j)
    have hlink := (A.dualEdge_space_subset_vertex_links (hpA j) hu.1 hne hdu).1
    rcases hrim.mp hlink with hm | hp | h0 | h1
    · exact Or.inl hm
    · exact Or.inr hp
    · exact False.elim (hzero h0)
    · exact False.elim (hone h1)
  · intro hxside
    have hlink := hrim.mpr (hxside.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
    rw [A.barycentric_vertex_link_space_eq_iUnion_dualEdges (hpA j)] at hlink
    obtain ⟨u, hu, hdu⟩ := mem_iUnion₂.mp hlink
    have huA : u ∈ A.vertices := A.face_subset_vertices hu.2
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    by_cases huL : u ∈ L.vertices
    · have hpairL : ({p j, u} : Finset E) ∈ L.faces := hfull _ hu.2 (by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hpL j
        · exact Finset.mem_singleton.mp hv ▸ huL)
      obtain ⟨k, hsub⟩ := ((hpf _).mp hpairL).2
      have hpj : p j ∈ ({p k, p (next k)} : Finset E) :=
        hsub (Finset.mem_insert_self _ _)
      have heq : ({p j, u} : Finset E) = {p k, p (next k)} :=
        Finset.eq_of_subset_of_card_le hsub (by
          rw [Finset.card_pair hu.1.symm]
          simpa only [Finset.card_singleton] using Finset.card_insert_le (p k) {p (next k)})
      have hJ : (D.map j x : E) ∈ (A.barycentricDualBlock {p k, p (next k)}).space :=
        heq ▸ hdu
      let z := (D.joint k).symm ⟨D.map j x, hJ⟩
      have hz : (D.joint k z : E) = D.map j x :=
        congrArg Subtype.val ((D.joint k).apply_symm_apply _)
      rcases Finset.mem_insert.mp hpj with hjk | hjk
      · have hjk := hpi hjk
        subst k
        have hx : x = ⟨(z, 1), z.property, zero_le_one, le_rfl⟩ := by
          apply (D.map j).injective
          exact Subtype.ext (hz.symm.trans (D.upper j z).symm)
        exact False.elim (hone (congrArg
          (fun y : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ↦ y.val.2) hx))
      · have hjk := hpi (Finset.mem_singleton.mp hjk)
        have hk : k = next.symm j := (next.eq_symm_apply).mpr hjk.symm
        have hx : x = ⟨(z, 0), z.property, le_rfl, zero_le_one⟩ := by
          apply (D.map j).injective
          apply Subtype.ext
          exact hz.symm.trans ((hk ▸ D.lower j z).symm)
        exact False.elim (hzero (congrArg
          (fun y : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ↦ y.val.2) hx))
    · exact ((A.vertex_dual_inter_closedFaceComplement L hpure (p j)).symm.subset
        (mem_iUnion₂.mpr ⟨u, ⟨huA, huL⟩, hdu⟩)).2

end PoincareConjecture.M76.Dehn
