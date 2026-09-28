import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.Orientation.BoundaryVertexTransport
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryIncidence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns

set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Dehn Dehn.Annuli

open Classical in
theorem exists_one_boundary_cap_geometric_signs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (J : SimplicialComplex ℝ (E × ℝ))
    (hK : K.faces.Finite) (hLK : L ≤ K)
    (hfaces : ∀ s, s ∈ J.faces ↔
      (∃ t ∈ K.faces, s = t.image (fun x => (x, (0 : ℝ)))) ∨ s = {(0, 1)} ∨
        ∃ t ∈ L.faces, s = insert (0, 1) (t.image (fun x => (x, (0 : ℝ)))))
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hboundary : ∀ s ∈ L.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 1)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1) :
    ∃ (label : E × ℝ → ℕ) (sigma : Finset (E × ℝ) → ZMod 2),
      InjOn label J.vertices ∧
      ∀ t ∈ J.faces, t.card = 3 → ∀ u ∈ J.faces, u.card = 3 → t ≠ u →
        ∀ s : Finset (E × ℝ), s.card = 2 → s ⊆ t → s ⊆ u →
          (sigma t + boundaryFaceParity label t s) +
            (sigma u + boundaryFaceParity label u s) = 1 := by
  classical
  let z : E → E × ℝ := fun x => (x, 0)
  let apex : E × ℝ := (0, 1)
  have hzi : Function.Injective z := fun _ _ h => congrArg Prod.fst h
  have haz (x : E) : apex ≠ z x := fun h => one_ne_zero (congrArg Prod.snd h)
  have hanot (s : Finset E) : apex ∉ s.image z := by
    rintro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
    exact haz x hx.symm
  have hcard (s : Finset E) : (s.image z).card = s.card :=
    Finset.card_image_iff.mpr hzi.injOn
  obtain ⟨N, hN⟩ := ((K.finite_vertices_of_finite_faces hK).image number).bddAbove
  let label : E × ℝ → ℕ := fun y => if y.2 = 0 then number y.1 else N + 1
  have hlabelz (x : E) : label (z x) = number x := by simp [label, z]
  have hlabela : label apex = N + 1 := by simp [label, apex]
  have hlabelaz (x : E) (hx : x ∈ K.vertices) : label apex ≠ label (z x) := by
    rw [hlabela, hlabelz]
    have hb := hN (mem_image_of_mem number hx)
    omega
  have hvertices (y : E × ℝ) (hy : y ∈ J.vertices) :
      y = apex ∨ ∃ x ∈ K.vertices, y = z x := by
    rcases (hfaces {y}).mp hy with ⟨t, ht, heq⟩ | heq | ⟨t, _, heq⟩
    · have hym : y ∈ t.image z := heq ▸ Finset.mem_singleton_self y
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hym
      exact Or.inr ⟨x, K.down_closed ht (Finset.singleton_subset_iff.mpr hx)
        (Finset.singleton_nonempty _), hxy.symm⟩
    · exact Or.inl (Finset.singleton_injective heq)
    · have ha : apex ∈ ({y} : Finset (E × ℝ)) := heq.symm ▸ Finset.mem_insert_self _ _
      exact Or.inl (Finset.mem_singleton.mp ha).symm
  have hlabel : InjOn label J.vertices := by
    intro x hx y hy heq
    rcases hvertices x hx with rfl | ⟨a, ha, rfl⟩ <;>
      rcases hvertices y hy with rfl | ⟨b, hb, rfl⟩
    · rfl
    · exact (hlabelaz b hb heq).elim
    · exact (hlabelaz a ha heq.symm).elim
    · exact congrArg z (hnumber ha hb (by simpa only [hlabelz] using heq))
  have hparity (s t : Finset E) :
      boundaryFaceParity label (s.image z) (t.image z) = boundaryFaceParity number s t := by
    let emb : E ↪ E × ℝ := ⟨z, hzi⟩
    have h := boundaryFaceParity_map emb label s t
    simpa only [Finset.map_eq_image, emb, Function.Embedding.coeFn_mk,
      Function.comp_def, hlabelz] using h
  have hordered (s : Finset E) (a b : E) :
      orderedCofaceParity label (s.image z) (z a) (z b) =
        orderedCofaceParity number s a b := by
    unfold orderedCofaceParity
    have hpair : ({z a, z b} : Finset (E × ℝ)) = ({a, b} : Finset E).image z := by simp
    rw [hpair, hparity, hlabelz, hlabelz]
  have hex (s : Finset E) (hs : s ∈ L.faces ∧ s.card = 2) :
      ∃ t, {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ s ⊆ u} = {t} :=
    ncard_eq_one.mp (hboundary s hs.1 hs.2)
  let old (s : Finset E) : Finset E := if hs : s ∈ L.faces ∧ s.card = 2 then
    (hex s hs).choose else ∅
  have hold (s : Finset E) (hs : s ∈ L.faces) (hsc : s.card = 2) :
      old s ∈ K.faces ∧ (old s).card = 3 ∧ s ⊆ old s := by
    have h := (hex s ⟨hs, hsc⟩).choose_spec
    have hm := h.symm.subset (mem_singleton _)
    simpa only [old, dif_pos (show s ∈ L.faces ∧ s.card = 2 from ⟨hs, hsc⟩),
      mem_ofPred_eq] using hm
  have hunique (s : Finset E) (hs : s ∈ L.faces) (hsc : s.card = 2)
      (t : Finset E) (ht : t ∈ K.faces) (htc : t.card = 3) (hst : s ⊆ t) : t = old s := by
    have h := (hex s ⟨hs, hsc⟩).choose_spec
    have hm := h.subset ⟨ht, htc, hst⟩
    simpa only [old, dif_pos (show s ∈ L.faces ∧ s.card = 2 from ⟨hs, hsc⟩),
      mem_singleton_iff] using hm
  let cone (s : Finset E) := insert apex (s.image z)
  let sigma (s : Finset (E × ℝ)) : ZMod 2 :=
    if apex ∈ s then
      let b := (s.erase apex).image Prod.fst
      sign (old b) + boundaryFaceParity number (old b) b +
        boundaryFaceParity label s (b.image z) + 1
    else sign (s.image Prod.fst)
  have hsigmaOld (s : Finset E) : sigma (s.image z) = sign s := by
    simp [sigma, hanot, Finset.image_image, z, Function.comp_def]
  have hsigmaCone (s : Finset E) : sigma (cone s) =
      sign (old s) + boundaryFaceParity number (old s) s +
        boundaryFaceParity label (cone s) (s.image z) + 1 := by
    simp [sigma, cone, hanot, Finset.image_image, z, Function.comp_def]
  have hcross (s : Finset E) (hs : s ∈ L.faces) (hsc : s.card = 2)
      (t : Finset E) (ht : t ∈ K.faces) (htc : t.card = 3) (hst : s ⊆ t) :
      (sigma (t.image z) + boundaryFaceParity label (t.image z) (s.image z)) +
        (sigma (cone s) + boundaryFaceParity label (cone s) (s.image z)) = 1 := by
    rw [hsigmaOld, hparity, hsigmaCone, hunique s hs hsc t ht htc hst]
    ring_nf
    simp only [mul_two, CharTwo.add_self_eq_zero, add_zero]
  have hradial (v a : E) (hva : v ≠ a) (he : {v, a} ∈ L.faces) :
      sigma (cone {v, a}) + orderedCofaceParity label (cone {v, a}) (z v) apex =
        sign (old {v, a}) + orderedCofaceParity number (old {v, a}) v a := by
    have hec : ({v, a} : Finset E).card = 2 := by simp [hva]
    have ht := hold {v, a} he hec
    have hc := hcross {v, a} he hec _ ht.1 ht.2.1 ht.2.2
    simp only [Finset.image_insert, Finset.image_singleton] at hc
    have hco := orderedCofaceParity_cancellation label ((old {v, a}).image z)
      (cone {v, a}) (z v) (z a) _ _ hc
    rw [hsigmaOld, hordered] at hco
    have hvK : v ∈ K.vertices := K.down_closed (hLK he) (by simp) (by simp)
    have haK : a ∈ K.vertices := K.down_closed (hLK he) (by simp) (by simp)
    have hnva : label (z v) ≠ label (z a) := by
      rw [hlabelz, hlabelz]
      exact fun h => hva (hnumber hvK haK h)
    have htri := orderedCofaceParity_triangle_of_label_ne label hnva
      (hlabelaz v hvK).symm (hlabelaz a haK).symm
    have hcone : ({z v, z a, apex} : Finset (E × ℝ)) = cone {v, a} := by
      ext x
      simp only [cone, Finset.image_insert, Finset.image_singleton,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hcone] at htri
    linear_combination (norm := ring_nf) htri - hco
    simp only [mul_two, CharTwo.add_self_eq_zero]
  refine ⟨label, sigma, hlabel, ?_⟩
  intro t ht htc u hu huc htu s hsc hst hsu
  have hs : s ∈ J.faces := J.down_closed ht hst (Finset.card_pos.mp (by omega))
  rcases (hfaces s).mp hs with ⟨b, hb, rfl⟩ | rfl | ⟨b, hb, rfl⟩
  · have hbc : b.card = 2 := (hcard b).symm.trans hsc
    rcases (one_boundary_cap_base_cofaces_iff K L J hfaces b hbc t).mp ⟨ht, htc, hst⟩ with
      ⟨t0, ht0, htc0, hbt0, rfl⟩ | ⟨hbL, rfl⟩
    · rcases (one_boundary_cap_base_cofaces_iff K L J hfaces b hbc u).mp ⟨hu, huc, hsu⟩ with
        ⟨u0, hu0, huc0, hbu0, rfl⟩ | ⟨hbL, rfl⟩
      · rw [hsigmaOld, hsigmaOld, hparity, hparity]
        exact hcancel _ ht0 htc0 _ hu0 huc0 (fun h => htu (h ▸ rfl)) _ hbc hbt0 hbu0
      · exact hcross b hbL hbc t0 ht0 htc0 hbt0
    · rcases (one_boundary_cap_base_cofaces_iff K L J hfaces b hbc u).mp ⟨hu, huc, hsu⟩ with
        ⟨u0, hu0, huc0, hbu0, rfl⟩ | ⟨_, rfl⟩
      · rw [add_comm]
        exact hcross b hbL hbc u0 hu0 huc0 hbu0
      · exact (htu rfl).elim
  · simp only [Finset.card_singleton] at hsc
    omega
  · have hbc : b.card = 1 := by
      rw [Finset.card_insert_of_notMem (hanot b), hcard] at hsc
      omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hbc
    simp only [Finset.image_singleton] at hst hsu ⊢
    obtain ⟨e1, he1, hc1, hv1, rfl⟩ :=
      (one_boundary_cap_radial_cofaces_iff K L J hfaces v t).mp ⟨ht, htc, hst⟩
    obtain ⟨e2, he2, hc2, hv2, rfl⟩ :=
      (one_boundary_cap_radial_cofaces_iff K L J hfaces v u).mp ⟨hu, huc, hsu⟩
    have hpair (e : Finset E) (he : e.card = 2) (hv : v ∈ e) :
        ∃ a, v ≠ a ∧ e = {v, a} := by
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨b, hab, rfl⟩
      · have hvb : v = b := Finset.mem_singleton.mp hv
        subst v
        exact ⟨a, hab.symm, Finset.pair_comm _ _⟩
    obtain ⟨a, hva, rfl⟩ := hpair e1 hc1 hv1
    obtain ⟨b, hvb, rfl⟩ := hpair e2 hc2 hv2
    have hab : a ≠ b := fun h => htu (h ▸ rfl)
    have hsigns := boundary_coface_signs_through_vertex K hK number hnumber sign hcancel
      hva hvb hab (hLK he1) (hLK he2) (hlinks v (hLK hb))
      (old {v, a}) (old {v, b})
      (fun q hq hqc hsq => hunique _ he1 hc1 q hq hqc hsq)
      (fun q hq hqc hsq => hunique _ he2 hc2 q hq hqc hsq)
    rw [← hradial v a hva he1, ← hradial v b hvb he2] at hsigns
    simp only [orderedCofaceParity, Finset.pair_comm (z v) apex] at hsigns
    change (sigma (cone {v, a}) + boundaryFaceParity label (cone {v, a}) {apex, z v}) +
      (sigma (cone {v, b}) + boundaryFaceParity label (cone {v, b}) {apex, z v}) = 1
    linear_combination (norm := ring_nf) hsigns
    simp only [mul_two, CharTwo.add_self_eq_zero, neg_zero]

end PoincareConjecture.M76
