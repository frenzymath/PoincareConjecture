import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualBlocks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem barycentricDualBlock_link_faces {s : Finset E} (hs : s ∈ K.faces)
    (f : Finset E) :
    f ∈ ((K.barycentricDualBlock s).link (s.centroid ℝ id)).faces ↔
      ∃ a : Finset (K.faceLink s).faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
        f = a.image (fun u => (s ∪ u.val).centroid ℝ id) := by
  classical
  let d : (K.faceLink s).faces → E := fun u => (s ∪ u.val).centroid ℝ id
  constructor
  · intro hf
    obtain ⟨b, hb, hchain, hfb⟩ :=
      (K.barycentricSubdivision_faces f).mp hf.1.1
    have hall (i : K.faces) (hi : i ∈ b) : s ⊆ i.val := by
      obtain ⟨t, ht, hst, hti⟩ := hf.1.2 _
        (hfb.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have he' : (⟨t, ht⟩ : K.faces) = i := K.faceCentroid_injective hti
      have he : t = i.val := congrArg Subtype.val he'
      exact he ▸ hst
    have herase (i : K.faces) (hi : i ∈ b) : i.val \ s ∈ (K.faceLink s).faces := by
      have hnot : i.val ≠ s := by
        intro h
        apply hf.2.1
        rw [hfb]
        exact Finset.mem_image.mpr ⟨i, hi, congrArg (fun t => t.centroid ℝ id) h⟩
      have hne : (i.val \ s).Nonempty := Finset.sdiff_nonempty.mpr
        (fun h => hnot (Finset.Subset.antisymm h (hall i hi)))
      refine ⟨K.down_closed i.property Finset.sdiff_subset hne,
        Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx), ?_⟩
      simpa only [Finset.union_sdiff_of_subset (hall i hi)] using i.property
    let er : b → (K.faceLink s).faces := fun i => ⟨i.val.val \ s, herase i.val i.property⟩
    have hcenter (i : b) : d (er i) = i.val.val.centroid ℝ id := by
      dsimp only [d, er]
      rw [Finset.union_sdiff_of_subset (hall i.val i.property)]
    refine ⟨b.attach.image er, hb.attach.image er, ?_, ?_⟩
    · intro i hi j hj
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
      rcases hchain u.val u.property v.val v.property with h | h
      · exact Or.inl (Finset.sdiff_subset_sdiff h Subset.rfl)
      · exact Or.inr (Finset.sdiff_subset_sdiff h Subset.rfl)
    · change f = (b.attach.image er).image d
      rw [hfb]
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
        refine Finset.mem_image.mpr ⟨er ⟨i, hi⟩,
          Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
        exact (hcenter ⟨i, hi⟩).trans hix
      · intro hx
        obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_image.mpr ⟨i.val, i.property, (hcenter i).symm.trans hjx⟩
  · rintro ⟨a, ha, hchain, rfl⟩
    let ins : (K.faceLink s).faces → K.faces := fun u => ⟨s ∪ u.val, u.property.2.2⟩
    have hins (i j : (K.faceLink s).faces) (hij : i ≤ j) : ins i ≤ ins j :=
      Finset.union_subset_union Subset.rfl hij
    have hfaces (b : Finset K.faces) (hb : b.Nonempty)
        (hbc : ∀ i ∈ b, ∀ j ∈ b, i ≤ j ∨ j ≤ i)
        (hbs : ∀ i ∈ b, s ⊆ i.val) :
        b.image (fun i => i.val.centroid ℝ id) ∈ (K.barycentricDualBlock s).faces := by
      refine ⟨(K.barycentricSubdivision_faces _).mpr ⟨b, hb, hbc, rfl⟩, ?_⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i.val, i.property, hbs i hi, rfl⟩
    have hbase : a.image d ∈ (K.barycentricDualBlock s).faces := by
      have hb := hfaces (a.image ins) (ha.image ins) (by
        intro i hi j hj
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
        exact (hchain u hu v hv).imp (hins u v) (hins v u)) (by
        intro i hi
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.subset_union_left)
      simpa only [Finset.image_image, Function.comp_def, ins, d] using hb
    have hjoin : insert (s.centroid ℝ id) (a.image d) ∈
        (K.barycentricDualBlock s).faces := by
      have hb := hfaces (insert ⟨s, hs⟩ (a.image ins)) (Finset.insert_nonempty _ _) (by
        intro i hi j hj
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Or.inl le_rfl
          · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hj
            exact Or.inl Finset.subset_union_left
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
            exact Or.inr Finset.subset_union_left
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
            exact (hchain u hu v hv).imp (hins u v) (hins v u)) (by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Subset.rfl
        · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
          exact Finset.subset_union_left)
      simpa only [Finset.image_insert, Finset.image_image, Function.comp_def, ins, d] using hb
    refine ⟨hbase, ?_, hjoin⟩
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have he' : ins i = ⟨s, hs⟩ := K.faceCentroid_injective hi
    have he : s ∪ i.val = s := congrArg Subtype.val he'
    obtain ⟨x, hx⟩ := (K.faceLink s).nonempty_of_mem_faces i.property
    exact Finset.disjoint_left.mp i.property.2.1
      (he ▸ Finset.mem_union_right s hx) hx

variable [FiniteDimensional ℝ E]

theorem exists_finitePL_barycentricDualLink {s : Finset E} (hs : s ∈ K.faces) :
    ∃ (f : E → E)
      (e : (K.faceLink s).space ≃ₜ
        ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space),
      e.IsFinitePL ∧
      (∀ t ∈ (K.faceLink s).faces,
        f (t.centroid ℝ id) = (s ∪ t).centroid ℝ id) ∧
      ∀ x, (e x : E) = f x := by
  classical
  let L := K.faceLink s
  let : Fintype L.faces := (finite_faceLink_faces (Set.toFinite K.faces) s).fintype
  let M := L.barycentricSubdivision
  let N := (K.barycentricDualBlock s).link (s.centroid ℝ id)
  let p : L.faces → E := fun u => u.val.centroid ℝ id
  let q : L.faces → E := fun u => (s ∪ u.val).centroid ℝ id
  have hp : Function.Injective p := L.faceCentroid_injective
  have hq : Function.Injective q := by
    intro i j hij
    have he' : (⟨s ∪ i.val, i.property.2.2⟩ : K.faces) =
        ⟨s ∪ j.val, j.property.2.2⟩ := K.faceCentroid_injective hij
    have he : s ∪ i.val = s ∪ j.val := congrArg Subtype.val he'
    apply Subtype.ext
    have hdiff := congrArg (fun t : Finset E => t \ s) he
    simpa only [Finset.union_sdiff_cancel_left i.property.2.1,
      Finset.union_sdiff_cancel_left j.property.2.1] using hdiff
  let v : E → E := Function.extend p q (fun _ => 0)
  let w : E → E := Function.extend q p (fun _ => 0)
  have hv (i : L.faces) : v (p i) = q i := hp.extend_apply q _ i
  have hw (i : L.faces) : w (q i) = p i := hq.extend_apply p _ i
  have hM (f : Finset E) : f ∈ M.faces ↔
      ∃ a : Finset L.faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧ f = a.image p :=
    L.barycentricSubdivision_faces f
  have hN (f : Finset E) : f ∈ N.faces ↔
      ∃ a : Finset L.faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧ f = a.image q :=
    K.barycentricDualBlock_link_faces hs f
  have hMv : M.vertices = range p := by
    ext x
    rw [L.mem_barycentricSubdivision_vertices_iff]
    exact ⟨fun ⟨t, ht, htx⟩ => ⟨⟨t, ht⟩, htx⟩,
      fun ⟨t, htx⟩ => ⟨t.val, t.property, htx⟩⟩
  have hNv : N.vertices = range q := by
    ext x
    change {x} ∈ N.faces ↔ _
    rw [hN]
    constructor
    · rintro ⟨a, ha, _, heq⟩
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, Finset.mem_singleton.mp (heq.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩
    · rintro ⟨i, rfl⟩
      refine ⟨{i}, Finset.singleton_nonempty i, ?_, by simp⟩
      intro j hj k hk
      have hj' := Finset.mem_singleton.mp hj
      have hk' := Finset.mem_singleton.mp hk
      exact Or.inl (hj'.trans hk'.symm).le
  obtain ⟨f, _, H, hf, _, hfv, _, hH, _⟩ :=
    M.exists_homeomorph_of_vertex_maps N L.barycentricSubdivision_finite v w (by
      intro t ht
      obtain ⟨a, ha, hchain, rfl⟩ := (hM t).mp ht
      refine ⟨a.image q, (hN _).mpr ⟨a, ha, hchain, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨i, hi, (hv i).symm⟩) (by
      intro t ht
      obtain ⟨a, ha, hchain, rfl⟩ := (hN t).mp ht
      refine ⟨a.image p, (hM _).mpr ⟨a, ha, hchain, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨i, hi, (hw i).symm⟩) (by
      intro x hx
      obtain ⟨i, rfl⟩ := hMv.subset hx
      rw [hv, hw]) (by
      intro x hx
      obtain ⟨i, rfl⟩ := hNv.subset hx
      rw [hw, hv])
  have hspace : M.space = L.space := L.barycentricSubdivision_isSubdivision.space_eq
  let e := (Homeomorph.setCongr hspace.symm).trans H
  have heval (x : L.space) : (e x : E) = f x := hH ⟨x, hspace.symm ▸ x.property⟩
  refine ⟨f, e, ⟨f, ⟨M, L.barycentricSubdivision_finite, hspace, hf⟩, heval⟩, ?_, heval⟩
  intro t ht
  exact (hfv (hMv.symm.subset (mem_range_self (⟨t, ht⟩ : L.faces)))).trans (hv ⟨t, ht⟩)

end Geometry.SimplicialComplex
