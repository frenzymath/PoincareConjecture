import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.InteriorSkeletonFans
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarConeFans
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.TriangleRefinementOwners

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_marked_cone_four_triangle_fan
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 2) (R T : SimplicialComplex ℝ E)
    (L C : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
    (Q : {s : K.faces // s.val.card = 2} → SimplicialComplex ℝ E)
    (hLR : ∀ s, L s ≤ R)
    (hLS : ∀ s, (L s).space = frontier (convexHull ℝ (s.val.val : Set E)))
    (hQR : ∀ s, Q s ≤ R)
    (hQS : ∀ s, (Q s).space = convexHull ℝ (s.val.val : Set E))
    (hC : ∀ s, (C s).faces.Finite)
    (hCS : ∀ s, (C s).space = convexHull ℝ (s.val.val : Set E))
    (hLC : ∀ s, L s ≤ C s)
    (hvertices : ∀ s, (C s).vertices = insert (s.val.val.centroid ℝ id) (L s).vertices)
    (hfaces : ∀ s z, z ∈ (C s).faces ↔ z.Nonempty ∧
      (z.erase (s.val.val.centroid ℝ id) = ∅ ∨
        z.erase (s.val.val.centroid ℝ id) ∈ (L s).faces))
    (hTS : T.space = K.space) (hTfaces : T.faces = ⋃ s, (C s).faces)
    (Z : Set E) (hZvertices : Disjoint K.vertices Z)
    (hZapices : ∀ s : {s : K.faces // s.val.card = 3}, s.val.val.centroid ℝ id ∉ Z)
    (hZboundary : Disjoint (frontier K.space) Z)
    {q : E} (hq : q ∈ T.vertices) (hqZ : q ∈ Z) :
    ∃ (e : {s : K.faces // s.val.card = 2})
      (s t : {s : K.faces // s.val.card = 3}) (u v : E),
      q ∈ intrinsicInterior ℝ (convexHull ℝ (e.val.val : Set E)) ∧
      s ≠ t ∧ e.val.val ⊆ s.val.val ∧ e.val.val ⊆ t.val.val ∧
      q ≠ u ∧ q ≠ v ∧ u ≠ v ∧ s.val.val.centroid ℝ id ≠ t.val.val.centroid ℝ id ∧
      {r : Finset E | r ∈ (Q e).faces ∧ r.card = 2 ∧ q ∈ r} =
        {({q, u} : Finset E), {q, v}} ∧
      ({q, s.val.val.centroid ℝ id, u} : Finset E) ∈ (C s).faces ∧
      ({q, s.val.val.centroid ℝ id, u} : Finset E).card = 3 ∧
      ({q, s.val.val.centroid ℝ id, v} : Finset E) ∈ (C s).faces ∧
      ({q, s.val.val.centroid ℝ id, v} : Finset E).card = 3 ∧
      ({q, t.val.val.centroid ℝ id, u} : Finset E) ∈ (C t).faces ∧
      ({q, t.val.val.centroid ℝ id, u} : Finset E).card = 3 ∧
      ({q, t.val.val.centroid ℝ id, v} : Finset E) ∈ (C t).faces ∧
      ({q, t.val.val.centroid ℝ id, v} : Finset E).card = 3 ∧
      {r : Finset E | r ∈ T.faces ∧ r.card = 3 ∧ q ∈ r} =
        {({q, s.val.val.centroid ℝ id, u} : Finset E), {q, s.val.val.centroid ℝ id, v},
          {q, t.val.val.centroid ℝ id, u}, {q, t.val.val.centroid ℝ id, v}} ∧
      {r : Finset E | r ∈ T.faces ∧ r.card = 3 ∧ q ∈ r}.ncard = 4 := by
  classical
  let τ := {s : K.faces // s.val.card = 3}
  have hCT (s : τ) : C s ≤ T := by
    intro r hr
    change r ∈ T.faces
    rw [hTfaces]
    exact mem_iUnion.mpr ⟨s, hr⟩
  have hqK : q ∈ K.space := hTS.subset (T.vertices_subset_space hq)
  have hqv : q ∉ K.vertices := fun h => disjoint_left.mp hZvertices h hqZ
  have hqint : q ∈ interior K.space := by
    by_contra h
    exact disjoint_left.mp hZboundary ⟨subset_closure hqK, h⟩ hqZ
  have hqskel : q ∈ ⋃ e : {s : K.faces // s.val.card = 2},
      convexHull ℝ (e.val.val : Set E) := by
    have hqface : ({q} : Finset E) ∈ ⋃ s, (C s).faces := hTfaces ▸ hq
    obtain ⟨i, hqi⟩ := mem_iUnion.mp hqface
    have hqi' : q ∈ (C i).vertices := hqi
    rw [hvertices i] at hqi'
    have hqL : q ∈ (L i).vertices := hqi'.resolve_left (fun h => hZapices i (h ▸ hqZ))
    have hqfront := (hLS i).subset ((L i).vertices_subset_space hqL)
    rw [K.triangle_frontier_eq_iUnion_erase hdim i.val.property i.property] at hqfront
    obtain ⟨p, hqp⟩ := mem_iUnion.mp hqfront
    obtain ⟨he, hecard, _⟩ := K.triangle_erase_is_edge i.val.property i.property p.property
    exact mem_iUnion.mpr ⟨⟨⟨i.val.val.erase p, he⟩, hecard⟩, hqp⟩
  obtain ⟨e, hqe, _, s, t, hst, hes, het, howners, hstars⟩ :=
    K.exists_interior_skeleton_shared_boundary_stars hK hdim R L hLR hLS Q hQR hQS
      hqskel hqv hqint
  have hcenter (i : τ) : i.val.val.centroid ℝ id ∈ interior (C i).space := by
    rw [hCS i]
    exact K.triangle_centroid_mem_interior hdim i.val.property i.property
  have hbound (i : τ) : (L i).space ⊆ frontier (C i).space := by
    rw [hLS i, hCS i]
  have hcenternot (i : τ) : i.val.val.centroid ℝ id ∉ (L i).vertices := fun h =>
    (hbound i ((L i).vertices_subset_space h)).2 (hcenter i)
  have hqdim (i : τ) : ∀ z ∈ (L i).faces, z.card ≤ 2 :=
    (L i).base_face_card_le_two_of_planar_cone (C i) hdim (hcenternot i) (hfaces i)
  have hqLi (i : τ) (hei : e.val.val ⊆ i.val.val) : q ∈ (L i).vertices := by
    have hproper : e.val.val ⊂ i.val.val := Finset.ssubset_iff_subset_ne.mpr ⟨hei, by
      intro h
      have hh := congrArg Finset.card h
      have hec := e.property
      have hic := i.property
      omega⟩
    have hqfront := intrinsicFrontier_subset_frontier
      ((K.indep i.val.property).convexHull_subset_intrinsicFrontier hproper (intrinsicInterior_subset hqe))
    obtain ⟨r, hr, hqr⟩ := mem_space_iff.mp ((hLS i).symm.subset hqfront)
    have hqr' := (T.vertex_mem_convexHull_iff hq (hCT i (hLC i hr))).mp hqr
    exact (L i).down_closed hr (Finset.singleton_subset_iff.mpr hqr') (Finset.singleton_nonempty q)
  obtain ⟨u, v, hqu, hqv', huv, hsedge, hstris, _⟩ :=
    (L s).exists_planar_cone_vertex_fan (C s) hdim (hC s) (hcenter s)
      (hbound s) (hfaces s) (hqLi s hes)
  have hQedge := (hstars s hes).symm.trans hsedge
  have htedge := (hstars t het).trans hQedge
  have httris := (L t).cone_vertex_triangle_cofaces_eq_pair (C t) (hcenternot t)
    (hqLi t het) (hfaces t) (hqdim t) htedge
  have hcne : s.val.val.centroid ℝ id ≠ t.val.val.centroid ℝ id := by
    intro heq
    have hcs := K.triangle_centroid_mem_interior hdim s.val.property s.property
    have hct := K.triangle_centroid_mem_interior hdim t.val.property t.property
    have hh := K.distinct_triangle_inter_subset_frontiers s.val.property t.val.property
      s.property t.property (fun h => hst (Subtype.ext (Subtype.ext h)))
      ⟨interior_subset hcs, heq.symm ▸ interior_subset hct⟩
    exact hh.1.2 hcs
  have hsu : ({q, s.val.val.centroid ℝ id, u} : Finset E) ∈ (C s).faces ∧
      ({q, s.val.val.centroid ℝ id, u} : Finset E).card = 3 ∧
      q ∈ ({q, s.val.val.centroid ℝ id, u} : Finset E) := by
    change _ ∈ {r : Finset E | r ∈ (C s).faces ∧ r.card = 3 ∧ q ∈ r}
    rw [hstris]
    simp
  have hsv : ({q, s.val.val.centroid ℝ id, v} : Finset E) ∈ (C s).faces ∧
      ({q, s.val.val.centroid ℝ id, v} : Finset E).card = 3 ∧
      q ∈ ({q, s.val.val.centroid ℝ id, v} : Finset E) := by
    change _ ∈ {r : Finset E | r ∈ (C s).faces ∧ r.card = 3 ∧ q ∈ r}
    rw [hstris]
    simp
  have htu : ({q, t.val.val.centroid ℝ id, u} : Finset E) ∈ (C t).faces ∧
      ({q, t.val.val.centroid ℝ id, u} : Finset E).card = 3 ∧
      q ∈ ({q, t.val.val.centroid ℝ id, u} : Finset E) := by
    change _ ∈ {r : Finset E | r ∈ (C t).faces ∧ r.card = 3 ∧ q ∈ r}
    rw [httris]
    simp
  have htv : ({q, t.val.val.centroid ℝ id, v} : Finset E) ∈ (C t).faces ∧
      ({q, t.val.val.centroid ℝ id, v} : Finset E).card = 3 ∧
      q ∈ ({q, t.val.val.centroid ℝ id, v} : Finset E) := by
    change _ ∈ {r : Finset E | r ∈ (C t).faces ∧ r.card = 3 ∧ q ∈ r}
    rw [httris]
    simp
  have hglobal : {r : Finset E | r ∈ T.faces ∧ r.card = 3 ∧ q ∈ r} =
      {({q, s.val.val.centroid ℝ id, u} : Finset E), {q, s.val.val.centroid ℝ id, v},
        {q, t.val.val.centroid ℝ id, u}, {q, t.val.val.centroid ℝ id, v}} := by
    ext r
    constructor
    · rintro ⟨hr, hrcard, hqr⟩
      rw [hTfaces] at hr
      obtain ⟨i, hri⟩ := mem_iUnion.mp hr
      have hqCi := (C i).convexHull_subset_space hri (subset_convexHull ℝ _ hqr)
      have hei := K.subset_of_mem_intrinsicInterior_face e.val.property i.val.property hqe
        ((hCS i).subset hqCi)
      rcases (howners i).mp hei with his | hit
      · subst i
        have hh : r ∈ {r : Finset E | r ∈ (C s).faces ∧ r.card = 3 ∧ q ∈ r} :=
          ⟨hri, hrcard, hqr⟩
        rw [hstris] at hh
        simp only [mem_insert_iff, mem_singleton_iff] at hh
        rcases hh with hh | hh <;> simp [hh]
      · subst i
        have hh : r ∈ {r : Finset E | r ∈ (C t).faces ∧ r.card = 3 ∧ q ∈ r} :=
          ⟨hri, hrcard, hqr⟩
        rw [httris] at hh
        simp only [mem_insert_iff, mem_singleton_iff] at hh
        rcases hh with hh | hh <;> simp [hh]
    · intro hr
      simp only [mem_insert_iff, mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨hCT s hsu.1, hsu.2⟩
      · exact ⟨hCT s hsv.1, hsv.2⟩
      · exact ⟨hCT t htu.1, htu.2⟩
      · exact ⟨hCT t htv.1, htv.2⟩
  have hpair (a : E) (hcard : ({q, a, u} : Finset E).card = 3) :
      ({q, a, u} : Finset E) ≠ {q, a, v} := by
    intro h
    have hu : u ∈ ({q, a, v} : Finset E) := h ▸ (by simp : u ∈ ({q, a, u} : Finset E))
    have hdistinct := Finset.card_triple_eq_three_iff.mp hcard
    simp [hdistinct.2.1.symm, hdistinct.2.2.symm, huv] at hu
  have hcross {r w : Finset E} (hr : r ∈ (C s).faces) (hw : w ∈ (C t).faces)
      (hrcard : r.card = 3) : r ≠ w := by
    intro h
    exact hst (K.refined_triangle_owner_unique hdim C (fun i => (hCS i).subset)
      hr (h.symm ▸ hw) hrcard)
  have hcount : {r : Finset E | r ∈ T.faces ∧ r.card = 3 ∧ q ∈ r}.ncard = 4 :=
    Set.ncard_eq_four.mpr ⟨_, _, _, _, hpair _ hsu.2.1,
      hcross hsu.1 htu.1 hsu.2.1, hcross hsu.1 htv.1 hsu.2.1,
      hcross hsv.1 htu.1 hsv.2.1, hcross hsv.1 htv.1 hsv.2.1, hpair _ htu.2.1, hglobal⟩
  exact ⟨e, s, t, u, v, hqe, hst, hes, het, hqu, hqv', huv, hcne, hQedge,
    hsu.1, hsu.2.1, hsv.1, hsv.2.1, htu.1, htu.2.1, htv.1, htv.2.1, hglobal, hcount⟩

end Geometry.SimplicialComplex
