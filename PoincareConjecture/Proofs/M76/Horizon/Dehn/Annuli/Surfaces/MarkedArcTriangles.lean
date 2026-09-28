import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.MarkedTriangleComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.OrientedVertexCut
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointSigns

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [DecidableEq E] in

theorem interval_eq_of_preconnected_subset_endpoints
    {U V : Set E} {a b : E} (hU : IsFinitePLBallPair ℝ U {a, b}) (hab : a ≠ b)
    (hV : IsPreconnected V) (hVU : V ⊆ U) (ha : a ∈ V) (hb : b ∈ V) : V = U := by
  obtain ⟨e, _, hea, heb⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  let f : V → ℝ := fun x ↦ (e.symm ⟨x, hVU x.property⟩ : ℝ)
  have hf : Continuous f := continuous_subtype_val.comp
    (e.symm.continuous.comp (continuous_subtype_val.subtype_mk fun x ↦ hVU x.property))
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hV
  have h0 : (0 : ℝ) ∈ range f := by
    refine ⟨⟨a, ha⟩, ?_⟩
    have he : (⟨a, hVU ha⟩ : U) = e ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext hea.symm
    simp only [f, he, e.symm_apply_apply]
  have h1 : (1 : ℝ) ∈ range f := by
    refine ⟨⟨b, hb⟩, ?_⟩
    have he : (⟨b, hVU hb⟩ : U) = e ⟨1, zero_le_one, le_rfl⟩ := Subtype.ext heb.symm
    simp only [f, he, e.symm_apply_apply]
  apply hVU.antisymm
  intro x hx
  obtain ⟨y, hy⟩ := (isPreconnected_range hf).Icc_subset h0 h1 (e.symm ⟨x, hx⟩).property
  have h := e.symm.injective (Subtype.ext hy)
  have hxy : (y : E) = x := congrArg Subtype.val h
  exact hxy ▸ y.property

theorem exists_covering_vertex_arc_triangle_chain
    (A : SimplicialComplex ℝ E) [Fintype A.faces] {v a b : E}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (ha : {v, a} ∈ A.faces) (hb : {v, b} ∈ A.faces)
    (U V : Set E)
    (hU : IsFinitePLBallPair ℝ U
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id})
    (hV : IsClosed V)
    (hcover : U ∪ V = (A.barycentricSubdivision.link v).space)
    (hinter : U ∩ V ⊆
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id}) :
    ∃ (n : ℕ) (p : ℕ → E), 0 < n ∧ p 0 = a ∧ p n = b ∧
      InjOn p (Icc 0 n) ∧ (∀ k ≤ n, v ≠ p k) ∧
      (∀ k < n, p k ≠ p (k + 1) ∧ {v, p k, p (k + 1)} ∈ A.faces ∧
        ({v, p k, p (k + 1)} : Finset E).card = 3 ∧
        ({v, p k, p (k + 1)} : Finset E).centroid ℝ id ∈ U) ∧
      ∀ t ∈ A.faces, t.card = 3 → v ∈ t → t.centroid ℝ id ∈ U →
        ∃ k < n, t = {v, p k, p (k + 1)} := by
  classical
  have hv : v ∈ A.vertices := A.down_closed ha (by simp) (by simp)
  let K := A.link v
  have haK : a ∈ K.vertices := by
    refine ⟨A.down_closed ha (by simp) (by simp), ?_, ha⟩
    simpa only [Finset.mem_singleton] using hva
  have hbK : b ∈ K.vertices := by
    refine ⟨A.down_closed hb (by simp) (by simp), ?_, hb⟩
    simpa only [Finset.mem_singleton] using hvb
  obtain ⟨e, _, hcent⟩ := exists_centroid_vertex_rim_homeomorph A hv
  have hca : (e ⟨a, K.vertices_subset_space haK⟩ : E) =
      ({v, a} : Finset E).centroid ℝ id := by
    simpa only [Finset.centroid_singleton, id_eq] using hcent {a} haK
  have hcb : (e ⟨b, K.vertices_subset_space hbK⟩ : E) =
      ({v, b} : Finset E).centroid ℝ id := by
    simpa only [Finset.centroid_singleton, id_eq] using hcent {b} hbK
  have hends : ({v, a} : Finset E).centroid ℝ id ≠
      ({v, b} : Finset E).centroid ℝ id := by
    intro h
    have he := e.injective (Subtype.ext (hca.trans (h.trans hcb.symm)))
    exact hab (congrArg Subtype.val he)
  obtain ⟨n, p, hn, hp0, hpn, hpi, _, hpe⟩ :=
    exists_edge_path_in_homeomorphic_rim_arc K (finite_link_faces (Set.toFinite A.faces) v)
      e U V hU.isCompact.isClosed hV hcover hU.isConnected.isPreconnected haK hbK hab
      (hca.symm ▸ hU.1 (Or.inl rfl)) (hcb.symm ▸ hU.1 (Or.inr rfl))
      (by rwa [hca, hcb])
  have hpv (k : ℕ) (hk : k ≤ n) : p k ∈ K.vertices := by
    rcases hk.eq_or_lt with h | h
    · simpa only [h, hpn] using hbK
    · exact K.down_closed (hpe k h).1 (by simp) (by simp)
  have hvp (k : ℕ) (hk : k ≤ n) : v ≠ p k := by
    exact fun h ↦ (hpv k hk).2.1 (Finset.mem_singleton.mpr h)
  have htri (k : ℕ) (hk : k < n) : p k ≠ p (k + 1) ∧
      {v, p k, p (k + 1)} ∈ A.faces ∧
      ({v, p k, p (k + 1)} : Finset E).card = 3 ∧
      ({v, p k, p (k + 1)} : Finset E).centroid ℝ id ∈ U := by
    have hne : p k ≠ p (k + 1) := by
      intro h
      have he := hpi ⟨Nat.zero_le _, hk.le⟩ ⟨Nat.zero_le _, by omega⟩ h
      omega
    have hface := (hpe k hk).1
    refine ⟨hne, hface.2.2, ?_, ?_⟩
    · simp [hvp k hk.le, hvp (k + 1) (by omega), hne]
    · rw [← hcent {p k, p (k + 1)} hface]
      apply (hpe k hk).2
      simpa only [Finset.coe_pair] using
        ({p k, p (k + 1)} : Finset E).centroid_mem_convexHull (Finset.insert_nonempty _ _)
  let T : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ K.faces ∧ ∃ k < n, s ⊆ {p k, p (k + 1)}}
      indep := fun hs ↦ K.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
        intro r hrs hr
        obtain ⟨k, hk, hks⟩ := hs.2
        exact ⟨K.down_closed hs.1 hrs hr, k, hk, hrs.trans hks⟩
      inter_subset_convexHull := fun hs ht ↦ K.inter_subset_convexHull hs.1 ht.1 }
  have hTK : T ≤ K := fun _ hs ↦ hs.1
  let : Fintype K.faces := (finite_link_faces (Set.toFinite A.faces) v).fintype
  let : Fintype T.faces := (Set.toFinite K.faces |>.subset hTK).fintype
  have hTs : T.space = ⋃ k ∈ Iio n, convexHull ℝ ({p k, p (k + 1)} : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      obtain ⟨k, hk, hsk⟩ := hs.2
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk,
        by simpa only [Finset.coe_pair] using convexHull_mono hsk hxs⟩⟩
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      obtain ⟨hkn, hxk⟩ := mem_iUnion.mp hk
      exact T.convexHull_subset_space ⟨(hpe k hkn).1, k, hkn, subset_rfl⟩
        (by simpa only [Finset.coe_pair] using hxk)
  have hconn : IsPreconnected T.space := by
    rw [hTs]
    apply IsPreconnected.biUnion_of_chain ordConnected_Iio
      (fun k _ ↦ (convex_convexHull ℝ ({p k, p (k + 1)} : Set E)).isPreconnected)
    intro k _ _
    exact ⟨p (k + 1), subset_convexHull ℝ _ (Or.inr rfl),
      subset_convexHull ℝ _ (Or.inl rfl)⟩
  let g : T.space → E := fun x ↦ e ⟨x, space_subset_of_le hTK x.property⟩
  have hg : Continuous g := continuous_subtype_val.comp
    (e.continuous.comp (continuous_subtype_val.subtype_mk
      fun x ↦ space_subset_of_le hTK x.property))
  have hgU : range g ⊆ U := by
    rintro x ⟨y, rfl⟩
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp y.property
    obtain ⟨k, hk, hsk⟩ := hs.2
    exact (hpe k hk).2 _ (by simpa only [Finset.coe_pair] using convexHull_mono hsk hys)
  have haT : a ∈ T.space := by
    rw [hTs]
    exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨hn,
      hp0 ▸ subset_convexHull ℝ _ (Or.inl rfl)⟩⟩
  have hbT : b ∈ T.space := by
    rw [hTs]
    refine mem_iUnion.mpr ⟨n - 1, mem_iUnion.mpr ⟨show n - 1 < n by omega, ?_⟩⟩
    rw [Nat.sub_add_cancel hn, hpn]
    exact subset_convexHull ℝ _ (Or.inr rfl)
  let : PreconnectedSpace T.space := isPreconnected_iff_preconnectedSpace.mp hconn
  have hgcover : range g = U := interval_eq_of_preconnected_subset_endpoints
    hU hends (isPreconnected_range hg) hgU ⟨⟨a, haT⟩, hca⟩ ⟨⟨b, hbT⟩, hcb⟩
  refine ⟨n, p, hn, hp0, hpn, hpi, hvp, htri, ?_⟩
  intro t ht htc hvt hct
  let s := t.erase v
  have hsc : s.card = 2 := by simp only [s, Finset.card_erase_of_mem hvt, htc]
  have hs : s ∈ K.faces := by
    refine ⟨A.down_closed ht (Finset.erase_subset _ _) ?_, Finset.notMem_erase _ _, ?_⟩
    · exact Finset.card_pos.mp (by omega)
    · simpa only [s, Finset.insert_erase hvt] using ht
  have hc := hcent s hs
  rw [Finset.insert_erase hvt] at hc
  obtain ⟨x, hx⟩ := hgcover.symm ▸ hct
  have he := e.injective (Subtype.ext (hx.trans hc.symm))
  have hxs : (x : E) = s.centroid ℝ id := congrArg Subtype.val he
  have hsT : s.centroid ℝ id ∈ T.space := hxs ▸ x.property
  have hface := K.face_mem_subcomplex_of_centroid T hTK hs hsT
  obtain ⟨k, hk, hsk⟩ := hface.2
  refine ⟨k, hk, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · rw [← Finset.insert_erase hvt]
    exact Finset.insert_subset_insert v hsk
  · rw [htc, (htri k hk).2.2.1]

theorem vertex_arc_triangles_same_marked_component
    (A L : SimplicialComplex ℝ E) [Fintype A.faces] {v a b : E}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (ha : {v, a} ∈ A.faces) (hb : {v, b} ∈ A.faces)
    (hmarked : ∀ s ∈ L.faces, v ∈ s → s.card = 2 → s = {v, a} ∨ s = {v, b})
    (U V : Set E)
    (hU : IsFinitePLBallPair ℝ U
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id})
    (hV : IsClosed V)
    (hcover : U ∪ V = (A.barycentricSubdivision.link v).space)
    (hinter : U ∩ V ⊆
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id})
    (C : (A.markedTriangleGraph L).ConnectedComponent)
    {t u : Finset E} (ht : t ∈ A.faces) (htc : t.card = 3) (hvt : v ∈ t)
    (htU : t.centroid ℝ id ∈ U)
    (hu : u ∈ A.faces) (huc : u.card = 3) (hvu : v ∈ u) (huU : u.centroid ℝ id ∈ U) :
    t ∈ (A.markedTriangleComponent L C).faces ↔
      u ∈ (A.markedTriangleComponent L C).faces := by
  classical
  obtain ⟨n, p, hn, hp0, hpn, hpi, hvp, htri, hwhole⟩ :=
    exists_covering_vertex_arc_triangle_chain A hva hvb hab ha hb U V hU hV hcover hinter
  let tri : ℕ → Finset E := fun k ↦ {v, p k, p (k + 1)}
  have hstep (k : ℕ) (hk : k + 1 < n) :
      tri k ∈ (A.markedTriangleComponent L C).faces ↔
        tri (k + 1) ∈ (A.markedTriangleComponent L C).faces := by
    let s : Finset E := {v, p (k + 1)}
    have hsc : s.card = 2 := Finset.card_pair (hvp _ hk.le)
    have hmark : s ∉ L.faces := by
      intro hs
      rcases hmarked s hs (by simp [s]) hsc with he | he
      all_goals
        have hmem : p (k + 1) ∈ s := by simp [s]
        rw [he] at hmem
        rcases Finset.mem_insert.mp hmem with hv | hp
        · exact hvp _ hk.le hv.symm
        · have hp := Finset.mem_singleton.mp hp
          first
          | have hi := hpi ⟨Nat.zero_le _, hk.le⟩ ⟨Nat.zero_le _, hn.le⟩
              (hp.trans hp0.symm)
            omega
          | have hi := hpi ⟨Nat.zero_le _, hk.le⟩ ⟨Nat.zero_le _, le_rfl⟩
              (hp.trans hpn.symm)
            omega
    have hs0 : s ⊆ tri k := by simp [s, tri]
    have hs1 : s ⊆ tri (k + 1) := by simp [s, tri]
    constructor
    · intro h
      exact A.markedTriangleComponent_unmarked_coface L C
        ((A.markedTriangleComponent L C).down_closed h hs0 (by simp [s])) hsc hmark
        (htri _ hk).2.1 (htri _ hk).2.2.1 hs1
    · intro h
      exact A.markedTriangleComponent_unmarked_coface L C
        ((A.markedTriangleComponent L C).down_closed h hs1 (by simp [s])) hsc hmark
        (htri k (by omega)).2.1 (htri k (by omega)).2.2.1 hs0
  have hall (k : ℕ) (hk : k < n) :
      tri 0 ∈ (A.markedTriangleComponent L C).faces ↔
        tri k ∈ (A.markedTriangleComponent L C).faces := by
    induction k with
    | zero => rfl
    | succ k ih => exact (ih (by omega)).trans (hstep k hk)
  obtain ⟨i, hi, rfl⟩ := hwhole t ht htc hvt htU
  obtain ⟨j, hj, rfl⟩ := hwhole u hu huc hvu huU
  exact (hall i hi).symm.trans (hall j hj)

end PoincareConjecture.M76.Dehn
