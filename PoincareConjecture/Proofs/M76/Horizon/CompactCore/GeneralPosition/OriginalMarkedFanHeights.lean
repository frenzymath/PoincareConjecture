import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.RefinedCrossingNeighborSigns
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalChartTriangleHeights
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.MarkedConeFans

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

variable {E V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]

theorem exists_original_marked_fan_heights
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
    (g0 g : E → X) (N F : Set X)
    (hboundary : ∀ s : {s : K.faces // s.val.card = 3},
      EqOn g g0 (frontier (convexHull ℝ (s.val.val : Set E))))
    (hverticesoff : ∀ x ∈ K.vertices, g0 x ∉ F)
    (hapices : ∀ s : {s : K.faces // s.val.card = 3}, g (s.val.val.centroid ℝ id) ∉ F)
    (houter : ∀ x ∈ frontier K.space, g x ∉ F)
    (a b : {s : K.faces // s.val.card = 2} → K.vertices)
    (hab : ∀ e, (a e : E) ≠ b e)
    (hpair : ∀ e, ({(a e : E), (b e : E)} : Finset E) = e.val.val)
    (B : {s : K.faces // s.val.card = 2} → OpenPartialHomeomorph X V)
    (hBsource : ∀ e, MapsTo g0 (segment ℝ (a e : E) (b e : E)) (B e).source)
    (hline : ∀ e (r : I), B e (g0 (AffineMap.lineMap (a e : E) (b e : E) (r : ℝ))) =
      AffineMap.lineMap (B e (g0 (a e))) (B e (g0 (b e))) (r : ℝ))
    (hkind : ∀ e, Disjoint (B e).source F ∨ ∃ ell : V →ᴬ[ℝ] ℝ,
      (∀ y ∈ (B e).source, y ∈ N ↔ 0 ≤ ell (B e y)) ∧
      ∀ y ∈ (B e).source, y ∈ F ↔ ell (B e y) = 0)
    (D : {s : K.faces // s.val.card = 3} → OpenPartialHomeomorph X V)
    (ell : {s : K.faces // s.val.card = 3} → V →ᵃ[ℝ] ℝ)
    (A : Finset E → E →ᵃ[ℝ] ℝ)
    (hDsource : ∀ s, MapsTo g (C s).space (D s).source)
    (hDF : ∀ s y, y ∈ (D s).source → (y ∈ F ↔ ell s (D s y) = 0))
    (hDN : ∀ s, ¬ Disjoint (D s).source F →
      ∀ y ∈ (D s).source, y ∈ N ↔ 0 ≤ ell s (D s y))
    (hformula : ∀ s z, z ∈ (C s).faces → z.card = 3 →
      ∀ x ∈ convexHull ℝ (z : Set E), A z x = ell s (D s (g x)))
    {q : E} (hq : q ∈ T.vertices) (hqF : g q ∈ F) :
    ∃ c d u v : E,
      ({q, c, u} : Finset E) ∈ T.faces ∧ ({q, c, u} : Finset E).card = 3 ∧
      ({q, c, v} : Finset E) ∈ T.faces ∧ ({q, c, v} : Finset E).card = 3 ∧
      ({q, d, u} : Finset E) ∈ T.faces ∧ ({q, d, u} : Finset E).card = 3 ∧
      ({q, d, v} : Finset E) ∈ T.faces ∧ ({q, d, v} : Finset E).card = 3 ∧
      (∀ z ∈ T.faces, z.card = 3 → q ∈ z →
        z = {q, c, u} ∨ z = {q, c, v} ∨ z = {q, d, u} ∨ z = {q, d, v}) ∧
      c ≠ d ∧
      A {q, c, u} c ≠ 0 ∧ A {q, c, u} c = A {q, c, v} c ∧
      A {q, d, u} d ≠ 0 ∧ A {q, d, u} d = A {q, d, v} d ∧
      A {q, c, u} u < 0 ∧ 0 < A {q, c, v} v ∧
      A {q, d, u} u < 0 ∧ 0 < A {q, d, v} v := by
  classical
  let Faces := {s : K.faces // s.val.card = 3}
  have hCT (s : Faces) : C s ≤ T := by
    intro z hz
    change z ∈ T.faces
    rw [hTfaces]
    exact mem_iUnion.mpr ⟨s, hz⟩
  have horiginal : Disjoint K.vertices (g ⁻¹' F) := by
    apply disjoint_left.mpr
    intro x hx hxF
    have hxT : x ∈ T.space := hTS.symm.subset (K.vertices_subset_space hx)
    obtain ⟨z, hz, hxz⟩ := mem_space_iff.mp hxT
    rw [hTfaces] at hz
    obtain ⟨s, hzs⟩ := mem_iUnion.mp hz
    have hxs := (hCS s).subset ((C s).convexHull_subset_space hzs hxz)
    have hxm := (K.vertex_mem_convexHull_iff hx s.val.property).mp hxs
    have hproper : ({x} : Finset E) ⊂ s.val.val :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hxm, by
        intro he
        have hc := s.property
        rw [← he] at hc
        simp at hc⟩
    have hxf := intrinsicFrontier_subset_frontier
      ((K.indep s.val.property).convexHull_subset_intrinsicFrontier hproper
        (subset_convexHull ℝ _ (by simp : x ∈ (({x} : Finset E) : Set E))))
    exact hverticesoff x hx ((hboundary s hxf) ▸ hxF)
  obtain ⟨e, s, t, u, v, hqe, hst, hes, het, hqu, hqv, huv, hcne, hQedges,
    hsu, hsuc, hsv, hsvc, htu, htuc, htv, htvc, hglobal, _⟩ :=
    K.exists_marked_cone_four_triangle_fan hK hdim R T L C Q hLR hLS hQR hQS hC hCS
      hLC hvertices hfaces hTS hTfaces (g ⁻¹' F) horiginal hapices
      (disjoint_left.mpr houter) hq hqF
  have hQseg : (Q e).space = segment ℝ (a e : E) (b e : E) := by
    rw [hQS, ← hpair e, Finset.coe_pair, convexHull_pair]
  have hqQ : q ∈ (Q e).space := (hQS e).symm.subset (intrinsicInterior_subset hqe)
  have hquedge : ({q, u} : Finset E) ∈ (Q e).faces := by
    have hh : ({q, u} : Finset E) ∈
        {z : Finset E | z ∈ (Q e).faces ∧ z.card = 2 ∧ q ∈ z} := by
      rw [hQedges]
      simp
    exact hh.1
  have hqvedge : ({q, v} : Finset E) ∈ (Q e).faces := by
    have hh : ({q, v} : Finset E) ∈
        {z : Finset E | z ∈ (Q e).faces ∧ z.card = 2 ∧ q ∈ z} := by
      rw [hQedges]
      simp
    exact hh.1
  have huQ : u ∈ (Q e).space := (Q e).convexHull_subset_space hquedge
    (subset_convexHull ℝ _ (by simp))
  have hvQ : v ∈ (Q e).space := (Q e).convexHull_subset_space hqvedge
    (subset_convexHull ℝ _ (by simp))
  have hQboundary (i : Faces) (hei : e.val.val ⊆ i.val.val) :
      (Q e).space ⊆ frontier (convexHull ℝ (i.val.val : Set E)) := by
    have hproper : e.val.val ⊂ i.val.val := Finset.ssubset_iff_subset_ne.mpr ⟨hei, by
      intro he
      have hc := e.property
      rw [he, i.property] at hc
      contradiction⟩
    intro x hx
    exact intrinsicFrontier_subset_frontier
      ((K.indep i.val.property).convexHull_subset_intrinsicFrontier hproper ((hQS e).subset hx))
  have heq (i : Faces) (hei : e.val.val ⊆ i.val.val) {x : E} (hx : x ∈ (Q e).space) :
      g x = g0 x := hboundary i (hQboundary i hei hx)
  have hq0F : g0 q ∈ F := heq s hes hqQ ▸ hqF
  have hB (x : E) (hx : x ∈ (Q e).space) : g0 x ∈ (B e).source :=
    hBsource e (hQseg.subset hx)
  obtain ⟨m, hmN, hmF⟩ : ∃ m : V →ᴬ[ℝ] ℝ,
      (∀ y ∈ (B e).source, y ∈ N ↔ 0 ≤ m (B e y)) ∧
      ∀ y ∈ (B e).source, y ∈ F ↔ m (B e y) = 0 := by
    rcases hkind e with hd | hm
    · exact (disjoint_left.mp hd (hB q hqQ) hq0F).elim
    · exact hm
  have ha : m (B e (g0 (a e))) ≠ 0 := fun hz => hverticesoff _ (a e).property
    ((hmF _ (hBsource e (left_mem_segment ℝ _ _))).mpr hz)
  have hb : m (B e (g0 (b e))) ≠ 0 := fun hz => hverticesoff _ (b e).property
    ((hmF _ (hBsource e (right_mem_segment ℝ _ _))).mpr hz)
  obtain ⟨r, hr, hrq⟩ := (segment_eq_image_lineMap ℝ (a e : E) (b e : E)).subset
    (hQseg.subset hqQ)
  have hsigns := (Q e).refined_crossing_neighbor_signs (hab e) hQseg.subset hquedge hqvedge
    hqu hqv huv ⟨r, hr⟩ hrq (B e) g0 m (hline e) ha hb ((hmF _ (hB q hqQ)).mp hq0F)
  have hfaceSource (i : Faces) (hei : e.val.val ⊆ i.val.val) {x : E}
      (hx : x ∈ (Q e).space) : g x ∈ (D i).source := by
    apply hDsource i
    rw [hCS i]
    exact convexHull_mono hei ((hQS e).subset hx)
  have hnotdisjoint (i : Faces) (hei : e.val.val ⊆ i.val.val) : ¬ Disjoint (D i).source F :=
    fun h => disjoint_left.mp h (hfaceSource i hei hqQ) hqF
  have htransport (i : Faces) (hei : e.val.val ⊆ i.val.val) {x : E}
      (hx : x ∈ (Q e).space) :
      (m (B e (g0 x)) < 0 ↔ ell i (D i (g x)) < 0) ∧
      (0 < m (B e (g0 x)) ↔ 0 < ell i (D i (g x))) := by
    have hN : 0 ≤ m (B e (g0 x)) ↔ 0 ≤ ell i (D i (g x)) :=
      (hmN _ (hB x hx)).symm.trans
        ((by rw [heq i hei hx] : g0 x ∈ N ↔ g x ∈ N).trans
          (hDN i (hnotdisjoint i hei) _ (hfaceSource i hei hx)))
    have hF : m (B e (g0 x)) = 0 ↔ ell i (D i (g x)) = 0 :=
      (hmF _ (hB x hx)).symm.trans
        ((by rw [heq i hei hx] : g0 x ∈ F ↔ g x ∈ F).trans
          (hDF i _ (hfaceSource i hei hx)))
    refine ⟨by simpa only [not_le] using hN.not, ?_⟩
    constructor
    · intro h
      exact lt_of_le_of_ne (hN.mp h.le) (fun he => h.ne' (hF.mpr he.symm))
    · intro h
      exact lt_of_le_of_ne (hN.mpr h.le) (fun he => h.ne' (hF.mp he.symm))
  have hvalue (i : Faces) {z : Finset E} (hz : z ∈ (C i).faces) (hc : z.card = 3)
      {x : E} (hx : x ∈ z) : A z x = ell i (D i (g x)) :=
    hformula i z hz hc x (subset_convexHull ℝ _ hx)
  have hcenter (i : Faces) : ell i (D i (g (i.val.val.centroid ℝ id))) ≠ 0 := by
    apply mt (hDF i _ ?_).mpr (hapices i)
    apply hDsource i
    rw [hCS i]
    exact interior_subset (K.triangle_centroid_mem_interior hdim i.val.property i.property)
  have hsuCenter := hvalue s hsu hsuc (by simp : s.val.val.centroid ℝ id ∈
    ({q, s.val.val.centroid ℝ id, u} : Finset E))
  have hsvCenter := hvalue s hsv hsvc (by simp : s.val.val.centroid ℝ id ∈
    ({q, s.val.val.centroid ℝ id, v} : Finset E))
  have htuCenter := hvalue t htu htuc (by simp : t.val.val.centroid ℝ id ∈
    ({q, t.val.val.centroid ℝ id, u} : Finset E))
  have htvCenter := hvalue t htv htvc (by simp : t.val.val.centroid ℝ id ∈
    ({q, t.val.val.centroid ℝ id, v} : Finset E))
  have hsuValue := hvalue s hsu hsuc (by simp : u ∈ ({q, s.val.val.centroid ℝ id, u} : Finset E))
  have hsvValue := hvalue s hsv hsvc (by simp : v ∈ ({q, s.val.val.centroid ℝ id, v} : Finset E))
  have htuValue := hvalue t htu htuc (by simp : u ∈ ({q, t.val.val.centroid ℝ id, u} : Finset E))
  have htvValue := hvalue t htv htvc (by simp : v ∈ ({q, t.val.val.centroid ℝ id, v} : Finset E))
  have hexhaust {z : Finset E} (hz : z ∈ T.faces) (hc : z.card = 3) (hqz : q ∈ z) :
      z = {q, s.val.val.centroid ℝ id, u} ∨ z = {q, s.val.val.centroid ℝ id, v} ∨
      z = {q, t.val.val.centroid ℝ id, u} ∨ z = {q, t.val.val.centroid ℝ id, v} := by
    have hh : z ∈ {z : Finset E | z ∈ T.faces ∧ z.card = 3 ∧ q ∈ z} := ⟨hz, hc, hqz⟩
    rw [hglobal] at hh
    simpa only [mem_insert_iff, mem_singleton_iff] using hh
  rcases hsigns with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · refine ⟨_, _, u, v, hCT s hsu, hsuc, hCT s hsv, hsvc, hCT t htu, htuc,
      hCT t htv, htvc, fun _ hz hc hqz => hexhaust hz hc hqz, hcne,
      hsuCenter ▸ hcenter s, hsuCenter.trans hsvCenter.symm,
      htuCenter ▸ hcenter t, htuCenter.trans htvCenter.symm, ?_, ?_, ?_, ?_⟩
    · exact hsuValue ▸ (htransport s hes huQ).1.mp hu
    · exact hsvValue ▸ (htransport s hes hvQ).2.mp hv
    · exact htuValue ▸ (htransport t het huQ).1.mp hu
    · exact htvValue ▸ (htransport t het hvQ).2.mp hv
  · refine ⟨_, _, v, u, hCT s hsv, hsvc, hCT s hsu, hsuc, hCT t htv, htvc,
      hCT t htu, htuc, ?_, hcne,
      hsvCenter ▸ hcenter s, hsvCenter.trans hsuCenter.symm,
      htvCenter ▸ hcenter t, htvCenter.trans htuCenter.symm, ?_, ?_, ?_, ?_⟩
    · intro z hz hc hqz
      rcases hexhaust hz hc hqz with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    · exact hsvValue ▸ (htransport s hes hvQ).1.mp hv
    · exact hsuValue ▸ (htransport s hes huQ).2.mp hu
    · exact htvValue ▸ (htransport t het hvQ).1.mp hv
    · exact htuValue ▸ (htransport t het huQ).2.mp hu

end Geometry.SimplicialComplex
