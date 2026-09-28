import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Radial
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.MiddleArcs
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Trimming

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)

theorem radialSide_subset_union (d : Bool × Bool) :
    P.radialSide d B.scale ⊆ ⋃ i, (B.face i).carrier := by
  rcases d with ⟨d, s⟩
  cases d
  · rw [← P.secondSide_eq_radialSide (s, s)]
    exact (B.secondSide_subset_carrier (s, s)).trans (subset_iUnion (fun i => (B.face i).carrier) (s, s))
  · rw [← P.firstSide_eq_radialSide (s, s)]
    exact (B.firstSide_subset_carrier (s, s)).trans (subset_iUnion (fun i => (B.face i).carrier) (s, s))

omit [T2Space M] in

theorem exists_radialSide_eq_of_boundary_match (i : Bool × Bool) (k : Fin 3)
    (hk : k = 1 ∨ k = 2) {S : Set M}
    (hS : ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 = S) :
    ∃ d : Bool × Bool, P.radialSide d B.scale = S := by
  rcases hk with rfl | rfl
  · exact ⟨(false, i.2), (P.secondSide_eq_radialSide i B.scale).symm.trans
      ((B.second_image i).symm.trans hS)⟩
  · exact ⟨(true, i.1), (P.firstSide_eq_radialSide i B.scale).symm.trans
      ((B.first_image i).symm.trans hS)⟩

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

theorem preconnected_boundary_subset_edge {S : Set M}
    (hS : IsPreconnected S) (hboundary : S ⊆ chartDiskBoundaryUnion D.centers D.radius)
    (hvertices : Disjoint S (D.vertices : Set M)) (a : D.EdgeIndex)
    {q : M} (hqS : q ∈ S) (hqa : q ∈ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) :
    S ⊆ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 := by
  classical
  let K : Set M := ⋃ b : {b : D.EdgeIndex // b ≠ a},
    (D.edge b.1.1 b.1.2).map '' Icc (0 : ℝ) 1
  have hK : IsClosed K := isClosed_iUnion_of_finite (fun b => (D.isCompact_edge b).isClosed)
  have hcover : S ⊆ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 ∪ K := by
    intro z hz
    have hzK := hboundary hz
    rw [← D.boundary_cover] at hzK
    obtain ⟨b, hb⟩ := mem_iUnion.mp hzK
    by_cases hba : b = a
    · exact Or.inl (hba ▸ hb)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨b, hba⟩, hb⟩)
  have havoid : S ∩ ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 ∩ K) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hzS, hza, hzK⟩
    obtain ⟨b, hb⟩ := mem_iUnion.mp hzK
    have hv := (D.edge_intersection a b b.property.symm ⟨hza, hb⟩).1
    apply disjoint_left.mp hvertices hzS
    rcases hv with h | h
    · exact h ▸ (D.endpoints_mem_vertices a).1
    · exact h ▸ (D.endpoints_mem_vertices a).2
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS _ _
      (D.isCompact_edge a).isClosed hK hcover havoid with h | h
  · exact h
  · exact False.elim (by
      have hz : q ∈ S ∩ ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 ∩ K) := ⟨hqS, hqa, h hqS⟩
      simp only [havoid, notMem_empty] at hz)

omit [T2Space M] in
theorem edgeFromEndpoint_continuous (a : D.EdgeIndex) (b : Bool) :
    Continuous (D.edgeFromEndpoint a b) := by
  apply (D.edge_contMDiff a).continuous.comp
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

omit [T2Space M] in
theorem edgeFromEndpoint_injective (a : D.EdgeIndex) (b : Bool) :
    InjOn (D.edgeFromEndpoint a b) (Icc (0 : ℝ) 1) := by
  cases b
  · exact D.edge_injective a.1 a.2
  · intro s hs t ht heq
    have h := D.edge_injective a.1 a.2
      (show 1 - s ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (show 1 - t ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.2], by linarith [ht.1]⟩) heq
    linarith

omit [T2Space M] in
theorem edgeFromEndpoint_image_unit (a : D.EdgeIndex) (b : Bool) :
    D.edgeFromEndpoint a b '' Icc (0 : ℝ) 1 = (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 := by
  cases b
  · rfl
  · simpa only [sub_self] using D.edgeFromEndpoint_image_terminal a 1

omit [T2Space M] in
theorem edgeEndpoint_injective (a : D.EdgeIndex) : Function.Injective (D.edgeEndpoint a) := by
  intro b c hbc
  have heq := congrArg (fun p : D.vertices => (p : M)) hbc
  cases b <;> cases c
  · rfl
  · exact False.elim (D.edge_endpoints_distinct a heq)
  · exact False.elim (D.edge_endpoints_distinct a heq.symm)
  · rfl

omit [T2Space M] in

theorem exists_edgeEndpoint_eq_of_mem {p : D.vertices} (a : D.EdgeIndex)
    (hp : (p : M) ∈ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) :
    ∃ b : Bool, D.edgeEndpoint a b = p := by
  obtain ⟨t, ht, heq⟩ := hp
  by_cases h0 : t = 0
  · exact ⟨false, Subtype.ext (by simpa [h0, edgeEndpoint] using heq)⟩
  by_cases h1 : t = 1
  · exact ⟨true, Subtype.ext (by simpa [h1, edgeEndpoint] using heq)⟩
  exact False.elim (disjoint_left.mp (D.open_edge_disjoint_vertices a)
    ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩, heq⟩ p.property)

omit [T2Space M] in

theorem patch_inter_vertices_subset_center
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (p : D.vertices) : (P p).carrier ∩ (D.vertices : Set M) ⊆ {(p : M)} := by
  rintro q ⟨hqP, hqV⟩
  by_contra hqp
  have hne : p ≠ ⟨q, hqV⟩ := fun h => hqp (congrArg Subtype.val h).symm
  exact disjoint_left.mp (hdisjoint p ⟨q, hqV⟩ hne) hqP
    ((P ⟨q, hqV⟩).openCarrier_subset_carrier (P ⟨q, hqV⟩).mem_openCarrier)

theorem radialSide_inter_edge_mem_endpoint_segment
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (p : D.vertices) (a : D.EdgeIndex) (d : Bool × Bool)
    {ε : ℝ} (hε : 0 < ε) (hwidth : ε ≤ (P p).width)
    (cut : Bool → ℝ) (hcut : ∀ b, cut b ∈ Ioo (0 : ℝ) 1)
    (hmatch : ∀ b, D.edgeEndpoint a b = p → ∃ e : Bool × Bool,
      (P p).radialSide e ε = D.edgeFromEndpoint a b '' Icc 0 (cut b))
    {q : M} (hqR : q ∈ (P p).radialSide d ε) (hqp : q ≠ (p : M))
    (hqa : q ∈ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) :
    ∃ b : Bool, D.edgeEndpoint a b = p ∧
      q ∈ D.edgeFromEndpoint a b '' Icc 0 (cut b) := by
  let S := (P p).radialSide d ε \ {(p : M)}
  have hRcarrier := (P p).radialSide_subset_carrier d hwidth
  have hqboundary : q ∈ chartDiskBoundaryUnion D.centers D.radius := by
    rw [← D.boundary_cover]
    exact mem_iUnion.mpr ⟨a, hqa⟩
  have hRcircles := (P p).radialSide_subset_circles_of_mem d hwidth hqR hqp
    ((hlocal p q (hRcarrier hqR)).mp hqboundary)
  have hSboundary : S ⊆ chartDiskBoundaryUnion D.centers D.radius :=
    fun z hz => (hlocal p z (hRcarrier hz.1)).mpr (hRcircles hz.1)
  have hSvertices : Disjoint S (D.vertices : Set M) := by
    apply disjoint_left.mpr
    intro z hz hzV
    exact hz.2 (D.patch_inter_vertices_subset_center P hdisjoint p ⟨hRcarrier hz.1, hzV⟩)
  have hSedge : S ⊆ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 :=
    D.preconnected_boundary_subset_edge ((P p).isPreconnected_radialSide_sdiff_center d hwidth)
      hSboundary hSvertices a ⟨hqR, hqp⟩ hqa
  have hpedge : (p : M) ∈ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 :=
    (closure_minimal hSedge (D.isCompact_edge a).isClosed)
      ((P p).center_mem_closure_radialSide_sdiff d hε hwidth)
  obtain ⟨b, hb⟩ := D.exists_edgeEndpoint_eq_of_mem a hpedge
  obtain ⟨e, he⟩ := hmatch b hb
  let T := D.edgeFromEndpoint a b '' Icc (cut b) 1
  have hTclosed : IsClosed T :=
    (isCompact_Icc.image (D.edgeFromEndpoint_continuous a b)).isClosed
  have hzero : D.edgeFromEndpoint a b 0 = (p : M) :=
    (D.edgeFromEndpoint_zero a b).trans (congrArg Subtype.val hb)
  have hpT : (p : M) ∉ T := by
    rintro ⟨t, ht, heq⟩
    have ht0 := D.edgeFromEndpoint_injective a b
      ⟨(hcut b).1.le.trans ht.1, ht.2⟩ (by simp) (heq.trans hzero.symm)
    linarith [(hcut b).1, ht.1]
  obtain ⟨z, hzT, hzS⟩ := mem_closure_iff.mp
    ((P p).center_mem_closure_radialSide_sdiff d hε hwidth)
      Tᶜ hTclosed.isOpen_compl hpT
  have hzedge := hSedge hzS
  rw [← D.edgeFromEndpoint_image_unit a b] at hzedge
  obtain ⟨t, ht, heq⟩ := hzedge
  have htcut : t ≤ cut b := by
    by_contra h
    exact hzT ⟨t, ⟨(lt_of_not_ge h).le, ht.2⟩, heq⟩
  have hze : z ∈ (P p).radialSide e ε := by
    rw [he]
    exact ⟨t, ⟨ht.1, htcut⟩, heq⟩
  have hde : d = e := by
    by_contra h
    exact hzS.2 ((P p).radialSide_inter_subset_center h hwidth ⟨hzS.1, hze⟩)
  exact ⟨b, hb, by simpa only [hde, he] using hqR⟩

theorem vertex_caps_inter_edge_mem_endpoint_segment
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (cut : D.EdgeIndex → Bool → ℝ)
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3))
    (hmatch : ∀ a b, ∃ d : Bool × Bool,
      (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b))
    (p : D.vertices) (a : D.EdgeIndex) {q : M}
    (hqcap : q ∈ ⋃ i, ((B p).face i).carrier)
    (hqa : q ∈ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) :
    ∃ b : Bool, D.edgeEndpoint a b = p ∧
      q ∈ D.edgeFromEndpoint a b '' Icc 0 (cut a b) := by
  by_cases hqp : q = (p : M)
  · obtain ⟨b, hb⟩ := D.exists_edgeEndpoint_eq_of_mem a (hqp ▸ hqa)
    refine ⟨b, hb, 0, ⟨le_rfl, (hcut a b).1.le⟩, ?_⟩
    exact (D.edgeFromEndpoint_zero a b).trans ((congrArg Subtype.val hb).trans hqp.symm)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hqcap
  have hqboundary : q ∈ chartDiskBoundaryUnion D.centers D.radius := by
    rw [← D.boundary_cover]
    exact mem_iUnion.mpr ⟨a, hqa⟩
  have hqcircle := (hlocal p q ((B p).carrier_subset_patch i hi)).mp hqboundary
  obtain ⟨d, hd⟩ : ∃ d : Bool × Bool, q ∈ (P p).radialSide d (B p).scale := by
    rcases (B p).carrier_subset_sector_sides i hi with hs | hs | hs
    · exact False.elim (disjoint_left.mp ((P p).sector_disjoint_circles i) hs hqcircle)
    · exact ⟨(true, i.1), (P p).firstSide_eq_radialSide i (B p).scale ▸ hs⟩
    · exact ⟨(false, i.2), (P p).secondSide_eq_radialSide i (B p).scale ▸ hs⟩
  apply D.radialSide_inter_edge_mem_endpoint_segment P hdisjoint hlocal p a d
    (B p).scale_pos (B p).scale_lt_width.le (cut a)
    (fun b => ⟨(hcut a b).1, (hcut a b).2.trans (by norm_num)⟩) ?_ hd hqp hqa
  intro b hb
  subst p
  exact hmatch a b

section CapFamily

variable
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (cut : D.EdgeIndex → Bool → ℝ)
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3))
    (hmatch : ∀ a b, ∃ d : Bool × Bool,
      (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b))

include hmatch in
theorem endpoint_segment_subset_vertex_caps (a : D.EdgeIndex) (b : Bool) :
    D.edgeFromEndpoint a b '' Icc 0 (cut a b) ⊆
      ⋃ i, ((B (D.edgeEndpoint a b)).face i).carrier := by
  obtain ⟨d, hd⟩ := hmatch a b
  rw [← hd]
  exact (B (D.edgeEndpoint a b)).radialSide_subset_union d

include hdisjoint hlocal hcut hmatch in

theorem endpoint_vertex_caps_inter_edge (a : D.EdgeIndex) (b : Bool) :
    (⋃ i, ((B (D.edgeEndpoint a b)).face i).carrier) ∩
      ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b) := by
  apply Subset.antisymm
  · rintro q ⟨hqcap, hqa⟩
    obtain ⟨c, hc, hqc⟩ := D.vertex_caps_inter_edge_mem_endpoint_segment
      P B hdisjoint hlocal cut hcut hmatch (D.edgeEndpoint a b) a hqcap hqa
    have hcb := D.edgeEndpoint_injective a hc
    simpa only [hcb] using hqc
  · intro q hq
    refine ⟨D.endpoint_segment_subset_vertex_caps P B cut hmatch a b hq, ?_⟩
    rw [← D.edgeFromEndpoint_image_unit a b]
    exact image_mono (Icc_subset_Icc le_rfl ((hcut a b).2.le.trans (by norm_num))) hq

include hdisjoint hlocal hcut hmatch in

theorem vertex_caps_inter_edge (a : D.EdgeIndex) :
    (⋃ p, ⋃ i, ((B p).face i).carrier) ∩
      ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) =
        (D.edgeFromEndpoint a false '' Icc 0 (cut a false)) ∪
          (D.edgeFromEndpoint a true '' Icc 0 (cut a true)) := by
  apply Subset.antisymm
  · rintro q ⟨hqcap, hqa⟩
    obtain ⟨p, hp⟩ := mem_iUnion.mp hqcap
    obtain ⟨b, _, hb⟩ := D.vertex_caps_inter_edge_mem_endpoint_segment
      P B hdisjoint hlocal cut hcut hmatch p a hp hqa
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · intro q hq
    have hsegment (b : Bool) (hb : q ∈ D.edgeFromEndpoint a b '' Icc 0 (cut a b)) :
        q ∈ (⋃ p, ⋃ i, ((B p).face i).carrier) ∩
          ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) := by
      have h := (D.endpoint_vertex_caps_inter_edge P B hdisjoint hlocal cut hcut hmatch a b).symm ▸ hb
      exact ⟨mem_iUnion.mpr ⟨D.edgeEndpoint a b, h.1⟩, h.2⟩
    exact hq.elim (hsegment false) (hsegment true)

include hdisjoint hlocal hcut hmatch in

theorem vertex_caps_inter_middleArc (a : D.EdgeIndex) :
    (⋃ p, ⋃ i, ((B p).face i).carrier) ∩ D.middleArc cut a =
      {(D.edge a.1 a.2).map (cut a false),
        (D.edge a.1 a.2).map (1 - cut a true)} := by
  have hparam := D.middleArc_parameters hcut a
  have hleft : cut a false ∈ Icc (0 : ℝ) 1 :=
    ⟨hparam.1.le, hparam.2.1.le.trans hparam.2.2.le⟩
  have hright : 1 - cut a true ∈ Icc (0 : ℝ) 1 :=
    ⟨hparam.1.le.trans hparam.2.1.le, hparam.2.2.le⟩
  apply Subset.antisymm
  · rintro q ⟨hqcap, t, ht, rfl⟩
    have htunit : t ∈ Icc (0 : ℝ) 1 :=
      ⟨hleft.1.trans ht.1, ht.2.trans hright.2⟩
    have hedge := D.vertex_caps_inter_edge P B hdisjoint hlocal cut hcut hmatch a
    have hsegments := hedge ▸ (show (D.edge a.1 a.2).map t ∈
      (⋃ p, ⋃ i, ((B p).face i).carrier) ∩
        ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) from ⟨hqcap, t, htunit, rfl⟩)
    rcases hsegments with h | h
    · obtain ⟨s, hs, heq⟩ := h
      have hst := D.edge_injective a.1 a.2
        ⟨hs.1, hs.2.trans hleft.2⟩ htunit heq
      have htleft : t = cut a false := le_antisymm (hst ▸ hs.2) ht.1
      exact Or.inl (congrArg (D.edge a.1 a.2).map htleft)
    · rw [D.edgeFromEndpoint_image_terminal] at h
      obtain ⟨s, hs, heq⟩ := h
      have hst := D.edge_injective a.1 a.2
        ⟨hright.1.trans hs.1, hs.2⟩ htunit heq
      have htright : t = 1 - cut a true := le_antisymm ht.2 (hst ▸ hs.1)
      exact Or.inr (mem_singleton_iff.mpr (congrArg (D.edge a.1 a.2).map htright))
  · intro q hq
    have hsegment (b : Bool) : D.edgeFromEndpoint a b (cut a b) ∈
        ⋃ p, ⋃ i, ((B p).face i).carrier := by
      apply mem_iUnion.mpr
      refine ⟨D.edgeEndpoint a b, ?_⟩
      exact D.endpoint_segment_subset_vertex_caps P B cut hmatch a b
        ⟨cut a b, ⟨(hcut a b).1.le, le_rfl⟩, rfl⟩
    rcases hq with h | h
    · subst q
      exact ⟨hsegment false, cut a false, ⟨le_rfl, hparam.2.1.le⟩, rfl⟩
    · have hq := mem_singleton_iff.mp h
      subst q
      exact ⟨hsegment true, 1 - cut a true, ⟨hparam.2.1.le, le_rfl⟩, rfl⟩

include hdisjoint hlocal hcut hmatch in

theorem vertex_caps_disjoint_open_middleArc (a : D.EdgeIndex) :
    Disjoint (⋃ p, ⋃ i, ((B p).face i).carrier)
      ((D.edge a.1 a.2).map '' Ioo (cut a false) (1 - cut a true)) := by
  apply disjoint_left.mpr
  rintro q hqcap ⟨t, ht, rfl⟩
  have hparam := D.middleArc_parameters hcut a
  have htunit : t ∈ Icc (0 : ℝ) 1 :=
    ⟨hparam.1.le.trans ht.1.le, ht.2.le.trans hparam.2.2.le⟩
  have hends := D.vertex_caps_inter_middleArc P B hdisjoint hlocal cut hcut hmatch a ▸
    (show (D.edge a.1 a.2).map t ∈
      (⋃ p, ⋃ i, ((B p).face i).carrier) ∩ D.middleArc cut a from
        ⟨hqcap, t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
  rcases hends with h | h
  · have heq := D.edge_injective a.1 a.2 htunit
      ⟨hparam.1.le, hparam.2.1.le.trans hparam.2.2.le⟩ h
    exact (ne_of_gt ht.1) heq
  · have heq := D.edge_injective a.1 a.2 htunit
      ⟨hparam.1.le.trans hparam.2.1.le, hparam.2.2.le⟩ (mem_singleton_iff.mp h)
    exact (ne_of_lt ht.2) heq

end CapFamily

theorem exists_vertex_caps_with_edge_intersections
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (x : D.vertices → Bool × Bool → M)
    (hchart : ∀ p i, (P p).closedSector i ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x p i)).source) :
    ∃ (ε : ℝ) (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
      (cut : D.EdgeIndex → Bool → ℝ),
      0 < ε ∧ (∀ p, (B p).scale = ε) ∧
      (∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3)) ∧
      (∀ a b, ∃ d : Bool × Bool,
        (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
          D.edgeFromEndpoint a b '' Icc 0 (cut a b)) ∧
      (∀ a b, (⋃ i, ((B (D.edgeEndpoint a b)).face i).carrier) ∩
        ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) =
          D.edgeFromEndpoint a b '' Icc 0 (cut a b)) ∧
      (∀ a, (⋃ p, ⋃ i, ((B p).face i).carrier) ∩ D.middleArc cut a =
        {(D.edge a.1 a.2).map (cut a false),
          (D.edge a.1 a.2).map (1 - cut a true)}) ∧
      ∀ a, Disjoint (⋃ p, ⋃ i, ((B p).face i).carrier)
        ((D.edge a.1 a.2).map '' Ioo (cut a false) (1 - cut a true)) := by
  obtain ⟨ε, B, cut, hε, hscale, hmatching⟩ :=
    D.exists_vertex_caps_matching_edges P hlocal x hchart
  have hcut := fun a b => (hmatching a b).1
  have hmatch (a : D.EdgeIndex) (b : Bool) : ∃ d : Bool × Bool,
      (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b) := by
    obtain ⟨i, j, k, _, hk, hi, _⟩ := (hmatching a b).2
    exact (B (D.edgeEndpoint a b)).exists_radialSide_eq_of_boundary_match i k hk hi
  exact ⟨ε, B, cut, hε, hscale, hcut, hmatch,
    D.endpoint_vertex_caps_inter_edge P B hdisjoint hlocal cut hcut hmatch,
    D.vertex_caps_inter_middleArc P B hdisjoint hlocal cut hcut hmatch,
    D.vertex_caps_disjoint_open_middleArc P B hdisjoint hlocal cut hcut hmatch⟩

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
