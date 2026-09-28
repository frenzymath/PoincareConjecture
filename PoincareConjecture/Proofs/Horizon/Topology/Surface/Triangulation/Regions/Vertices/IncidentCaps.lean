


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Caps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Separators








set_option autoImplicit false
open Set
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  {r : M → ℝ} {p : M} (P : ChartCircleArrangementVertexPatch r p)

omit [T2Space M] in
theorem firstSide_closedSector_indices {ε : ℝ} (hwidth : ε ≤ P.width)
    {i j : Bool × Bool} (hij : i ≠ j) {q : M} (hqp : q ≠ p)
    (hq : q ∈ P.firstSide i ε) (hqj : q ∈ P.closedSector j) :
    ∀ s, q ∈ P.closedSector s → s = i ∨ s = j := by
  have hagree (s : Bool × Bool) (hs : q ∈ P.closedSector s) : s.1 = i.1 := by
    by_contra h
    exact hqp (P.firstSide_inter_opposite_sector (Ne.symm h) hwidth ⟨hq, hs⟩)
  have hj := hagree j hqj
  have hne : i.2 ≠ j.2 := fun h => hij (Prod.ext hj.symm h)
  intro s hs
  have hm : s.2 = i.2 ∨ s.2 = j.2 := by
    cases hi : i.2 <;> cases hj : j.2 <;> cases hs : s.2 <;> simp_all
  exact hm.elim (fun h => Or.inl (Prod.ext (hagree s hs) h))
    (fun h => Or.inr (Prod.ext ((hagree s hs).trans hj.symm) h))

omit [T2Space M] in
theorem secondSide_closedSector_indices {ε : ℝ} (hwidth : ε ≤ P.width)
    {i j : Bool × Bool} (hij : i ≠ j) {q : M} (hqp : q ≠ p)
    (hq : q ∈ P.secondSide i ε) (hqj : q ∈ P.closedSector j) :
    ∀ s, q ∈ P.closedSector s → s = i ∨ s = j := by
  have hagree (s : Bool × Bool) (hs : q ∈ P.closedSector s) : s.2 = i.2 := by
    by_contra h
    exact hqp (P.secondSide_inter_opposite_sector (Ne.symm h) hwidth ⟨hq, hs⟩)
  have hj := hagree j hqj
  have hne : i.1 ≠ j.1 := fun h => hij (Prod.ext h hj.symm)
  intro s hs
  have hm : s.1 = i.1 ∨ s.1 = j.1 := by
    cases hi : i.1 <;> cases hj : j.1 <;> cases hs : s.1 <;> simp_all
  exact hm.elim (fun h => Or.inl (Prod.ext h (hagree s hs)))
    (fun h => Or.inr (Prod.ext h ((hagree s hs).trans hj.symm)))

omit [T2Space M] in
theorem radial_endpoint_mem_openCarrier (i : Bool × Bool) (vertical : Bool)
    {ε : ℝ} (hε : 0 ≤ ε) (hwidth : ε < P.width) :
    P.sectorCoordinates i (if vertical then (0, ε) else (ε, 0)) ∈ P.openCarrier := by
  rw [P.openCarrier_eq_image_rectangle]
  refine ⟨collarParameterEquiv.symm
    (sectorParameterEquiv P.center i (if vertical then (0, ε) else (ε, 0))), ?_, rfl⟩
  rw [crossingOpenRectangle_eq]
  change (sectorParameterEquiv P.center i (if vertical then (0, ε) else (ε, 0))).1 ∈
      Ioo (P.center.1 - P.width) (P.center.1 + P.width) ∧
    (sectorParameterEquiv P.center i (if vertical then (0, ε) else (ε, 0))).2 ∈
      Ioo (P.center.2 - P.width) (P.center.2 + P.width)
  rcases i with ⟨i, j⟩
  cases vertical <;> cases i <;> cases j <;>
    simp only [sectorParameterEquiv_apply, Bool.false_eq_true, ite_false, ite_true,
      neg_zero, zero_add, mem_Ioo] <;>
    constructor <;> constructor <;> linarith [P.width_pos]

theorem carrier_subset_closure_sectors : P.carrier ⊆ closure (⋃ i, P.sector i) := by
  rw [← P.closedSectors_cover]
  apply iUnion_subset
  intro i
  rw [← P.closure_sector i]
  exact closure_mono (subset_iUnion (fun i => P.sector i) i)

end ChartCircleArrangementVertexPatch

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in
theorem edgeFromEndpoint_mem_open_edge (a : D.EdgeIndex) (terminal : Bool)
    {cut : ℝ} (hcut : cut ∈ Ioo (0 : ℝ) 1) :
    D.edgeFromEndpoint a terminal cut ∈ (D.edge a.1 a.2).map '' Ioo (0 : ℝ) 1 := by
  cases terminal
  · exact ⟨cut, hcut, rfl⟩
  · exact ⟨1 - cut, ⟨by linarith [hcut.2], by linarith [hcut.1]⟩, rfl⟩

omit [T2Space M] in
theorem edgeFromEndpoint_frontier_iff (a : D.EdgeIndex) (terminal : Bool)
    {cut : ℝ} (hcut : cut ∈ Ioo (0 : ℝ) 1) (R : D.regions) :
    D.edgeFromEndpoint a terminal cut ∈ frontier (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ↔
        R = D.regionLeft a ∨ R = D.regionRight a := by
  cases terminal
  · exact D.edge_interior_incidence a cut hcut R
  · exact D.edge_interior_incidence a (1 - cut)
      ⟨by linarith [hcut.2], by linarith [hcut.1]⟩ R



theorem region_eq_of_mem_frontier_two_sectors
    {p : M} (P : ChartCircleArrangementVertexPatch D.radius p)
    (region : Bool × Bool → D.regions)
    (hsector : ∀ i, P.sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i))
    {q : M} (hqP : q ∈ P.openCarrier) {i j : Bool × Bool}
    (honly : ∀ s, q ∈ P.closedSector s → s = i ∨ s = j)
    (R : D.regions)
    (hqR : q ∈ frontier (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)) :
    R = region i ∨ R = region j := by
  classical
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  let K : Set M := ⋃ s : {s : Bool × Bool // s ≠ i ∧ s ≠ j}, P.closedSector s
  have hK : IsClosed K := isClosed_iUnion_of_finite (fun s => (P.isCompact_closedSector s).isClosed)
  have hqK : q ∉ K := by
    intro hq
    obtain ⟨s, hs⟩ := mem_iUnion.mp hq
    exact (honly s hs).elim s.property.1 s.property.2
  let N := P.openCarrier ∩ Kᶜ
  have hN : IsOpen N := P.isOpen_openCarrier.inter hK.isOpen_compl
  have hqN : q ∈ N := ⟨hqP, hqK⟩
  let U := connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R
  have hU : IsOpen U := (isClosed_chartDiskBoundaryUnion D.centers D.radius).isOpen_compl.connectedComponentIn
  obtain ⟨z, hzN, hzU⟩ := mem_closure_iff.mp hqR.1 N hN hqN
  have hzdense := P.carrier_subset_closure_sectors (P.openCarrier_subset_carrier hzN.1)
  obtain ⟨w, hw, hwsector⟩ := mem_closure_iff.mp hzdense (N ∩ U) (hN.inter hU) ⟨hzN, hzU⟩
  obtain ⟨s, hs⟩ := mem_iUnion.mp hwsector
  have hsi : s = i ∨ s = j := by
    by_contra h
    push Not at h
    exact hw.1.2 (mem_iUnion.mpr ⟨⟨s, h⟩, P.sector_subset_closed s hs⟩)
  have hReq : R = region s := Subtype.ext
    (D.regions_distinct R R.property (region s) (region s).property
      ((connectedComponentIn_eq hw.2).trans (connectedComponentIn_eq (hsector s hs)).symm))
  exact hsi.elim (fun h => Or.inl (hReq.trans (congrArg region h)))
    (fun h => Or.inr (hReq.trans (congrArg region h)))



theorem matched_caps_incidence
    {p : D.vertices} {P : ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : Bool × Bool → M} (B : ChartCircleArrangementVertexPatch.VertexCapFaces P x)
    (region : Bool × Bool → D.regions)
    (hsector : ∀ i, P.sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i))
    (hclosed : ∀ i, P.closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i)))
    (a : D.EdgeIndex) (terminal : Bool) {cut : ℝ}
    (hcut : cut ∈ Ioo (0 : ℝ) 1) {i j : Bool × Bool} (hij : i ≠ j)
    (k : Fin 3) (hk : k = 1 ∨ k = 2)
    (hend : ∀ s, s = i ∨ s = j →
      ((B.face s).boundary k).map 1 = D.edgeFromEndpoint a terminal cut) :
    region i ≠ region j ∧
      (∀ R : D.regions, R = region i ∨ R = region j ↔
        R = D.regionLeft a ∨ R = D.regionRight a) ∧
      D.edgeFromEndpoint a terminal cut ∈ P.openCarrier ∧
      (∀ s, D.edgeFromEndpoint a terminal cut ∈ P.closedSector s ↔ s = i ∨ s = j) ∧
      ∀ s, D.edgeFromEndpoint a terminal cut ∈ (B.face s).carrier ↔ s = i ∨ s = j := by
  let q := D.edgeFromEndpoint a terminal cut
  have hqcap (s : Bool × Bool) (hs : s = i ∨ s = j) : q ∈ (B.face s).carrier :=
    (B.face s).isClosed_carrier.frontier_subset
      ((B.face s).boundary_image_subset_frontier k ⟨1, by norm_num, hend s hs⟩)
  have hqi := hqcap i (Or.inl rfl)
  have hqj := hqcap j (Or.inr rfl)
  have hqne : q ≠ (p : M) := by
    intro h
    have hqV : q ∈ (D.vertices : Set M) := h.symm ▸ p.property
    exact disjoint_left.mp (D.open_edge_disjoint_vertices a)
      (D.edgeFromEndpoint_mem_open_edge a terminal hcut) hqV
  have hqP : q ∈ P.openCarrier := by
    rcases hk with rfl | rfl
    · have heq : q = P.sectorCoordinates i (0, B.scale) := by
        simpa only [one_mul] using (hend i (Or.inl rfl)).symm.trans
          (B.second_map i 1 (by norm_num))
      rw [heq]
      exact P.radial_endpoint_mem_openCarrier i true B.scale_pos.le B.scale_lt_width
    · have heq : q = P.sectorCoordinates i (B.scale, 0) := by
        simpa only [one_mul] using (hend i (Or.inl rfl)).symm.trans
          (B.first_map i 1 (by norm_num))
      rw [heq]
      exact P.radial_endpoint_mem_openCarrier i false B.scale_pos.le B.scale_lt_width
  have honly : ∀ s, q ∈ P.closedSector s → s = i ∨ s = j := by
    rcases hk with rfl | rfl
    · apply P.secondSide_closedSector_indices B.scale_lt_width.le hij hqne
        ?_ (B.carrier_subset_sector j hqj)
      rw [← B.second_image i]
      exact ⟨1, by norm_num, hend i (Or.inl rfl)⟩
    · apply P.firstSide_closedSector_indices B.scale_lt_width.le hij hqne
        ?_ (B.carrier_subset_sector j hqj)
      rw [← B.first_image i]
      exact ⟨1, by norm_num, hend i (Or.inl rfl)⟩
  have hqK : q ∈ chartDiskBoundaryUnion D.centers D.radius := by
    rw [← D.boundary_cover]
    exact mem_iUnion.mpr ⟨a, image_mono Ioo_subset_Icc_self
      (D.edgeFromEndpoint_mem_open_edge a terminal hcut)⟩
  have hfront (s : Bool × Bool) (hs : s = i ∨ s = j) :
      q ∈ frontier (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region s)) := by
    refine ⟨hclosed s (B.carrier_subset_sector s (hqcap s hs)), ?_⟩
    intro hq
    exact connectedComponentIn_subset _ _ (interior_subset hq) hqK
  have hincident (R : D.regions) : R = region i ∨ R = region j ↔
      R = D.regionLeft a ∨ R = D.regionRight a := by
    rw [← D.edgeFromEndpoint_frontier_iff a terminal hcut R]
    constructor
    · rintro (rfl | rfl)
      · exact hfront i (Or.inl rfl)
      · exact hfront j (Or.inr rfl)
    · exact D.region_eq_of_mem_frontier_two_sectors P region hsector hqP honly R
  have hne : region i ≠ region j := by
    intro h
    have hl := (hincident (D.regionLeft a)).mpr (Or.inl rfl)
    have hr := (hincident (D.regionRight a)).mpr (Or.inr rfl)
    have hli : D.regionLeft a = region i := hl.elim id (fun he => he.trans h.symm)
    have hri : D.regionRight a = region i := hr.elim id (fun he => he.trans h.symm)
    exact D.region_sides_distinct a (hli.trans hri.symm)
  exact ⟨hne, hincident, hqP,
    fun s => ⟨honly s, fun hs => B.carrier_subset_sector s (hqcap s hs)⟩,
    fun s => ⟨fun hs => honly s (B.carrier_subset_sector s hs), hqcap s⟩⟩



theorem matched_caps_global_incidence
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (p : D.vertices) (a : D.EdgeIndex) (terminal : Bool) {cut : ℝ}
    (hcut : cut ∈ Ioo (0 : ℝ) 1) {i j : Bool × Bool} (hij : i ≠ j)
    (k : Fin 3) (hk : k = 1 ∨ k = 2)
    (hend : ∀ s, s = i ∨ s = j →
      (((B p).face s).boundary k).map 1 = D.edgeFromEndpoint a terminal cut) :
    region p i ≠ region p j ∧
      (∀ R : D.regions, R = region p i ∨ R = region p j ↔
        R = D.regionLeft a ∨ R = D.regionRight a) ∧
      ∀ v s, D.edgeFromEndpoint a terminal cut ∈ ((B v).face s).carrier ↔
        v = p ∧ (s = i ∨ s = j) := by
  obtain ⟨hne, hincident, _, _, hcap⟩ := D.matched_caps_incidence (B p) (region p)
    (hsector p) (hclosed p) a terminal hcut hij k hk hend
  refine ⟨hne, hincident, ?_⟩
  intro v s
  constructor
  · intro hq
    have hvp : v = p := by
      by_contra h
      exact disjoint_left.mp (hdisjoint v p h) ((B v).carrier_subset_patch s hq)
        ((B p).carrier_subset_patch i ((hcap i).mpr (Or.inl rfl)))
    subst v
    exact ⟨rfl, (hcap s).mp hq⟩
  · rintro ⟨rfl, hs⟩
    exact (hcap s).mpr hs


def vertexCapsInRegion
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions) (R : D.regions) : Set M :=
  ⋃ a : {a : D.vertices × (Bool × Bool) // region a.1 a.2 = R},
    ((B a.1.1).face a.1.2).carrier

omit [T2Space M] in
theorem isCompact_vertexCapsInRegion
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions) (R : D.regions) :
    IsCompact (D.vertexCapsInRegion B region R) :=
  isCompact_iUnion (fun a => ((B a.1.1).face a.1.2).isCompact_carrier_image)

omit [T2Space M] in
theorem vertexCapsInRegion_subset_union
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions) (R : D.regions) :
    D.vertexCapsInRegion B region R ⊆ ⋃ p, ⋃ s, ((B p).face s).carrier := by
  intro q hq
  obtain ⟨a, ha⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨a.1.1, mem_iUnion.mpr ⟨a.1.2, ha⟩⟩

theorem isClosed_vertexCapsInRegion
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions) (R : D.regions) :
    IsClosed (D.vertexCapsInRegion B region R) :=
  isClosed_iUnion_of_finite (fun a => ((B a.1.1).face a.1.2).isClosed_carrier)



theorem exists_neighborhood_vertexCapsInRegion_eq_cap
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions)
    {p : D.vertices} {i : Bool × Bool} {R : D.regions} {q : M}
    (hregion : region p i = R)
    (hunique : ∀ v s, q ∈ ((B v).face s).carrier → region v s = R → v = p ∧ s = i) :
    ∃ N : Set M, IsOpen N ∧ q ∈ N ∧
      N ∩ D.vertexCapsInRegion B region R = N ∩ ((B p).face i).carrier := by
  classical
  let K : Set M := ⋃ a : {a : D.vertices × (Bool × Bool) //
      region a.1 a.2 = R ∧ a ≠ (p, i)}, ((B a.1.1).face a.1.2).carrier
  have hK : IsClosed K := isClosed_iUnion_of_finite
    (fun a => ((B a.1.1).face a.1.2).isClosed_carrier)
  have hqK : q ∉ K := by
    intro hq
    obtain ⟨a, ha⟩ := mem_iUnion.mp hq
    obtain ⟨hp, hi⟩ := hunique a.1.1 a.1.2 ha a.property.1
    exact a.property.2 (Prod.ext hp hi)
  refine ⟨Kᶜ, hK.isOpen_compl, hqK, ?_⟩
  apply subset_antisymm
  · rintro z ⟨hzK, hz⟩
    obtain ⟨a, ha⟩ := mem_iUnion.mp hz
    by_cases h : a.val = (p, i)
    · obtain ⟨hp, hi⟩ := Prod.mk.inj h
      subst p i
      exact ⟨hzK, ha⟩
    · exact False.elim (hzK (mem_iUnion.mpr ⟨⟨a.val, a.property, h⟩, ha⟩))
  · rintro z ⟨hzK, hz⟩
    exact ⟨hzK, mem_iUnion.mpr ⟨⟨(p, i), hregion⟩, hz⟩⟩



theorem exists_incident_region_cap_neighborhood
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (p : D.vertices) (a : D.EdgeIndex) (terminal : Bool) {cut : ℝ}
    (hcut : cut ∈ Ioo (0 : ℝ) 1) {i j : Bool × Bool} (hij : i ≠ j)
    (k : Fin 3) (hk : k = 1 ∨ k = 2)
    (hend : ∀ s, s = i ∨ s = j →
      (((B p).face s).boundary k).map 1 = D.edgeFromEndpoint a terminal cut)
    (R : D.regions) (hR : R = D.regionLeft a ∨ R = D.regionRight a) :
    ∃ (s : Bool × Bool) (N : Set M), (s = i ∨ s = j) ∧ region p s = R ∧
      IsOpen N ∧ D.edgeFromEndpoint a terminal cut ∈ N ∧
      D.edgeFromEndpoint a terminal cut ∈ ((B p).face s).carrier ∧
      (∀ v t, D.edgeFromEndpoint a terminal cut ∈ ((B v).face t).carrier →
        region v t = R → v = p ∧ t = s) ∧
      N ∩ D.vertexCapsInRegion B region R = N ∩ ((B p).face s).carrier := by
  obtain ⟨hne, hincident, hcap⟩ := D.matched_caps_global_incidence P B region hdisjoint
    hsector hclosed p a terminal hcut hij k hk hend
  obtain ⟨s, hs, hsR⟩ : ∃ s, (s = i ∨ s = j) ∧ region p s = R := by
    rcases (hincident R).mpr hR with h | h
    · exact ⟨i, Or.inl rfl, h.symm⟩
    · exact ⟨j, Or.inr rfl, h.symm⟩
  have hunique : ∀ v t, D.edgeFromEndpoint a terminal cut ∈ ((B v).face t).carrier →
      region v t = R → v = p ∧ t = s := by
    intro v t ht htR
    obtain ⟨rfl, ht⟩ := (hcap v t).mp ht
    refine ⟨rfl, ?_⟩
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact False.elim (hne (hsR.trans htR.symm))
    · exact False.elim (hne (htR.trans hsR.symm))
    · rfl
  obtain ⟨N, hN, hqN, heq⟩ :=
    D.exists_neighborhood_vertexCapsInRegion_eq_cap B region hsR hunique
  exact ⟨s, N, hs, hsR, hN, hqN, (hcap p s).mpr ⟨rfl, hs⟩, hunique, heq⟩

omit [T2Space M] in

theorem vertexCapsInRegion_subset_chart
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
      (fun s => chart (region p s))) (R : D.regions) :
    D.vertexCapsInRegion B region R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source := by
  intro q hq
  obtain ⟨a, ha⟩ := mem_iUnion.mp hq
  have h := (B a.1.1).carrier_subset_chart a.1.2 ha
  simpa only [a.property] using h

omit [T2Space M] in


theorem isClosed_chart_vertexCapsInRegion
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
      (fun s => chart (region p s))) (R : D.regions) :
    IsClosed ((chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)) '' D.vertexCapsInRegion B region R) :=
  ((D.isCompact_vertexCapsInRegion B region R).image_of_continuousOn
    ((chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).continuousOn.mono
      (D.vertexCapsInRegion_subset_chart region chart B R))).isClosed



theorem exists_incident_region_cap_separator
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
      (fun s => chart (region p s)))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (p : D.vertices) (a : D.EdgeIndex) (terminal : Bool) {cut : ℝ}
    (hcut : cut ∈ Ioo (0 : ℝ) 1) {i j : Bool × Bool} (hij : i ≠ j)
    (k : Fin 3) (hk : k = 1 ∨ k = 2)
    (hend : ∀ s, s = i ∨ s = j →
      (((B p).face s).boundary k).map 1 = D.edgeFromEndpoint a terminal cut)
    (hparameters : ∀ s, s = i ∨ s = j → ∃ A : OpenPartialHomeomorph ℝ ℝ,
      A (B p).scale = cut ∧ Icc 0 (B p).scale ⊆ A.source ∧
      StrictMonoOn A A.source ∧ ContDiffOn ℝ ∞ A A.source ∧
      ∀ u ∈ Icc 0 (B p).scale, D.edgeFromEndpoint a terminal (A u) =
        (P p).sectorCoordinates s (if k = 1 then (0, u) else (u, 0)))
    (R : D.regions) (hR : R = D.regionLeft a ∨ R = D.regionRight a) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
    ∃ (s : Bool × Bool) (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (W : Set (EuclideanSpace ℝ (Fin 2))),
      (s = i ∨ s = j) ∧ region p s = R ∧ IsOpen W ∧
      c (D.edgeFromEndpoint a terminal cut) ∈ W ∧
      0 < ℓ (deriv (c ∘ D.edgeFromEndpoint a terminal) cut) ∧
      (if terminal then ℓ (deriv (c ∘ (D.edge a.1 a.2).map) (1 - cut)) < 0
       else 0 < ℓ (deriv (c ∘ (D.edge a.1 a.2).map) cut)) ∧
      (∀ t : ℝ, ℓ ((1 - t) • (B p).planarCoordinates s ((B p).scale, 0) +
        t • (B p).planarCoordinates s (0, (B p).scale) -
          c (D.edgeFromEndpoint a terminal cut)) = 0) ∧
      ∀ z ∈ (c '' D.vertexCapsInRegion B region R) ∩ W,
        ℓ (z - c (D.edgeFromEndpoint a terminal cut)) ≤ 0 := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
  obtain ⟨s, N, hs, hsR, hN, hqN, hqcap, _, hNeq⟩ :=
    D.exists_incident_region_cap_neighborhood P B region hdisjoint hsector hclosed
      p a terminal hcut hij k hk hend R hR
  obtain ⟨A, hAt, hsource, hmono, hA, hcurve⟩ := hparameters s hs
  have hcurve' : ∀ u ∈ Icc 0 (B p).scale, D.edgeFromEndpoint a terminal (A u) =
      (P p).sectorCoordinates s (if decide (k = 1) then (0, u) else (u, 0)) := by
    simpa only [decide_eq_true_eq] using hcurve
  obtain ⟨ℓ, W, hW, hqW, hpos, hsign, hchord, hsep⟩ :=
    D.exists_edge_cap_separator (B p) s a terminal (decide (k = 1))
      A hAt hsource hmono hA hcurve'
  simp only [hsR] at hqW hpos hsign hchord hsep
  have hqsource : D.edgeFromEndpoint a terminal cut ∈ c.source := by
    simpa only [hsR] using (B p).carrier_subset_chart s hqcap
  let W' := W ∩ c '' (N ∩ c.source)
  have hW' : IsOpen W' := hW.inter
    (c.isOpen_image_of_subset_source (hN.inter c.open_source) inter_subset_right)
  have hqW' : c (D.edgeFromEndpoint a terminal cut) ∈ W' :=
    ⟨hqW, D.edgeFromEndpoint a terminal cut, ⟨hqN, hqsource⟩, rfl⟩
  refine ⟨s, ℓ, W', hs, hsR, hW', hqW', hpos, hsign, hchord, ?_⟩
  rintro z ⟨⟨q, hq, hqz⟩, hzW, v, hv, hvz⟩
  have hqsource := D.vertexCapsInRegion_subset_chart region chart B R hq
  have hqv : q = v := c.injOn hqsource hv.2 (hqz.trans hvz.symm)
  have hqN : q ∈ N := hqv.symm ▸ hv.1
  have hqcap : q ∈ ((B p).face s).carrier :=
    (hNeq ▸ (show q ∈ N ∩ D.vertexCapsInRegion B region R from ⟨hqN, hq⟩)).2
  have hz : ℓ (c q - c (D.edgeFromEndpoint a terminal cut)) ≤ 0 :=
    hsep q hqcap (hqz ▸ hzW)
  rwa [hqz] at hz

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
