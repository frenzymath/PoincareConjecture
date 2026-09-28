import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.GraphNeighborhoods
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Strip

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in

theorem exists_regions_of_two_sided_neighborhood (e : D.EdgeIndex)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {W U V : Set M}
    (hW : W ∈ 𝓝 ((D.edge e.1 e.2).map t))
    (hpartition : W \ chartDiskBoundaryUnion D.centers D.radius = U ∪ V)
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hUne : U.Nonempty) (hVne : V.Nonempty)
    (hUclosure : (D.edge e.1 e.2).map t ∈ closure U)
    (hVclosure : (D.edge e.1 e.2).map t ∈ closure V) :
    ∃ upper lower : D.regions, upper ≠ lower ∧
      (∀ q : D.regions, q = upper ∨ q = lower ↔ q = D.regionLeft e ∨ q = D.regionRight e) ∧
      U ⊆ connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper ∧
      V ⊆ connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower ∧
      W ∩ connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper = U ∧
      W ∩ connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower = V := by
  let K := chartDiskBoundaryUnion D.centers D.radius
  have hUK : U ⊆ Kᶜ := by
    intro z hz
    exact (show z ∈ W \ K from hpartition ▸ Or.inl hz).2
  have hVK : V ⊆ Kᶜ := by
    intro z hz
    exact (show z ∈ W \ K from hpartition ▸ Or.inr hz).2
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨v, hv⟩ := hVne
  obtain ⟨upper, hupper⟩ := D.region_representative u (hUK hu)
  obtain ⟨lower, hlower⟩ := D.region_representative v (hVK hv)
  have hindex {q s : D.regions}
      (heq : connectedComponentIn Kᶜ q = connectedComponentIn Kᶜ s) : q = s :=
    Subtype.ext (D.regions_distinct q q.property s s.property heq)
  have hpK : (D.edge e.1 e.2).map t ∈ K := by
    change (D.edge e.1 e.2).map t ∈ chartDiskBoundaryUnion D.centers D.radius
    rw [← D.boundary_cover]
    exact mem_iUnion.mpr ⟨e, t, Ioo_subset_Icc_self ht, rfl⟩
  have hincident (q : D.regions) : q = upper ∨ q = lower ↔
      q = D.regionLeft e ∨ q = D.regionRight e := by
    rw [← D.edge_interior_incidence e t ht q]
    rw [Poincare.Topology.mem_frontier_connectedComponentIn_iff_of_two_sided_neighborhood
      hW hpartition hU hV hu hv hpK hUclosure hVclosure, hupper, hlower]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact fun h => h.elim (fun h => Or.inl (hindex h)) (fun h => Or.inr (hindex h))
  have hne : upper ≠ lower := by
    intro heq
    have hl := (hincident (D.regionLeft e)).mpr (Or.inl rfl)
    have hr := (hincident (D.regionRight e)).mpr (Or.inr rfl)
    have hlu : D.regionLeft e = upper := hl.elim id (fun h => h.trans heq.symm)
    have hru : D.regionRight e = upper := hr.elim id (fun h => h.trans heq.symm)
    exact D.region_sides_distinct e (hlu.trans hru.symm)
  have hUC : U ⊆ connectedComponentIn Kᶜ upper := by
    rw [← hupper]
    exact hU.subset_connectedComponentIn hu hUK
  have hVC : V ⊆ connectedComponentIn Kᶜ lower := by
    rw [← hlower]
    exact hV.subset_connectedComponentIn hv hVK
  have hdis : Disjoint (connectedComponentIn Kᶜ upper) (connectedComponentIn Kᶜ lower) := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact hne (hindex ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm))
  refine ⟨upper, lower, hne, hincident, hUC, hVC, ?_, ?_⟩
  · apply subset_antisymm
    · intro z hz
      have hloc : z ∈ U ∪ V := hpartition ▸
        (show z ∈ W \ K from ⟨hz.1, connectedComponentIn_subset _ _ hz.2⟩)
      exact hloc.resolve_right (fun hzV => disjoint_left.mp hdis hz.2 (hVC hzV))
    · intro z hz
      exact ⟨(show z ∈ W \ K from hpartition ▸ Or.inl hz).1, hUC hz⟩
  · apply subset_antisymm
    · intro z hz
      have hloc : z ∈ U ∪ V := hpartition ▸
        (show z ∈ W \ K from ⟨hz.1, connectedComponentIn_subset _ _ hz.2⟩)
      exact hloc.resolve_left (fun hzU => disjoint_left.mp hdis (hUC hzU) hz.2)
    · intro z hz
      exact ⟨(show z ∈ W \ K from hpartition ▸ Or.inr hz).1, hVC hz⟩

omit [T2Space M] in

theorem exists_rectangle_incident_regions (e : D.EdgeIndex)
    (H : OpenPartialHomeomorph (ℝ × ℝ) M)
    {a b δ x t : ℝ} (hab : a < b) (hδ : 0 < δ) (hx : x ∈ Ioo a b)
    (ht : t ∈ Ioo (0 : ℝ) 1) (haxis : H (x, 0) = (D.edge e.1 e.2).map t)
    (hsource : Icc a b ×ˢ Icc (-δ) δ ⊆ H.source)
    (hboundary : ∀ q ∈ Icc a b ×ˢ Icc (-δ) δ,
      H q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q.2 = 0) :
    ∃ upper lower : D.regions, upper ≠ lower ∧
      (∀ q : D.regions, q = upper ∨ q = lower ↔ q = D.regionLeft e ∨ q = D.regionRight e) ∧
      H '' (Ioo a b ×ˢ Ioo 0 δ) ⊆ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper ∧
      H '' (Ioo a b ×ˢ Ioo (-δ) 0) ⊆ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower ∧
      H '' (Icc a b ×ˢ Icc 0 δ) ⊆ closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper) ∧
      H '' (Icc a b ×ˢ Icc (-δ) 0) ⊆ closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower) ∧
      (H '' (Ioo a b ×ˢ Ioo (-δ) δ)) ∩ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper = H '' (Ioo a b ×ˢ Ioo 0 δ) ∧
      (H '' (Ioo a b ×ˢ Ioo (-δ) δ)) ∩ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower = H '' (Ioo a b ×ˢ Ioo (-δ) 0) := by
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-δ) δ
  let U : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo 0 δ
  let V : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-δ) 0
  have hR : R ⊆ H.source :=
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans hsource
  have hUR : U ⊆ R := by
    intro q hq
    exact ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
  have hVR : V ⊆ R := by
    intro q hq
    exact ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
  have hopen : IsOpen (H '' R) := H.isOpen_image_of_subset_source
    (isOpen_Ioo.prod isOpen_Ioo) hR
  have hpR : (x, (0 : ℝ)) ∈ R := ⟨hx, by constructor <;> linarith⟩
  have hW : H '' R ∈ 𝓝 ((D.edge e.1 e.2).map t) :=
    hopen.mem_nhds ⟨(x, 0), hpR, haxis⟩
  have hpartition : H '' R \ chartDiskBoundaryUnion D.centers D.radius =
      H '' U ∪ H '' V := by
    apply subset_antisymm
    · rintro z ⟨⟨q, hq, rfl⟩, hqK⟩
      have hqclosed : q ∈ Icc a b ×ˢ Icc (-δ) δ :=
        ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩
      have hne : q.2 ≠ 0 := fun h => hqK ((hboundary q hqclosed).mpr h)
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact Or.inr ⟨q, ⟨hq.1, hq.2.1, hneg⟩, rfl⟩
      · exact Or.inl ⟨q, ⟨hq.1, hpos, hq.2.2⟩, rfl⟩
    · rintro z (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · have hqr := hUR hq
        refine ⟨⟨q, hqr, rfl⟩, ?_⟩
        intro hK
        have hzero := (hboundary q ⟨Ioo_subset_Icc_self hqr.1,
          Ioo_subset_Icc_self hqr.2⟩).mp hK
        exact (ne_of_gt hq.2.1) hzero
      · have hqr := hVR hq
        refine ⟨⟨q, hqr, rfl⟩, ?_⟩
        intro hK
        have hzero := (hboundary q ⟨Ioo_subset_Icc_self hqr.1,
          Ioo_subset_Icc_self hqr.2⟩).mp hK
        exact (ne_of_lt hq.2.2) hzero
  have hU : IsPreconnected (H '' U) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image H (H.continuousOn.mono (hUR.trans hR))
  have hV : IsPreconnected (H '' V) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image H (H.continuousOn.mono (hVR.trans hR))
  have hUne : (H '' U).Nonempty := ⟨H (x, δ / 2), (x, δ / 2),
    ⟨hx, by constructor <;> linarith⟩, rfl⟩
  have hVne : (H '' V).Nonempty := ⟨H (x, -δ / 2), (x, -δ / 2),
    ⟨hx, by constructor <;> linarith⟩, rfl⟩
  have hclU : closure U = Icc a b ×ˢ Icc 0 δ := by
    change closure (Ioo a b ×ˢ Ioo 0 δ) = _
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo hδ.ne]
  have hclV : closure V = Icc a b ×ˢ Icc (-δ) 0 := by
    change closure (Ioo a b ×ˢ Ioo (-δ) 0) = _
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo (by linarith : -δ ≠ 0)]
  have hUcl : (D.edge e.1 e.2).map t ∈ closure (H '' U) := by
    rw [← haxis]
    apply mem_closure_image (H.continuousAt (hR hpR))
    rw [hclU]
    exact ⟨Ioo_subset_Icc_self hx, le_rfl, hδ.le⟩
  have hVcl : (D.edge e.1 e.2).map t ∈ closure (H '' V) := by
    rw [← haxis]
    apply mem_closure_image (H.continuousAt (hR hpR))
    rw [hclV]
    exact ⟨Ioo_subset_Icc_self hx, by linarith, le_rfl⟩
  obtain ⟨upper, lower, hne, hpair, hupper, hlower, hupper_exact, hlower_exact⟩ :=
    D.exists_regions_of_two_sided_neighborhood e ht hW hpartition hU hV hUne hVne hUcl hVcl
  refine ⟨upper, lower, hne, hpair, hupper, hlower, ?_, ?_, hupper_exact, hlower_exact⟩
  · rintro z ⟨q, hq, rfl⟩
    apply closure_mono hupper
    apply mem_closure_image (H.continuousAt (hsource ⟨hq.1, by
      constructor <;> linarith [hq.2.1, hq.2.2]⟩))
    rwa [hclU]
  · rintro z ⟨q, hq, rfl⟩
    apply closure_mono hlower
    apply mem_closure_image (H.continuousAt (hsource ⟨hq.1, by
      constructor <;> linarith [hq.2.1, hq.2.2]⟩))
    rwa [hclV]

theorem exists_edge_graph_incident_regions (e : D.EdgeIndex)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (G : OpenPartialHomeomorph ℝ ℝ) (h : ℝ → ℝ)
    {a b l r : ℝ} (hab : a ≤ b) (hla : l < a) (hbr : b < r)
    (ha : 0 < a) (hb : b < 1) (hGsource : G.source = Ioo l r)
    (hmono : StrictMonoOn G G.source) (hh : ContDiffOn ℝ ∞ h G.target)
    (hgraph_source : ∀ x ∈ G.target, collarParameterEquiv.symm (x, h x) ∈ F.source)
    (hgraph : ∀ t ∈ G.source, (D.edge e.1 e.2).map t =
      F (collarParameterEquiv.symm (G t, h (G t)))) :
    ∃ (α β δ : ℝ) (upper lower : D.regions), α < G a ∧ G b < β ∧
      0 < δ ∧ upper ≠ lower ∧
      (∀ q : D.regions, q = upper ∨ q = lower ↔ q = D.regionLeft e ∨ q = D.regionRight e) ∧
      ∀ x ∈ Ioo α β, ∀ z : ℝ, |z| < δ →
        collarParameterEquiv.symm (x, h x + z) ∈ F.source ∧
        (F (collarParameterEquiv.symm (x, h x + z)) ∈
          chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) ∧
        (0 < z → F (collarParameterEquiv.symm (x, h x + z)) ∈
          connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper) ∧
        (z < 0 → F (collarParameterEquiv.symm (x, h x + z)) ∈
          connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower) ∧
        (0 ≤ z → F (collarParameterEquiv.symm (x, h x + z)) ∈
          closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper)) ∧
        (z ≤ 0 → F (collarParameterEquiv.symm (x, h x + z)) ∈
          closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower)) := by
  let c := (max l 0 + a) / 2
  let d := (b + min r 1) / 2
  have hc : max l 0 < c ∧ c < a := by
    have h := max_lt hla ha
    dsimp [c]
    constructor <;> linarith
  have hd : b < d ∧ d < min r 1 := by
    have h := lt_min hbr hb
    dsimp [d]
    constructor <;> linarith
  have hcd : c < d := hc.2.trans_le hab |>.trans hd.1
  have hlc : l < c := (le_max_left l 0).trans_lt hc.1
  have hc0 : 0 < c := (le_max_right l 0).trans_lt hc.1
  have hdr : d < r := hd.2.trans_le (min_le_left r 1)
  have hd1 : d < 1 := hd.2.trans_le (min_le_right r 1)
  have hI : Icc c d ⊆ G.source := by
    rw [hGsource]
    exact fun t ht => ⟨hlc.trans_le ht.1, ht.2.trans_lt hdr⟩
  have hcG := hI (left_mem_Icc.mpr hcd.le)
  have hdG := hI (right_mem_Icc.mpr hcd.le)
  have haG := hI (show a ∈ Icc c d from ⟨hc.2.le, (hab.trans hd.1.le)⟩)
  have hbG := hI (show b ∈ Icc c d from ⟨hc.2.le.trans hab, hd.1.le⟩)
  have hGcGd : G c < G d := hmono hcG hdG hcd
  have hGa : G c < G a := hmono hcG haG hc.2
  have hGb : G b < G d := hmono hbG hdG hd.1
  obtain ⟨X, ε, hX, hIX, hXG, hε, htube⟩ :=
    D.exists_edge_graph_tube e F G h hcd.le hlc hdr hc0 hd1 hGsource hmono
      hh.continuousOn hgraph_source hgraph
  let P := graphStripCoordinates G.open_target hh (hh.add contDiffOn_const)
    (show ∀ x ∈ G.target, h x < h x + 1 from fun _ _ => by linarith)
  let H := (P.trans collarParameterEquiv.symm.toHomeomorph.toOpenPartialHomeomorph).trans F
  have hH (q : ℝ × ℝ) : H q = F (collarParameterEquiv.symm (q.1, h q.1 + q.2)) := by
    simp [H, P, graphStripCoordinates, graphStripMap]
  have hδ : 0 < ε / 2 := by linarith
  have hsource : Icc (G c) (G d) ×ˢ Icc (-(ε / 2)) (ε / 2) ⊆ H.source := by
    intro q hq
    have hqabs : |q.2| < ε := abs_lt.mpr (by constructor <;> linarith [hq.2.1, hq.2.2])
    refine ⟨⟨⟨hXG (hIX hq.1), mem_univ _⟩, mem_univ _⟩, ?_⟩
    simpa [P, graphStripCoordinates, graphStripMap] using (htube q.1 (hIX hq.1) q.2 hqabs).1
  have hboundary : ∀ q ∈ Icc (G c) (G d) ×ˢ Icc (-(ε / 2)) (ε / 2),
      H q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q.2 = 0 := by
    intro q hq
    rw [hH]
    exact (htube q.1 (hIX hq.1) q.2
      (abs_lt.mpr (by constructor <;> linarith [hq.2.1, hq.2.2]))).2
  have haxis : H (G a, 0) = (D.edge e.1 e.2).map a := by
    rw [hH]
    simpa using (hgraph a haG).symm
  obtain ⟨upper, lower, hne, hpair, hupper, hlower, hupperCl, hlowerCl, _, _⟩ :=
    D.exists_rectangle_incident_regions e H hGcGd hδ
      ⟨hGa, (hmono.monotoneOn haG hbG hab).trans_lt hGb⟩
      ⟨ha, hab.trans_lt hb⟩ haxis hsource hboundary
  refine ⟨G c, G d, ε / 2, upper, lower, hGa, hGb, hδ, hne, hpair, ?_⟩
  intro x hx z hz
  have hxopen : x ∈ Ioo (G c) (G d) := hx
  have hzx := abs_lt.mp hz
  have htube := htube x (hIX (Ioo_subset_Icc_self hxopen)) z (by linarith)
  refine ⟨htube.1, htube.2, ?_, ?_, ?_, ?_⟩
  · intro hzpos
    exact hupper ⟨(x, z), ⟨hxopen, hzpos, hzx.2⟩, hH (x, z)⟩
  · intro hzneg
    exact hlower ⟨(x, z), ⟨hxopen, hzx.1, hzneg⟩, hH (x, z)⟩
  · intro hzpos
    exact hupperCl ⟨(x, z), ⟨Ioo_subset_Icc_self hxopen, hzpos, hzx.2.le⟩, hH (x, z)⟩
  · intro hzneg
    exact hlowerCl ⟨(x, z), ⟨Ioo_subset_Icc_self hxopen, hzx.1.le, hzneg⟩, hH (x, z)⟩

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
