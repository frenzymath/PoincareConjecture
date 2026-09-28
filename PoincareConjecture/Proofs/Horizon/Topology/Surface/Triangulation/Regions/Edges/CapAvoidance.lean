


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.EdgeIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.IncidentCaps
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.EndpointBarriers








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Manifold
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

private theorem linear_graph_deriv
    {f : ℝ → EuclideanSpace ℝ (Fin 2)}
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hh : ContDiffOn ℝ ∞ h G.target)
    (hgraph : ∀ t ∈ G.source, L (f t) = (G t, h (G t)))
    {t : ℝ} (ht : t ∈ G.source) (hf : DifferentiableAt ℝ f t) :
    L (deriv f t) = deriv G t • ((1 : ℝ), deriv h (G t)) := by
  have hdG := ((hG t ht).contDiffAt (G.open_source.mem_nhds ht)).differentiableAt (by simp)
  have hdh := ((hh (G t) (G.map_source ht)).contDiffAt
    (G.open_target.mem_nhds (G.map_source ht))).differentiableAt (by simp)
  have hdleft := L.hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
  have hdright := hdG.hasDerivAt.prodMk (hdh.hasDerivAt.comp t hdG.hasDerivAt)
  have heq : (L ∘ f) =ᶠ[𝓝 t] (fun u => (G u, h (G u))) :=
    Filter.mem_of_superset (G.open_source.mem_nhds ht) (hgraph ·)
  have hderiv := hdleft.unique (hdright.congr_of_eventuallyEq heq)
  change L (deriv f t) = (deriv G t, deriv h (G t) * deriv G t) at hderiv
  rw [hderiv]
  ext <;> simp [smul_eq_mul, mul_comm]

private theorem linear_graph_separator_sign
    {f : ℝ → EuclideanSpace ℝ (Fin 2)}
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hh : ContDiffOn ℝ ∞ h G.target)
    (hgraph : ∀ t ∈ G.source, L (f t) = (G t, h (G t)))
    {t : ℝ} (ht : t ∈ G.source) (hf : DifferentiableAt ℝ f t)
    (hprojection : 0 < (L (deriv f t)).1)
    (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (terminal : Bool)
    (hsign : if terminal then ℓ (deriv f t) < 0 else 0 < ℓ (deriv f t)) :
    if terminal then (ℓ.comp L.symm.toContinuousLinearMap) (1, deriv h (G t)) < 0
    else 0 < (ℓ.comp L.symm.toContinuousLinearMap) (1, deriv h (G t)) := by
  have hd := linear_graph_deriv L G hG hh hgraph ht hf
  have hdG : 0 < deriv G t := by
    have h := congrArg Prod.fst hd
    simp only [Prod.smul_mk, smul_eq_mul, mul_one] at h
    exact h ▸ hprojection
  have heq : ℓ (deriv f t) =
      deriv G t * (ℓ.comp L.symm.toContinuousLinearMap) (1, deriv h (G t)) := by
    have h := congrArg (fun z => ℓ (L.symm z)) hd
    simpa only [L.symm_apply_apply, map_smul, smul_eq_mul,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using h
  rw [heq] at hsign
  cases terminal
  · exact (mul_pos_iff_of_pos_left hdG).mp hsign
  · exact neg_of_mul_neg_right hsign hdG.le

private theorem exists_transverse_barrier_off_closed_set
    {C : Set (ℝ × ℝ)} (hC : IsClosed C) {h : ℝ → ℝ} {x u w : ℝ}
    (hx : (x, h x) ∉ C) (htrans : 0 < w - deriv h x * u) (terminal : Bool) :
    ∃ (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (W : Set (ℝ × ℝ)),
      IsOpen W ∧ (x, h x) ∈ W ∧ ℓ (u, w) = 0 ∧
      (if terminal then ℓ (1, deriv h x) < 0 else 0 < ℓ (1, deriv h x)) ∧
      ∀ q ∈ C ∩ W, ℓ (q - (x, h x)) ≤ 0 := by
  let N : (ℝ × ℝ) →L[ℝ] ℝ :=
    w • ContinuousLinearMap.fst ℝ ℝ ℝ - u • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hN (q : ℝ × ℝ) : N q = w * q.1 - u * q.2 := rfl
  have hzero : N (u, w) = 0 := by rw [hN]; ring
  have hpos : 0 < N (1, deriv h x) := by
    rw [hN]
    nlinarith only [htrans]
  refine ⟨if terminal then -N else N, Cᶜ, hC.isOpen_compl, hx, ?_, ?_, ?_⟩
  · cases terminal <;> simp [hzero]
  · cases terminal <;> simp [hpos]
  · rintro q ⟨hq, hq'⟩
    exact False.elim (hq' hq)

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

section CapFamily

variable
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
      (fun s => chart (region p s))) (R : D.regions)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))


def graphCapObstacle : Set (ℝ × ℝ) :=
  L '' ((chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)) '' D.vertexCapsInRegion B region R)

omit [T2Space M] in
theorem isClosed_graphCapObstacle : IsClosed (D.graphCapObstacle region chart B R L) :=
  L.toHomeomorph.isClosedMap _ (D.isClosed_chart_vertexCapsInRegion region chart B R)

omit [T2Space M] in
theorem graphCapObstacle_subset_source :
    D.graphCapObstacle region chart B R L ⊆ collarParameterEquiv.symm ⁻¹'
      (linearGraphCoordinates (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm L).source := by
  rintro z ⟨w, ⟨q, hq, rfl⟩, rfl⟩
  refine ⟨mem_univ _, ?_⟩
  change L.symm (collarParameterEquiv (collarParameterEquiv.symm
    (L (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) q)))) ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).target
  rw [collarParameterEquiv.apply_symm_apply, L.symm_apply_apply]
  exact (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).map_source
    (D.vertexCapsInRegion_subset_chart region chart B R hq)

omit [T2Space M] in


theorem graphCapObstacle_surface_image :
    (fun z : ℝ × ℝ => linearGraphCoordinates
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm L (collarParameterEquiv.symm z)) ''
        D.graphCapObstacle region chart B R L = D.vertexCapsInRegion B region R := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
  have hmap (q : M) (hq : q ∈ D.vertexCapsInRegion B region R) :
      linearGraphCoordinates c.symm L (collarParameterEquiv.symm (L (c q))) = q := by
    rw [linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply, L.symm_apply_apply]
    exact c.left_inv (D.vertexCapsInRegion_subset_chart region chart B R hq)
  apply subset_antisymm
  · rintro z ⟨w, ⟨v, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    change linearGraphCoordinates c.symm L (collarParameterEquiv.symm (L (c q))) ∈ _
    rw [hmap q hq]
    exact hq
  · intro q hq
    exact ⟨L (c q), ⟨c q, ⟨q, hq, rfl⟩, rfl⟩, hmap q hq⟩

omit [T2Space M] in


theorem graph_piece_avoids_caps (a : D.EdgeIndex)
    (cut : D.EdgeIndex → Bool → ℝ)
    (havoid : Disjoint (⋃ p, ⋃ s, ((B p).face s).carrier)
      ((D.edge a.1 a.2).map '' Ioo (cut a false) (1 - cut a true)))
    {α β : ℝ} (hα : cut a false ≤ α) (hβ : β ≤ 1 - cut a true)
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hI : Icc α β ⊆ G.source)
    (hsource : G.source ⊆ (D.edge a.1 a.2).map ⁻¹'
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source)
    (himage : G '' Icc α β = Icc (G α) (G β))
    (hgraph : ∀ t ∈ G.source,
      L (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge a.1 a.2).map t)) =
        (G t, h (G t))) :
    ∀ x ∈ Ioo (G α) (G β), (x, h x) ∉ D.graphCapObstacle region chart B R L := by
  intro x hx hmem
  have hxI : x ∈ G '' Icc α β := himage.symm ▸ Ioo_subset_Icc_self hx
  obtain ⟨t, ht, htx⟩ := hxI
  have hta : t ≠ α := fun he => (ne_of_gt hx.1) (htx.symm.trans (congrArg G he))
  have htb : t ≠ β := fun he => (ne_of_lt hx.2) (htx.symm.trans (congrArg G he))
  have htopen : t ∈ Ioo (cut a false) (1 - cut a true) :=
    ⟨hα.trans_lt (lt_of_le_of_ne ht.1 (Ne.symm hta)),
      (lt_of_le_of_ne ht.2 htb).trans_le hβ⟩
  obtain ⟨z, ⟨q, hq, rfl⟩, hqgraph⟩ := hmem
  have hedgegraph := hgraph t (hI ht)
  rw [htx] at hedgegraph
  have hqe : q = (D.edge a.1 a.2).map t :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).injOn
      (D.vertexCapsInRegion_subset_chart region chart B R hq) (hsource (hI ht))
      (L.injective (hqgraph.trans hedgegraph.symm))
  exact disjoint_left.mp havoid
    (D.vertexCapsInRegion_subset_union B region R hq) ⟨t, htopen, hqe.symm⟩

omit [T2Space M] in


theorem edge_graph_point_avoids_caps (a : D.EdgeIndex)
    (cut : D.EdgeIndex → Bool → ℝ)
    (havoid : Disjoint (⋃ p, ⋃ s, ((B p).face s).carrier)
      ((D.edge a.1 a.2).map '' Ioo (cut a false) (1 - cut a true)))
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hsource : G.source ⊆ (D.edge a.1 a.2).map ⁻¹'
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source)
    (hgraph : ∀ t ∈ G.source,
      L (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge a.1 a.2).map t)) =
        (G t, h (G t)))
    {t : ℝ} (ht : t ∈ G.source) (htcut : t ∈ Ioo (cut a false) (1 - cut a true)) :
    (G t, h (G t)) ∉ D.graphCapObstacle region chart B R L := by
  rintro ⟨z, ⟨q, hq, rfl⟩, hqgraph⟩
  have hqe : q = (D.edge a.1 a.2).map t :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).injOn
      (D.vertexCapsInRegion_subset_chart region chart B R hq) (hsource ht)
      (L.injective (hqgraph.trans (hgraph t ht).symm))
  exact disjoint_left.mp havoid
    (D.vertexCapsInRegion_subset_union B region R hq) ⟨t, htcut, hqe.symm⟩

omit [T2Space M] in


theorem exists_internal_graph_cap_barrier (a : D.EdgeIndex)
    (cut : D.EdgeIndex → Bool → ℝ)
    (havoid : Disjoint (⋃ p, ⋃ s, ((B p).face s).carrier)
      ((D.edge a.1 a.2).map '' Ioo (cut a false) (1 - cut a true)))
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hsource : G.source ⊆ (D.edge a.1 a.2).map ⁻¹'
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source)
    (hgraph : ∀ t ∈ G.source,
      L (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge a.1 a.2).map t)) =
        (G t, h (G t)))
    {t u w : ℝ} (ht : t ∈ G.source) (htcut : t ∈ Ioo (cut a false) (1 - cut a true))
    (htrans : 0 < w - deriv h (G t) * u) (terminal : Bool) :
    ∃ (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (W : Set (ℝ × ℝ)),
      IsOpen W ∧ (G t, h (G t)) ∈ W ∧ ℓ (u, w) = 0 ∧
      (if terminal then ℓ (1, deriv h (G t)) < 0 else 0 < ℓ (1, deriv h (G t))) ∧
      ∀ q ∈ D.graphCapObstacle region chart B R L ∩ W,
        ℓ (q - (G t, h (G t))) ≤ 0 :=
  exists_transverse_barrier_off_closed_set (D.isClosed_graphCapObstacle region chart B R L)
    (D.edge_graph_point_avoids_caps region chart B R L a cut havoid G hsource hgraph ht htcut)
    htrans terminal




theorem exists_incident_graph_cap_separator
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
    (hR : R = D.regionLeft a ∨ R = D.regionRight a)
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hh : ContDiffOn ℝ ∞ h G.target)
    (hsource : G.source ⊆ (D.edge a.1 a.2).map ⁻¹'
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source)
    (hgraph : ∀ t ∈ G.source,
      L (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge a.1 a.2).map t)) =
        (G t, h (G t)))
    (ht : (if terminal then 1 - cut else cut) ∈ G.source)
    (hprojection : 0 < (L (deriv
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ∘ (D.edge a.1 a.2).map)
        (if terminal then 1 - cut else cut))).1) :
    let t := if terminal then 1 - cut else cut
    ∃ (s : Bool × Bool) (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (W : Set (ℝ × ℝ)),
      (s = i ∨ s = j) ∧ region p s = R ∧ IsOpen W ∧ (G t, h (G t)) ∈ W ∧
      (if terminal then ℓ (1, deriv h (G t)) < 0 else 0 < ℓ (1, deriv h (G t))) ∧
      ℓ (L ((B p).planarCoordinates s (0, (B p).scale) -
        (B p).planarCoordinates s ((B p).scale, 0))) = 0 ∧
      (∀ r : ℝ, ℓ (L ((1 - r) • (B p).planarCoordinates s ((B p).scale, 0) +
        r • (B p).planarCoordinates s (0, (B p).scale)) - (G t, h (G t))) = 0) ∧
      ∀ z ∈ D.graphCapObstacle region chart B R L ∩ W,
        ℓ (z - (G t, h (G t))) ≤ 0 := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
  let t := if terminal then 1 - cut else cut
  obtain ⟨s, ℓ, W, hs, hsR, hW, hqW, _, hsign, hchord, hsep⟩ :=
    D.exists_incident_region_cap_separator P region chart B hdisjoint hsector hclosed
      p a terminal hcut hij k hk hend hparameters R hR
  let m := ℓ.comp L.symm.toContinuousLinearMap
  have hm (z : EuclideanSpace ℝ (Fin 2)) : m (L z) = ℓ z := by
    simp only [m, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      L.symm_apply_apply]
  have hbase : L (c (D.edgeFromEndpoint a terminal cut)) = (G t, h (G t)) := by
    cases terminal <;> exact hgraph _ ht
  have hf : DifferentiableAt ℝ (c ∘ (D.edge a.1 a.2).map) t := by
    have hc : ContDiffOn ℝ ∞ (c ∘ (D.edge a.1 a.2).map)
        ((D.edge a.1 a.2).map ⁻¹' c.source) :=
      ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := chart R)).comp
        (D.edge_contMDiff a).contMDiffOn (fun _ ht => ht)).contDiffOn
    exact ((hc t (hsource ht)).contDiffAt
      ((c.open_source.preimage (D.edge_contMDiff a).continuous).mem_nhds
        (hsource ht))).differentiableAt (by simp)
  have hsign' : if terminal then ℓ (deriv (c ∘ (D.edge a.1 a.2).map) t) < 0
      else 0 < ℓ (deriv (c ∘ (D.edge a.1 a.2).map) t) := by
    cases terminal <;> exact hsign
  have hgraphsign := linear_graph_separator_sign L G hG hh hgraph ht hf hprojection ℓ terminal hsign'
  refine ⟨s, m, L '' W, hs, hsR, L.toHomeomorph.isOpenMap W hW,
    ⟨c (D.edgeFromEndpoint a terminal cut), hqW, hbase⟩, hgraphsign, ?_, ?_, ?_⟩
  · rw [hm]
    have h0 := hchord 0
    have h1 := hchord 1
    simp only [sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add] at h0 h1
    have he : (B p).planarCoordinates s (0, (B p).scale) -
        (B p).planarCoordinates s ((B p).scale, 0) =
        ((B p).planarCoordinates s (0, (B p).scale) - c (D.edgeFromEndpoint a terminal cut)) -
        ((B p).planarCoordinates s ((B p).scale, 0) - c (D.edgeFromEndpoint a terminal cut)) := by
      module
    rw [he, map_sub, h0, h1, sub_self]
  · intro r
    rw [← hbase, ← map_sub, hm]
    exact hchord r
  · rintro z ⟨⟨v, hv, rfl⟩, w, hw, hwv⟩
    have hvW : v ∈ W := L.injective hwv ▸ hw
    rw [← hbase, ← map_sub, hm]
    exact hsep v ⟨hv, hvW⟩




theorem exists_graph_cap_avoiding_strip
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (cut : D.EdgeIndex → Bool → ℝ)
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3))
    (hmatch : ∀ a b, ∃ d : Bool × Bool,
      (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b))
    (a : D.EdgeIndex) {α β : ℝ}
    (hα : cut a false ≤ α) (hβ : β ≤ 1 - cut a true)
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ ∞ h G.target)
    (hI : Icc α β ⊆ G.source)
    (hsource : G.source ⊆ (D.edge a.1 a.2).map ⁻¹'
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source)
    (himage : G '' Icc α β = Icc (G α) (G β))
    (hgraph : ∀ t ∈ G.source,
      L (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge a.1 a.2).map t)) =
        (G t, h (G t)))
    (hab : G α < G β) {ua wa ub wb : ℝ}
    (Q : TransverseGraphCuts h (G α) (G β) ua wa ub wb)
    (ℓa ℓb : (ℝ × ℝ) →L[ℝ] ℝ)
    (hcutA : ℓa (ua, wa) = 0) (hcutB : ℓb (ub, wb) = 0)
    (htangentA : 0 < ℓa (1, deriv h (G α))) (htangentB : ℓb (1, deriv h (G β)) < 0)
    {Wa Wb : Set (ℝ × ℝ)} (hWa : IsOpen Wa) (hWb : IsOpen Wb)
    (haW : (G α, h (G α)) ∈ Wa) (hbW : (G β, h (G β)) ∈ Wb)
    (hsepA : ∀ q ∈ D.graphCapObstacle region chart B R L ∩ Wa,
      ℓa (q - (G α, h (G α))) ≤ 0)
    (hsepB : ∀ q ∈ D.graphCapObstacle region chart B R L ∩ Wb,
      ℓb (q - (G β, h (G β))) ≤ 0) :
    ∃ δ > 0, δ ≤ Q.radius ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
        (t, z) ∈ (Q.coordinates G.open_target hh).source) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
        Q.coordinates G.open_target hh (t, z) ∉ D.graphCapObstacle region chart B R L) ∧
      (∀ z : ℝ, |z| < δ →
        Q.coordinates G.open_target hh (0, z) =
          (G α + Q.left.parameter.symm z * ua, h (G α) + Q.left.parameter.symm z * wa) ∧
        Q.coordinates G.open_target hh (1, z) =
          (G β + Q.right.parameter.symm z * ub, h (G β) + Q.right.parameter.symm z * wb)) := by
  have hGI : Icc (G α) (G β) ⊆ G.target := by
    rw [← himage]
    rintro x ⟨t, ht, rfl⟩
    exact G.map_source (hI ht)
  have havoid := D.graph_piece_avoids_caps region chart B R L a cut
    (D.vertex_caps_disjoint_open_middleArc P B hdisjoint hlocal cut hcut hmatch a)
    hα hβ G hI hsource himage hgraph
  exact Q.exists_avoiding_strip G.open_target hh hab hGI
    (D.isClosed_graphCapObstacle region chart B R L) havoid
    ℓa ℓb hcutA hcutB htangentA htangentB hWa hWb haW hbW hsepA hsepB

end CapFamily

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
