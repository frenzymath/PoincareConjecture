import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeReversal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutRectangle
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarBoundaryEdges
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import Mathlib.Order.Interval.Set.Infinite









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

theorem sourceBridge_infinite (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    (A.sourceBridge i).Infinite := by
  obtain ⟨g, α, β, _, _, _, _, _, _, hαβ, _, _, _, _, hi, him⟩ :=
    A.exists_ordered_longArc_bridge_chart hbound i
  rw [← him]
  exact (Icc_infinite hαβ).image hi



theorem exists_paired_bridge_sample (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (i : Fin 4) {bad : Set E} (hbad : bad.Finite) :
    ∃ x p q,
      x ∈ A.sourceBridge i ∧ x ∉ bad ∧
      p ∈ A.boundaryBridge i ∧ q ∈ A.boundaryBridge (A.arcPairing i) ∧
      (A.sourceMap K P D hD hcofaces hP labels) p = x ∧
      (A.sourceMap K P D hD hcofaces hP labels) q = x ∧
      p ≠ A.bridgeBegin i ∧ p ≠ A.bridgeEnd i ∧
      q ≠ A.bridgeBegin (A.arcPairing i) ∧ q ≠ A.bridgeEnd (A.arcPairing i) := by
  let sm := A.sourceMap K P D hD hcofaces hP labels
  let ends : Set E := {sm (A.bridgeBegin i), sm (A.bridgeEnd i)}
  obtain ⟨x, hx, havoid⟩ := (A.sourceBridge_infinite hbound i).exists_notMem_finite
    (hbad.union ((finite_singleton _).insert _)) (t := bad ∪ ends)
  have hxends : x ∉ ends := fun h ↦ havoid (Or.inr h)
  obtain ⟨p, hp, hpx⟩ := (A.sourceMap_boundaryBridge i).symm ▸ hx
  have hxj : x ∈ A.sourceBridge (A.arcPairing i) := (A.sourceBridge_paired i).symm ▸ hx
  obtain ⟨q, hq, hqx⟩ := (A.sourceMap_boundaryBridge (A.arcPairing i)).symm ▸ hxj
  have hqends : x ∉ ({sm (A.bridgeBegin (A.arcPairing i)),
      sm (A.bridgeEnd (A.arcPairing i))} : Set E) := by
    rw [A.source_bridge_endpoints_paired i]
    exact hxends
  refine ⟨x, p, q, hx, fun h ↦ havoid (Or.inl h), hp, hq, hpx, hqx, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hxends (Or.inl (hpx.symm.trans (congrArg sm h)))
  · intro h
    exact hxends (Or.inr (hpx.symm.trans (congrArg sm h)))
  · intro h
    exact hqends (Or.inl (hqx.symm.trans (congrArg sm h)))
  · intro h
    exact hqends (Or.inr (hqx.symm.trans (congrArg sm h)))



theorem exists_paired_nonvertex_square_samples
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (C : (PeriodicSquare.squareCarrier 1) ≃ₜ A.carrier)
    (hw : ∀ x, (C x).val ∈ A.longBoundaryArc 0 ↔ x.val.2 = 0)
    (hz : ∀ x, (C x).val ∈ A.longBoundaryArc 2 ↔ x.val.2 = 1)
    (hl : ∀ x, (C x).val ∈ A.longBoundaryArc 3 ↔ x.val.1 = 0)
    (hr : ∀ x, (C x).val ∈ A.longBoundaryArc 1 ↔ x.val.1 = 1)
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (hL : L.faces.Finite)
    (hLs : L.space = PeriodicSquare.squareCarrier 1)
    (F : (ℝ × ℝ) → E)
    (hF : ∀ x, F x.val = (A.sourceMap K P D hD hcofaces hP labels) (C x))
    (i : Fin 4) :
    ∃ u v : PeriodicSquare.squareCarrier 1,
      (C u).val ∈ A.boundaryBridge i ∧
      (C v).val ∈ A.boundaryBridge (A.arcPairing i) ∧
      F u.val = F v.val ∧ u.val ∉ L.vertices ∧ v.val ∉ L.vertices ∧
      u.val ∈ frontier L.space ∧ v.val ∈ frontier L.space ∧
      (C u).val ≠ A.bridgeBegin i ∧ (C u).val ≠ A.bridgeEnd i ∧
      (C v).val ≠ A.bridgeBegin (A.arcPairing i) ∧
      (C v).val ≠ A.bridgeEnd (A.arcPairing i) := by
  obtain ⟨x, p, q, _, hbad, hp, hq, hpx, hqx, hp0, hp1, hq0, hq1⟩ :=
    A.exists_paired_bridge_sample hbound i ((L.finite_vertices_of_finite_faces hL).image F)
  have hcarrier (j : Fin 4) {p} (hp : p ∈ A.boundaryBridge j) : p ∈ A.carrier :=
    A.disk.1 (A.longBoundaryArcs_cover.subset (mem_iUnion.mpr ⟨j, Or.inl (Or.inr hp)⟩))
  obtain ⟨u, hu⟩ := C.surjective ⟨p, hcarrier i hp⟩
  obtain ⟨v, hv⟩ := C.surjective ⟨q, hcarrier (A.arcPairing i) hq⟩
  have huval : (C u).val = p := congrArg Subtype.val hu
  have hvval : (C v).val = q := congrArg Subtype.val hv
  have hux : F u.val = x := (hF u).trans (congrArg _ huval |>.trans hpx)
  have hvx : F v.val = x := (hF v).trans (congrArg _ hvval |>.trans hqx)
  have hfront (w : PeriodicSquare.squareCarrier 1) (j : Fin 4)
      (hj : (C w).val ∈ A.boundaryBridge j) : w.val ∈ frontier L.space := by
    have hside : w.val.1 = 0 ∨ w.val.1 = 1 ∨ w.val.2 = 0 ∨ w.val.2 = 1 := by
      have hlong : (C w).val ∈ A.longBoundaryArc j := Or.inl (Or.inr hj)
      fin_cases j
      · exact Or.inr (Or.inr (Or.inl ((hw w).mp hlong)))
      · exact Or.inr (Or.inl ((hr w).mp hlong))
      · exact Or.inr (Or.inr (Or.inr ((hz w).mp hlong)))
      · exact Or.inl ((hl w).mp hlong)
    rw [hLs, frontier]
    refine ⟨subset_closure w.property, ?_⟩
    change w.val ∉ interior (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    rw [interior_prod_eq, interior_Icc]
    intro hint
    rcases hside with h | h | h | h <;> simp_all
  refine ⟨u, v, huval.symm ▸ hp, hvval.symm ▸ hq, hux.trans hvx.symm,
    ?_, ?_, hfront u i (huval.symm ▸ hp),
    hfront v (A.arcPairing i) (hvval.symm ▸ hq), ?_, ?_, ?_, ?_⟩
  · exact fun h ↦ hbad ⟨u.val, h, hux⟩
  · exact fun h ↦ hbad ⟨v.val, h, hvx⟩
  all_goals simpa only [huval, hvval]

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

namespace Geometry.SimplicialComplex

private theorem edge_hull_subset_frontier_of_openSegment
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (hL : L.faces.Finite)
    (hcv : Convex ℝ L.space) (hne : (interior L.space).Nonempty)
    {a b x : ℝ × ℝ} (he : ({a, b} : Finset (ℝ × ℝ)) ∈ L.faces)
    (hx : x ∈ frontier L.space) (hxab : x ∈ openSegment ℝ a b) :
    convexHull ℝ (({a, b} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ⊆ frontier L.space := by
  obtain ⟨ell, hell⟩ := geometric_hahn_banach_open_point hcv.interior isOpen_interior hx.2
  have hle (y) (hy : y ∈ L.space) : ell y ≤ ell x := by
    apply le_on_closure (fun z hz ↦ (hell z hz).le)
      ell.continuous.continuousOn continuousOn_const
    rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne,
      (L.isCompact_space_of_finite hL).isClosed.closure_eq]
    exact hy
  have ha := hle a (L.subset_space he (by simp))
  have hb := hle b (L.subset_space he (by simp))
  obtain ⟨r, s, hr, hs, hrs, hxx⟩ := hxab
  have hlin : r * ell a + s * ell b = ell x := by
    simpa only [map_add, map_smul, smul_eq_mul] using congrArg ell hxx
  have hea : ell a = ell x := by
    apply le_antisymm ha
    by_contra h
    have hlt := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (lt_of_not_ge h) hr)
      (mul_le_mul_of_nonneg_left hb hs.le)
    rw [hlin, ← add_mul, hrs, one_mul] at hlt
    exact (lt_irrefl _ hlt)
  have heb : ell b = ell x := by
    apply le_antisymm hb
    by_contra h
    have hlt := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left ha hr.le)
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) hs)
    rw [hlin, ← add_mul, hrs, one_mul] at hlt
    exact (lt_irrefl _ hlt)
  intro y hy
  have hyspace := L.convexHull_subset_space he hy
  have hye : ell y = ell x := by
    have hseg : y ∈ segment ℝ a b := by
      simpa only [Finset.coe_pair, convexHull_pair] using hy
    obtain ⟨u, v, _, _, huv, rfl⟩ := hseg
    simp only [map_add, map_smul, smul_eq_mul, hea, heb]
    rw [← add_mul, huv, one_mul]
  refine ⟨subset_closure hyspace, ?_⟩
  intro hyi
  exact (ne_of_lt (hell y hyi)) hye



theorem square_nonvertex_boundary_edge_coface
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (hL : L.faces.Finite)
    (hLs : L.space = PoincareConjecture.M76.PeriodicSquare.squareCarrier 1)
    {x : ℝ × ℝ} (hx : x ∈ frontier L.space) (hxv : x ∉ L.vertices) :
    ∃ a b : ℝ × ℝ, ∃ t : Finset (ℝ × ℝ),
      a ≠ b ∧ ({a, b} : Finset (ℝ × ℝ)) ∈ (L.frontierSubcomplex L.space).faces ∧
      a ∈ frontier L.space ∧ b ∈ frontier L.space ∧
      x ∈ openSegment ℝ a b ∧ t ∈ L.faces ∧ t.card = 3 ∧ {a, b} ⊆ t := by
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hcv : Convex ℝ L.space := hLs.symm ▸
    (convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)
  have hne : (interior L.space).Nonempty := by
    rw [hLs]
    refine ⟨((1 / 2 : ℝ), (1 / 2 : ℝ)), ?_⟩
    change ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ interior (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    rw [interior_prod_eq, interior_Icc]
    norm_num
  rcases L.frontier_point_vertex_or_boundary_edge hL hdim hcv hne hx with h | h
  · exact (hxv h).elim
  · obtain ⟨a, b, hab, he, haf, hbf, hxab⟩ := h
    obtain ⟨t, ht, het, htc⟩ := L.exists_full_coface_of_convex_space hL hcv hne he
    refine ⟨a, b, t, hab, ⟨he, ?_⟩, haf, hbf, hxab, ht, ?_, het⟩
    · exact edge_hull_subset_frontier_of_openSegment L hL hcv hne he hx hxab
    · simpa [hdim] using htc

end Geometry.SimplicialComplex
