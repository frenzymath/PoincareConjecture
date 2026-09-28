


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.IncidentCaps








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

omit [T2Space M] in
theorem boundary_radial_map (i : Bool × Bool) (k : Fin 3) (hk : k = 1 ∨ k = 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((B.face i).boundary k).map t =
      P.radialMap (if k = 1 then (false, i.2) else (true, i.1)) (t * B.scale) := by
  rcases hk with rfl | rfl
  · rw [B.second_map i t ht]
    change P.productCoordinates (sectorParameterEquiv P.center i (0, t * B.scale)) =
      P.productCoordinates (sectorParameterEquiv P.center (i.2, i.2) (0, t * B.scale))
    simp only [sectorParameterEquiv_apply, neg_zero, ite_self]
  · rw [B.first_map i t ht]
    change P.productCoordinates (sectorParameterEquiv P.center i (t * B.scale, 0)) =
      P.productCoordinates (sectorParameterEquiv P.center (i.1, i.1) (t * B.scale, 0))
    simp only [sectorParameterEquiv_apply, neg_zero, ite_self]

omit [T2Space M] in
theorem radial_tip_ne_center (i : Bool × Bool) (k : Fin 3) (hk : k = 1 ∨ k = 2) :
    ((B.face i).boundary k).map 1 ≠ p := by
  rw [B.boundary_radial_map i k hk (by norm_num), one_mul]
  exact fun h => B.scale_pos.ne' ((P.radialMap_eq_center_iff _
    ⟨B.scale_pos.le, B.scale_lt_width.le⟩).mp h)

omit [T2Space M] in
theorem radial_boundary_image (i : Bool × Bool) (k : Fin 3) (hk : k = 1 ∨ k = 2) :
    ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 =
      P.radialSide (if k = 1 then (false, i.2) else (true, i.1)) B.scale := by
  rcases hk with rfl | rfl
  · simpa only [ite_true] using (B.second_image i).trans (P.secondSide_eq_radialSide i B.scale)
  · simpa using (B.first_image i).trans (P.firstSide_eq_radialSide i B.scale)

omit [T2Space M] in
theorem radial_tip_injective (i : Bool × Bool) {k l : Fin 3}
    (hk : k = 1 ∨ k = 2) (hl : l = 1 ∨ l = 2)
    (heq : ((B.face i).boundary k).map 1 = ((B.face i).boundary l).map 1) : k = l := by
  have hne := B.radial_tip_ne_center i k hk
  have hmem (j : Fin 3) (hj : j = 1 ∨ j = 2) :
      ((B.face i).boundary j).map 1 ∈
        P.radialSide (if j = 1 then (false, i.2) else (true, i.1)) B.scale := by
    rw [← B.radial_boundary_image i j hj]
    exact mem_image_of_mem _ (by norm_num)
  have hdir : (if k = 1 then (false, i.2) else (true, i.1)) =
      (if l = 1 then (false, i.2) else (true, i.1)) := by
    by_contra h
    exact hne (P.radialSide_inter_subset_center h B.scale_lt_width.le
      ⟨hmem k hk, heq.symm ▸ hmem l hl⟩)
  rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> simp_all

theorem chord_endpoint_eq_radial_tip (i : Bool × Bool) (terminal : Bool) :
    ((B.face i).boundary 0).map (if terminal then 1 else 0) =
      ((B.face i).boundary (if terminal then 1 else 2)).map 1 := by
  have hsource (k : Fin 3) : ((B.face i).boundary k).map 1 ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source :=
    B.carrier_subset_chart i ((B.face i).isClosed_carrier.frontier_subset
      ((B.face i).boundary_image_subset_frontier k ⟨1, by norm_num, rfl⟩))
  cases terminal
  · rw [B.chord_map]
    simp only [Bool.false_eq_true, ite_false, sub_zero, one_smul, zero_smul, add_zero]
    have htip := B.first_map i 1 (by norm_num)
    simp only [one_mul] at htip
    rw [← htip]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).left_inv (hsource 2)
  · rw [B.chord_map]
    simp only [ite_true, sub_self, zero_smul, one_smul, zero_add]
    have htip := B.second_map i 1 (by norm_num)
    simp only [one_mul] at htip
    rw [← htip]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).left_inv (hsource 1)

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))



theorem exists_cap_radial_attachment
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (cut : D.EdgeIndex → Bool → ℝ)
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) 1)
    (hmatch : ∀ a b, ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
      (((B (D.edgeEndpoint a b)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b) ∧
      ∀ s, s = i ∨ s = j → (((B (D.edgeEndpoint a b)).face s).boundary k).map 1 =
        D.edgeFromEndpoint a b (cut a b))
    (p : D.vertices) (s : Bool × Bool) (k : Fin 3) (hk : k = 1 ∨ k = 2)
    (htip : (((B p).face s).boundary k).map 1 ∈ chartDiskBoundaryUnion D.centers D.radius) :
    ∃ (a : D.EdgeIndex) (terminal : Bool), D.edgeEndpoint a terminal = p ∧
      (((B p).face s).boundary k).map 1 = D.edgeFromEndpoint a terminal (cut a terminal) ∧
      (region p s = D.regionLeft a ∨ region p s = D.regionRight a) ∧
      ∀ v j, D.edgeFromEndpoint a terminal (cut a terminal) ∈ ((B v).face j).carrier →
        region v j = region p s → v = p ∧ j = s := by
  let q := (((B p).face s).boundary k).map 1
  let d := if k = 1 then (false, s.2) else (true, s.1)
  have hqrad : q = (P p).radialMap d (B p).scale := by
    simpa only [one_mul] using (B p).boundary_radial_map s k hk (t := 1) (by norm_num)
  have hqside : q ∈ (P p).radialSide d (B p).scale :=
    ⟨(B p).scale, ⟨(B p).scale_pos.le, le_rfl⟩, hqrad.symm⟩
  have hqne : q ≠ (p : M) := (B p).radial_tip_ne_center s k hk
  rw [← D.boundary_cover] at htip
  obtain ⟨a, hqa⟩ := mem_iUnion.mp htip
  have hradial (b : Bool) (hb : D.edgeEndpoint a b = p) : ∃ e : Bool × Bool,
      (P p).radialSide e (B p).scale = D.edgeFromEndpoint a b '' Icc 0 (cut a b) := by
    subst p
    obtain ⟨i, j, l, _, hl, hi, _⟩ := hmatch a b
    exact (B (D.edgeEndpoint a b)).exists_radialSide_eq_of_boundary_match i l hl hi
  obtain ⟨b, hb, hqsegment⟩ := D.radialSide_inter_edge_mem_endpoint_segment
    P hdisjoint hlocal p a d (B p).scale_pos (B p).scale_lt_width.le
      (cut a) (hcut a) hradial hqside hqne hqa
  subst p
  obtain ⟨i, j, l, hij, hl, hi, hend⟩ := hmatch a b
  let e := if l = 1 then (false, i.2) else (true, i.1)
  have heimage : (P (D.edgeEndpoint a b)).radialSide e (B (D.edgeEndpoint a b)).scale =
      D.edgeFromEndpoint a b '' Icc 0 (cut a b) :=
    ((B (D.edgeEndpoint a b)).radial_boundary_image i l hl).symm.trans hi
  have hde : d = e := by
    by_contra h
    exact hqne ((P (D.edgeEndpoint a b)).radialSide_inter_subset_center h
      (B (D.edgeEndpoint a b)).scale_lt_width.le ⟨hqside, heimage.symm ▸ hqsegment⟩)
  have hqcut : q = D.edgeFromEndpoint a b (cut a b) := by
    calc
      q = (P (D.edgeEndpoint a b)).radialMap e (B (D.edgeEndpoint a b)).scale := hde ▸ hqrad
      _ = (((B (D.edgeEndpoint a b)).face i).boundary l).map 1 := by
        simpa only [one_mul] using
          ((B (D.edgeEndpoint a b)).boundary_radial_map i l hl (t := 1) (by norm_num)).symm
      _ = D.edgeFromEndpoint a b (cut a b) := hend i (Or.inl rfl)
  obtain ⟨hne, hincident, hcap⟩ := D.matched_caps_global_incidence P B region hdisjoint
    hsector hclosed (D.edgeEndpoint a b) a b (hcut a b) hij l hl hend
  have hqcap : D.edgeFromEndpoint a b (cut a b) ∈ ((B (D.edgeEndpoint a b)).face s).carrier := by
    rw [← hqcut]
    exact ((B (D.edgeEndpoint a b)).face s).isClosed_carrier.frontier_subset
      (((B (D.edgeEndpoint a b)).face s).boundary_image_subset_frontier k
        ⟨1, by norm_num, rfl⟩)
  have hs : s = i ∨ s = j := ((hcap (D.edgeEndpoint a b) s).mp hqcap).2
  refine ⟨a, b, rfl, hqcut, (hincident _).mp ?_, ?_⟩
  · exact hs.elim (fun h => Or.inl (congrArg (region (D.edgeEndpoint a b)) h))
      (fun h => Or.inr (congrArg (region (D.edgeEndpoint a b)) h))
  · intro v t ht htR
    obtain ⟨rfl, ht⟩ := (hcap v t).mp ht
    refine ⟨rfl, ?_⟩
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact False.elim (hne htR.symm)
    · exact False.elim (hne htR)
    · rfl

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
