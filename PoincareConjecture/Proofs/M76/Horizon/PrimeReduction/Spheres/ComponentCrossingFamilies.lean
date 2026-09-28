import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ComponentNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PairedChartRestriction

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_actual_component_crossing_families
    (P : Fin 2 → SimplicialComplex ℝ V3) (G : SimplicialComplex ℝ V3)
    (hG : G.faces.Finite) (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (hneigh : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty)
    (hGs : G.space = (P 1).space ∩ (P 0).space)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (p : Fin 2 → V3)
    (hd : IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
      {p 0, p 1})
    (hfront : C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
      intrinsicFrontier ℝ (P 0).space = {p 0, p 1})
    {W : Set V3} (hW : IsOpen W)
    (hdW : C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ W)
    (hinterior : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (P 0).space,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 C3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, x ∈ (P 1).space ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ (P 0).space ↔ (B x).1.1 = 0)
    (hboundary : ∀ w ∈ G.space ∩ intrinsicFrontier ℝ (P 0).space,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 V3,
          B ∈ piecewiseAffineGroupoid V3 ∧ w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          (∀ x ∈ B.source, x ∈ (P 1).space ↔ B x 1 = 0) ∧
          ∀ x ∈ B.source, x ∈ (P 0).space ↔ B x 0 = 0 ∧ 0 ≤ B x 2) :
    let d := C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
    ∃ (U : Set V3) (B : Fin 2 → OpenPartialHomeomorph V3 V3)
      (Q : ↥(d \ {p 0, p 1}) → OpenPartialHomeomorph V3 V3),
      IsOpen U ∧ d ⊆ U ∧ U ⊆ W ∧
      (∀ x ∈ U, x ∈ d ↔ x ∈ (P 0).space ∧ x ∈ (P 1).space) ∧
      (∀ i, B i ∈ piecewiseAffineGroupoid V3) ∧
      (∀ i, p i ∈ (B i).source) ∧ (∀ i, (B i).source ⊆ U) ∧
      (∀ i, B i (p i) = 0) ∧
      (∀ i x, x ∈ (B i).source → (x ∈ (P 0).space ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2)) ∧
      (∀ i x, x ∈ (B i).source → (x ∈ (P 1).space ↔ B i x 1 = 0)) ∧
      (∀ q, Q q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ q, (q : V3) ∈ (Q q).source) ∧ (∀ q, (Q q).source ⊆ U) ∧
      (∀ q, Q q q = 0) ∧
      ∀ q i x, x ∈ (Q q).source → (x ∈ (P i).space ↔ Q q x i.castSucc = 0) := by
  classical
  let d := C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
  have hdG : d ⊆ G.space := by
    rintro x ⟨v, w, hvw, hx⟩
    exact (G.actual_edgeGraph_segmentCarrier_eq_space hdim hneigh).subset
      ⟨v.val, w.val, hvw, hx⟩
  obtain ⟨U₀, hU₀, hdU₀, hGU₀⟩ := G.exists_open_component_neighborhood hG hdim hneigh C
  let U := U₀ ∩ W
  have hU : IsOpen U := hU₀.inter hW
  have hdU : d ⊆ U := fun x hx => ⟨hdU₀ hx, hdW hx⟩
  have hisolate (x : V3) (hx : x ∈ U) : x ∈ d ↔ x ∈ (P 0).space ∧ x ∈ (P 1).space := by
    constructor
    · intro hxd
      exact ((hGs.subset (hdG hxd))).symm
    · intro hxP
      exact hGU₀.subset ⟨hGs.symm.subset hxP.symm, hx.1⟩
  have hpfront (i : Fin 2) : p i ∈ d ∩ intrinsicFrontier ℝ (P 0).space :=
    hfront.symm.subset (by fin_cases i <;> simp)
  have hpd (i : Fin 2) : p i ∈ d := hd.1 (by fin_cases i <;> simp)
  have hendpoint (i : Fin 2) : ∃ B : OpenPartialHomeomorph V3 V3,
      B ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ B.source ∧ B.source ⊆ U ∧ B (p i) = 0 ∧
      (∀ x ∈ B.source, x ∈ (P 1).space ↔ B x 1 = 0) ∧
      ∀ x ∈ B.source, x ∈ (P 0).space ↔ B x 0 = 0 ∧ 0 ≤ B x 2 :=
    hboundary (p i) ⟨hdG (hpd i), (hpfront i).2⟩ U hU (hdU (hpd i))
  choose B hB hpB hBU hBp hBsphere hBtriangle using hendpoint
  have hregular (q : ↥(d \ {p 0, p 1})) :
      (q : V3) ∈ G.space ∩ intrinsicInterior ℝ (P 0).space := by
    refine ⟨hdG q.property.1, ?_⟩
    by_contra hnot
    apply q.property.2
    apply hfront.subset
    refine ⟨q.property.1, ?_⟩
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure (hGs.subset (hdG q.property.1)).2, hnot⟩
  have hinter (q : ↥(d \ {p 0, p 1})) :
      ∃ Q : OpenPartialHomeomorph V3 V3,
        Q ∈ piecewiseAffineGroupoid V3 ∧ (q : V3) ∈ Q.source ∧ Q.source ⊆ U ∧ Q q = 0 ∧
        ∀ i x, x ∈ Q.source → (x ∈ (P i).space ↔ Q x i.castSucc = 0) := by
    obtain ⟨D, hqD, hDU, hDq, hD, hDi, hDsphere, hDtriangle⟩ :=
      hinterior q (hregular q) U hU (hdU q.property.1)
    obtain ⟨Q, hQ, hqQ, hs, hQq, hcross⟩ := exists_ordered_interior_crossing_chart
      D hD hDi hqD hDq (fun i => (P i).space) hDtriangle hDsphere
    exact ⟨Q, hQ, hqQ, hs.subset.trans hDU, hQq, hcross⟩
  choose Q hQ hqQ hQU hQq hcross using hinter
  exact ⟨U, B, Q, hU, hdU, inter_subset_right, hisolate,
    hB, hpB, hBU, hBp, hBtriangle, hBsphere, hQ, hqQ, hQU, hQq, hcross⟩

end PoincareConjecture.M76
