import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.PrescribedIntervalDiskMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.HoleTransport
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus

/-! # Attach a disk to a punctured disk along prescribed outer intervals

The filled disk attachment is normalized by its actual interval parameters.
Transporting the untouched inner disk and then removing its interior gives
the new annulus, with both complete source copies retained.
-/

set_option autoImplicit false
open Set Geometry TriangleDiskModel PLAnnularStrip unitInterval

namespace PoincareMT.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)

private theorem parameter_mem_endpoints {E : Type*} [TopologicalSpace E]
    {W : Set E} {a b : E} (p : I01 ≃ₜ W)
    (h0 : (p (0 : I) : E) = a) (h1 : (p (1 : I) : E) = b) (x : W) :
    (x : E) ∈ ({a, b} : Set E) ↔ p.symm x = (0 : I) ∨ p.symm x = (1 : I) := by
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (hx | hx)
    · left
      apply p.injective
      rw [p.apply_symm_apply]
      exact Subtype.ext (hx.trans h0.symm)
    · right
      apply p.injective
      rw [p.apply_symm_apply]
      exact Subtype.ext (hx.trans h1.symm)
  · rintro (hx | hx)
    · left
      have h := congrArg (fun t : I01 => (p t : E)) hx
      simpa only [p.apply_symm_apply, h0] using h
    · right
      have h := congrArg (fun t : I01 => (p t : E)) hx
      simpa only [p.apply_symm_apply, h1] using h

private theorem exists_prescribed_disk_identification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {S Q W : Set E} {a b : E} (hS : IsFinitePLBallPair P2 S Q)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hWQ : W ⊆ Q) (hab : a ≠ b)
    (p : I01 ≃ₜ W) (hp : p.IsFinitePL)
    (hp0 : (p (0 : I) : E) = a) (hp1 : (p (1 : I) : E) = b)
    {T C : Set P2} (hT : IsFinitePLBallPair P2 T (C ∪ TE))
    (hC : IsFinitePLBallPair ℝ C {(0, 1), (0, 0)})
    (hCE : C ∩ TE = {(0, 1), (0, 0)})
    (q : I01 ≃ₜ TE) (hq : q.IsFinitePL)
    (hq0 : (q (0 : I) : P2) = (0, 1)) (hq1 : (q (1 : I) : P2) = (0, 0)) :
    ∃ (B : Set E) (H : S ≃ₜ T),
      IsFinitePLBallPair ℝ B {a, b} ∧ W ∪ B = Q ∧ W ∩ B = {a, b} ∧
      H.IsFinitePL ∧
      (∀ t : I01, (H ⟨p t, hS.1 (hWQ (p t).property)⟩ : P2) = q t) ∧
      ∀ x : S, (x : E) ∈ B ↔ (H x : P2) ∈ C := by
  obtain ⟨B, hB, hWB, hWBinter⟩ := hS.exists_boundary_arc_complement hW hWQ hab
  have hS' : IsFinitePLBallPair P2 S (B ∪ W) := by rwa [union_comm, hWB]
  have hBW : B ∩ W = {a, b} := by rwa [inter_comm]
  let d : W ≃ₜ TE := p.symm.trans q
  have hd : d.IsFinitePL := hp.symm.trans hq
  have hdmem (x : W) : (x : E) ∈ ({a, b} : Set E) ↔
      (d x : P2) ∈ ({(0, 1), (0, 0)} : Set P2) := by
    change (x : E) ∈ ({a, b} : Set E) ↔
      (q (p.symm x) : P2) ∈ ({(0, 1), (0, 0)} : Set P2)
    rw [parameter_mem_endpoints p hp0 hp1 x,
      parameter_mem_endpoints q hq0 hq1 (q (p.symm x)), q.symm_apply_apply]
  obtain ⟨H, hH, hHW, hHB, _⟩ :=
    hS'.exists_extension_of_boundary_piece hT hB hC hBW hCE d hd hdmem
  refine ⟨B, H, hB, hWB, hWBinter, hH, ?_, hHB⟩
  intro t
  have h := congrArg (fun y : T => (y : P2)) (hHW (p t))
  change (H ⟨p t, _⟩ : P2) = (q (p.symm (p t)) : P2) at h
  simpa only [p.symm_apply_apply] using h

theorem exists_punctured_prescribed_attachment
    {S0 S1 W0 W1 D : Set P2} {a0 b0 a1 b1 : P2}
    (hS0 : IsFinitePLBallPair P2 S0 (frontier S0))
    (hS1 : IsFinitePLBallPair P2 S1 (frontier S1))
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hDS : D ⊆ interior S0)
    (hW0 : IsFinitePLBallPair ℝ W0 {a0, b0})
    (hW1 : IsFinitePLBallPair ℝ W1 {a1, b1})
    (hW0Q : W0 ⊆ frontier S0) (hW1Q : W1 ⊆ frontier S1)
    (hab0 : a0 ≠ b0) (hab1 : a1 ≠ b1)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1)
    (hp0 : p0.IsFinitePL) (hp1 : p1.IsFinitePL)
    (hp00 : (p0 (0 : I) : P2) = a0) (hp01 : (p0 (1 : I) : P2) = b0)
    (hp10 : (p1 (0 : I) : P2) = a1) (hp11 : (p1 (1 : I) : P2) = b1) :
    ∃ (B0 B1 P : Set P2) (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL)
      (p : I01 ≃ₜ TE) (q : D ≃ₜ P)
      (H : squareAnnulus 8 1 ≃ₜ ((TR ∪ TL) \ interior P : Set P2)),
      IsFinitePLBallPair ℝ B0 {a0, b0} ∧ IsFinitePLBallPair ℝ B1 {a1, b1} ∧
      W0 ∪ B0 = frontier S0 ∧ W1 ∪ B1 = frontier S1 ∧
      W0 ∩ B0 = {a0, b0} ∧ W1 ∩ B1 = {a1, b1} ∧
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ p.IsFinitePL ∧ q.IsFinitePL ∧ H.IsFinitePL ∧
      (∀ t : I01, (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) = p t) ∧
      (∀ t : I01, (n1 ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩ : P2) = p t) ∧
      IsFinitePLBallPair P2 P (frontier P) ∧ P ⊆ interior TR ∧
      (∀ x : D, (q x : P2) = n0 ⟨x, interior_subset (hDS x.property)⟩) ∧
      (∀ x : S0, (n0 x : P2) ∈ P ↔ (x : P2) ∈ D) ∧
      (∀ x : S0, (n0 x : P2) ∈ interior P ↔ (x : P2) ∈ interior D) ∧
      (∀ x : S0, (n0 x : P2) ∈ frontier P ↔ (x : P2) ∈ frontier D) ∧
      ((TR ∪ TL) \ interior P : Set P2) =
        ((fun x : S0 => (n0 x : P2)) '' {x : S0 | (x : P2) ∉ interior D}) ∪ TL ∧
      (∀ z : squareAnnulus 8 1,
        depth 8 (z : P2) = -1 ↔ (H z : P2) ∈ frontier (TR ∪ TL)) ∧
      ∀ z : squareAnnulus 8 1,
        depth 8 (z : P2) = 1 ↔ (H z : P2) ∈ frontier P := by
  obtain ⟨C0, C1, hR, hL, hC0, hC1, hC0E, hC1E, hwhole⟩ :=
    exists_disk_attachment_model
  obtain ⟨p, hp, hpzero, hpone⟩ :=
    isFinitePLBallPair_common_edge.exists_unitInterval_chart_with_endpoints (by norm_num)
  obtain ⟨B0, n0, hB0, hW0B, hW0Bi, hn0, hn0p, _⟩ :=
    exists_prescribed_disk_identification hS0 hW0 hW0Q hab0 p0 hp0 hp00 hp01
      hR hC0 hC0E p hp hpzero hpone
  obtain ⟨B1, n1, hB1, hW1B, hW1Bi, hn1, hn1p, _⟩ :=
    exists_prescribed_disk_identification hS1 hW1 hW1Q hab1 p1 hp1 hp10 hp11
      hL hC1 hC1E p hp hpzero hpone
  obtain ⟨P, q, hq, hP, hPT, hqval, hmem, hint, hfront⟩ :=
    exists_inner_disk_image n0 hn0 hD hDS
  have hwhole' : IsFinitePLBallPair P2 (TR ∪ TL) (frontier (TR ∪ TL)) :=
    (hwhole.frontier_eq_of_finrank_eq rfl).symm ▸ hwhole
  have hPwhole : P ⊆ interior (TR ∪ TL) :=
    hPT.trans (interior_mono subset_union_left)
  obtain ⟨H, hH, hout, hin⟩ := exists_square_annulus_nested_disks hP hwhole' hPwhole
    (show (0 : ℝ) < 1 by norm_num) (show (2 : ℝ) * 1 < 8 by norm_num)
  have hLavoid : Disjoint TL P := by
    refine disjoint_left.mpr ?_
    intro x hxL hxP
    have hxR := hPT hxP
    have hxE := region_inter.subset ⟨interior_subset hxR, hxL⟩
    have hfrontR : x ∈ frontier TR := by
      rw [hR.frontier_eq_of_finrank_eq rfl]
      exact Or.inr hxE
    exact hfrontR.2 hxR
  have hcover : ((TR ∪ TL) \ interior P : Set P2) =
      ((fun x : S0 => (n0 x : P2)) '' {x : S0 | (x : P2) ∉ interior D}) ∪ TL := by
    ext x
    constructor
    · rintro ⟨hxR | hxL, hxP⟩
      · refine Or.inl ⟨n0.symm ⟨x, hxR⟩, ?_, ?_⟩
        · intro hxD
          have hh := (hint (n0.symm ⟨x, hxR⟩)).mpr hxD
          exact hxP (by simpa only [n0.apply_symm_apply] using hh)
        · exact congrArg Subtype.val (n0.apply_symm_apply ⟨x, hxR⟩)
      · exact Or.inr hxL
    · rintro (⟨x, hx, rfl⟩ | hxL)
      · exact ⟨Or.inl (n0 x).property, fun h => hx ((hint x).mp h)⟩
      · exact ⟨Or.inr hxL, fun hxP => disjoint_left.mp hLavoid hxL (interior_subset hxP)⟩
  exact ⟨B0, B1, P, n0, n1, p, q, H, hB0, hB1, hW0B, hW1B, hW0Bi, hW1Bi,
    hn0, hn1, hp, hq, hH, hn0p, hn1p, hP, hPT, hqval, hmem, hint, hfront,
    hcover, hout, hin⟩

end PoincareMT.M76.Dehn
