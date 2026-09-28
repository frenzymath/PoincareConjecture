import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLClosedUnion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleDiskAttachmentModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition











set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)

private theorem parameter_mem_endpoints {E : Type*} [TopologicalSpace E]
    {W : Set E} {a b : E} (p : I01 ≃ₜ W)
    (h0 : (p i0 : E) = a) (h1 : (p i1 : E) = b) (x : W) :
    (x : E) ∈ ({a, b} : Set E) ↔ p.symm x = i0 ∨ p.symm x = i1 := by
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
    (hp0 : (p i0 : E) = a) (hp1 : (p i1 : E) = b)
    {T C : Set P2} (hT : IsFinitePLBallPair P2 T (C ∪ TE))
    (hC : IsFinitePLBallPair ℝ C {(0, 1), (0, 0)})
    (hCE : C ∩ TE = {(0, 1), (0, 0)})
    (q : I01 ≃ₜ TE) (hq : q.IsFinitePL)
    (hq0 : (q i0 : P2) = (0, 1)) (hq1 : (q i1 : P2) = (0, 0)) :
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






theorem exists_prescribed_interval_disk_map
    {E0 E1 F X ι : Type*}
    [NormedAddCommGroup E0] [NormedSpace ℝ E0] [FiniteDimensional ℝ E0]
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S0 Q0 W0 : Set E0} {S1 Q1 W1 : Set E1} {a0 b0 : E0} {a1 b1 : E1}
    (hS0 : IsFinitePLBallPair P2 S0 Q0) (hS1 : IsFinitePLBallPair P2 S1 Q1)
    (hW0 : IsFinitePLBallPair ℝ W0 {a0, b0}) (hW1 : IsFinitePLBallPair ℝ W1 {a1, b1})
    (hW0Q : W0 ⊆ Q0) (hW1Q : W1 ⊆ Q1) (hab0 : a0 ≠ b0) (hab1 : a1 ≠ b1)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1)
    (hp0 : p0.IsFinitePL) (hp1 : p1.IsFinitePL)
    (hp00 : (p0 i0 : E0) = a0) (hp01 : (p0 i1 : E0) = b0)
    (hp10 : (p1 i0 : E1) = a1) (hp11 : (p1 i1 : E1) = b1)
    {f0 : E0 → X} {f1 : E1 → X}
    (hf0 : PolyhedralPLInCharts e f0 S0) (hf1 : PolyhedralPLInCharts e f1 S1)
    (hagree : ∀ t : I01, f0 (p0 t) = f1 (p1 t)) :
    ∃ (B0 : Set E0) (B1 : Set E1) (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL)
      (p : I01 ≃ₜ TE) (g : P2 → X),
      IsFinitePLBallPair ℝ B0 {a0, b0} ∧ IsFinitePLBallPair ℝ B1 {a1, b1} ∧
      W0 ∪ B0 = Q0 ∧ W1 ∪ B1 = Q1 ∧
      W0 ∩ B0 = {a0, b0} ∧ W1 ∩ B1 = {a1, b1} ∧
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ p.IsFinitePL ∧
      (p i0 : P2) = (0, 1) ∧ (p i1 : P2) = (0, 0) ∧
      (∀ t : I01, (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) = p t) ∧
      (∀ t : I01, (n1 ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩ : P2) = p t) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S0, g (n0 x) = f0 x) ∧ (∀ x : S1, g (n1 x) = f1 x) ∧
      g '' (TR ∪ TL) = f0 '' S0 ∪ f1 '' S1 ∧
      IsFinitePLBallPair P2 (TR ∪ TL)
        ((fun x : S0 => (n0 x : P2)) '' (Subtype.val ⁻¹' B0) ∪
         (fun x : S1 => (n1 x : P2)) '' (Subtype.val ⁻¹' B1)) ∧
      ∀ Z : Set X, (TR ∪ TL) ∩ g ⁻¹' Z =
        (fun x : S0 => (n0 x : P2)) '' {x : S0 | f0 x ∈ Z} ∪
        (fun x : S1 => (n1 x : P2)) '' {x : S1 | f1 x ∈ Z} := by
  classical
  obtain ⟨C0, C1, hR, hL, hC0, hC1, hC0E, hC1E, hwhole⟩ :=
    exists_disk_attachment_model
  obtain ⟨p, hp, hpzero, hpone⟩ :=
    isFinitePLBallPair_common_edge.exists_unitInterval_chart_with_endpoints (by norm_num)
  obtain ⟨B0, n0, hB0, hW0B, hW0Bi, hn0, hn0p, hn0B⟩ :=
    exists_prescribed_disk_identification hS0 hW0 hW0Q hab0 p0 hp0 hp00 hp01
      hR hC0 hC0E p hp hpzero hpone
  obtain ⟨B1, n1, hB1, hW1B, hW1Bi, hn1, hn1p, hn1B⟩ :=
    exists_prescribed_disk_identification hS1 hW1 hW1Q hab1 p1 hp1 hp10 hp11
      hL hC1 hC1E p hp hpzero hpone
  obtain ⟨r0, hr0, hr0val⟩ := hn0.symm
  obtain ⟨r1, hr1, hr1val⟩ := hn1.symm
  have hr0n (x : S0) : r0 (n0 x) = x := by
    have h := hr0val (n0 x)
    rw [n0.symm_apply_apply] at h
    exact h.symm
  have hr1n (x : S1) : r1 (n1 x) = x := by
    have h := hr1val (n1 x)
    rw [n1.symm_apply_apply] at h
    exact h.symm
  have hr0p (t : I01) : r0 (p t) = p0 t := by
    have h := hr0n ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩
    rwa [hn0p t] at h
  have hr1p (t : I01) : r1 (p t) = p1 t := by
    have h := hr1n ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩
    rwa [hn1p t] at h
  have hagree' (x : P2) (hxR : x ∈ TR) (hxL : x ∈ TL) :
      f0 (r0 x) = f1 (r1 x) := by
    have hxE : x ∈ TE := region_inter.subset ⟨hxR, hxL⟩
    let t : I01 := p.symm ⟨x, hxE⟩
    have hpt : (p t : P2) = x := congrArg Subtype.val (p.apply_symm_apply ⟨x, hxE⟩)
    rw [← hpt, hr0p, hr1p]
    exact hagree t
  let g : P2 → X := fun x => if x ∈ TR then f0 (r0 x) else f1 (r1 x)
  have hg0 (x : P2) (hx : x ∈ TR) : g x = f0 (r0 x) := by
    dsimp only [g]
    rw [if_pos hx]
  have hg1 (x : P2) (hx : x ∈ TL) : g x = f1 (r1 x) := by
    by_cases hxR : x ∈ TR
    · exact (hg0 x hxR).trans (hagree' x hxR hx)
    · dsimp only [g]
      rw [if_neg hxR]
  have hkeep0 (x : S0) : g (n0 x) = f0 x := by
    rw [hg0 _ (n0 x).property, hr0n]
  have hkeep1 (x : S1) : g (n1 x) = f1 x := by
    rw [hg1 _ (n1 x).property, hr1n]
  have hmap0 : MapsTo r0 TR S0 := by
    intro x hx
    rw [← hr0val ⟨x, hx⟩]
    exact (n0.symm ⟨x, hx⟩).property
  have hmap1 : MapsTo r1 TL S1 := by
    intro x hx
    rw [← hr1val ⟨x, hx⟩]
    exact (n1.symm ⟨x, hx⟩).property
  have hr0copy := hr0
  have hr1copy := hr1
  obtain ⟨K0, hK0, hK0s, _⟩ := hr0copy
  obtain ⟨K1, hK1, hK1s, _⟩ := hr1copy
  have hreg0 : PolyhedralPLInCharts e g K0.space := by
    have hr : FinitePiecewiseAffineOn r0 K0.space := by simpa only [hK0s] using hr0
    have hm : MapsTo r0 K0.space S0 := by simpa only [hK0s] using hmap0
    exact (hf0.comp_finitePiecewiseAffineOn K0 hK0 hr hm).congr
      (fun x hx => (hg0 x (hK0s.subset hx)).symm)
  have hreg1 : PolyhedralPLInCharts e g K1.space := by
    have hr : FinitePiecewiseAffineOn r1 K1.space := by simpa only [hK1s] using hr1
    have hm : MapsTo r1 K1.space S1 := by simpa only [hK1s] using hmap1
    exact (hf1.comp_finitePiecewiseAffineOn K1 hK1 hr hm).congr
      (fun x hx => (hg1 x (hK1s.subset hx)).symm)
  have hreg : PolyhedralPLInCharts e g (TR ∪ TL) := by
    have h := PolyhedralPLInCharts.union_of_finite hcompat K0 K1 hK0 hK1 hreg0 hreg1
    simpa only [hK0s, hK1s] using h
  have him0 : (fun x : S0 => (n0 x : P2)) '' (Subtype.val ⁻¹' B0) = C0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hn0B x).mp hx
    · intro hy
      let yR : TR := ⟨y, hR.1 (Or.inl hy)⟩
      refine ⟨n0.symm yR, (hn0B _).mpr ?_, ?_⟩
      · simpa only [n0.apply_symm_apply] using hy
      · exact congrArg Subtype.val (n0.apply_symm_apply yR)
  have him1 : (fun x : S1 => (n1 x : P2)) '' (Subtype.val ⁻¹' B1) = C1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hn1B x).mp hx
    · intro hy
      let yL : TL := ⟨y, hL.1 (Or.inl hy)⟩
      refine ⟨n1.symm yL, (hn1B _).mpr ?_, ?_⟩
      · simpa only [n1.apply_symm_apply] using hy
      · exact congrArg Subtype.val (n1.apply_symm_apply yL)
  refine ⟨B0, B1, n0, n1, p, g, hB0, hB1, hW0B, hW1B, hW0Bi, hW1Bi,
    hn0, hn1, hp, hpzero, hpone, hn0p, hn1p, hreg, hkeep0, hkeep1, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hxR | hxL, rfl⟩
      · exact Or.inl ⟨r0 x, hmap0 hxR, (hg0 x hxR).symm⟩
      · exact Or.inr ⟨r1 x, hmap1 hxL, (hg1 x hxL).symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨n0 ⟨x, hx⟩, Or.inl (n0 ⟨x, hx⟩).property, hkeep0 ⟨x, hx⟩⟩
      · exact ⟨n1 ⟨x, hx⟩, Or.inr (n1 ⟨x, hx⟩).property, hkeep1 ⟨x, hx⟩⟩
  · rw [him0, him1]
    exact hwhole
  · intro Z
    ext y
    constructor
    · rintro ⟨hyR | hyL, hyZ⟩
      · refine Or.inl ⟨n0.symm ⟨y, hyR⟩, ?_, ?_⟩
        · change f0 (n0.symm ⟨y, hyR⟩) ∈ Z
          rw [← hkeep0, n0.apply_symm_apply]
          exact hyZ
        · exact congrArg Subtype.val (n0.apply_symm_apply ⟨y, hyR⟩)
      · refine Or.inr ⟨n1.symm ⟨y, hyL⟩, ?_, ?_⟩
        · change f1 (n1.symm ⟨y, hyL⟩) ∈ Z
          rw [← hkeep1, n1.apply_symm_apply]
          exact hyZ
        · exact congrArg Subtype.val (n1.apply_symm_apply ⟨y, hyL⟩)
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · refine ⟨Or.inl (n0 x).property, ?_⟩
        change g (n0 x) ∈ Z
        rw [hkeep0]
        exact hx
      · refine ⟨Or.inr (n1 x).property, ?_⟩
        change g (n1 x) ∈ Z
        rw [hkeep1]
        exact hx

end PoincareConjecture.M76.Dehn
