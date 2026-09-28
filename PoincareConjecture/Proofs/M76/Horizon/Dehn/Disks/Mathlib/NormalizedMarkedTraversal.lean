import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedIntervalAttachment
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MarkedIntervalDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedAttachmentSources
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.MarkedIntervalHomotopy

set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)

theorem attachment_complement_eq_marked_preimage
    {E X : Type*} {S C W B P : Set E} {Z : Set X} {f : E → X}
    (hWS : W ⊆ S) (hWB : W ∪ B = C) (hi : W ∩ B = P)
    (hQ : C = (S ∩ f ⁻¹' Z) ∪ W) (hmark : W ∩ f ⁻¹' Z = P) :
    B = S ∩ f ⁻¹' Z := by
  ext x
  have h1 := congrArg (fun A : Set E ↦ x ∈ A) hWB
  have h2 := congrArg (fun A : Set E ↦ x ∈ A) hi
  have h3 := congrArg (fun A : Set E ↦ x ∈ A) hQ
  have h4 := congrArg (fun A : Set E ↦ x ∈ A) hmark
  have hs : x ∈ W → x ∈ S := fun hx ↦ hWS hx
  simp only [mem_union, mem_inter_iff, mem_preimage] at h1 h2 h3 h4 ⊢
  tauto

theorem exists_normalized_marked_traversal_with_sources
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
    (hagree : ∀ t : I01, f0 (p0 t) = f1 (p1 t))
    (Z : Set X) (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hQ1 : Q1 = (S1 ∩ f1 ⁻¹' Z) ∪ W1)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = {a0, b0})
    (hmark1 : W1 ∩ f1 ⁻¹' Z = {a1, b1})
    (P0 : Path a0 b0) (P1 : Path a1 b1)
    (hP0S : ∀ t : I01, P0 t ∈ S0) (hP1S : ∀ t : I01, P1 t ∈ S1)
    (hP0Z : ∀ t : I01, f0 (P0 t) ∈ Z) (hP1Z : ∀ t : I01, f1 (P1 t) ∈ Z)
    (x y : Z) (U V : Path x y)
    (hU : ∀ t : I01, (U t : X) = f0 (P0 t))
    (hV : ∀ t : I01, (V t : X) = f1 (P1 t)) :
    ∃ (g : V2 → X) (R : Path x x),
      PolyhedralPLInCharts e g D ∧ g '' D = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ z ∈ D, g z ∈ Z ↔ z ∈ Q) ∧
      (∀ t : I01, (R t : X) = g (squareRimLoop t)) ∧
      R.Homotopic (U.trans V.symm) ∧
      ∃ (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (H : D ≃ₜ T) (p : I01 ≃ₜ TE),
        let j0 := fun z : S0 ↦ (H.symm ⟨n0 z, Or.inl (n0 z).property⟩ : V2)
        let j1 := fun z : S1 ↦ (H.symm ⟨n1 z, Or.inr (n1 z).property⟩ : V2)
        n0.IsFinitePL ∧ n1.IsFinitePL ∧ H.IsFinitePL ∧ p.IsFinitePL ∧
        (∀ t : I01, (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) = p t) ∧
        (∀ t : I01, (n1 ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩ : P2) = p t) ∧
        Topology.IsEmbedding j0 ∧ Topology.IsEmbedding j1 ∧ range j0 ∪ range j1 = D ∧
        (∀ z : S0, g (j0 z) = f0 z) ∧ (∀ z : S1, g (j1 z) = f1 z) ∧
        (∀ (z : S0) (w : S1), j0 z = j1 w ↔
          ∃! t : I01, (z : E0) = p0 t ∧ (w : E1) = p1 t) ∧
        ∀ A : Set X, D ∩ g ⁻¹' A =
          j0 '' {z : S0 | f0 z ∈ A} ∪ j1 '' {z : S1 | f1 z ∈ A} := by
  obtain ⟨B0, B1, hB0S', hB1S', n0, n1, p, f, q0, q1, d, hdata⟩ :=
    exists_normalized_prescribed_interval_disk_map e hcompat hS0 hS1 hW0 hW1
      hW0Q hW1Q hab0 hab1 p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree
  dsimp only at hdata
  obtain ⟨_, _, hWB0, hWB1, hi0, hi1, hn0, hn1, hp, _, _, hn0p, hn1p,
    _, _, hq00, hq01, hq10, hq11, _, _, _, hfcopy0, hfcopy1, _, hpre,
    hd, hdemb, hdimage, hdiff, _, _, hg, himage, _, _,
    r0, r1, hcont, hbase, hr0, hr1, hloop⟩ := hdata
  let g := f ∘ d
  have hrim := marked_attachment_rim_eq (fun z : S0 ↦ (n0 z : P2))
    (fun z : S1 ↦ (n1 z : P2)) (hW0Q.trans hS0.1) (hW1Q.trans hS1.1)
    hWB0 hWB1 hi0 hi1 hQ0
    (show Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ (∅ : Set E1)) ∪ W1 by
      simpa only [union_empty] using hQ1)
    hmark0 hmark1 (inter_empty W1) (hpre Z)
  simp only [preimage_empty, image_empty, union_empty] at hrim
  have hfrontier (z : V2) (hz : z ∈ D) : g z ∈ Z ↔ z ∈ Q := by
    have hdT : d z ∈ T := hdimage.subset ⟨z, hz, rfl⟩
    have h := hdiff ⟨z, hz⟩
    rw [hrim] at h
    simpa only [g, mem_inter_iff, mem_preimage, hdT, true_and, Function.comp_apply] using h
  obtain ⟨H, hH, hHval⟩ := exists_normalization_homeomorph_of_map hd hdemb hdimage
  have hsource := normalized_attachment_source_properties
    (hW0Q.trans hS0.1) (hW1Q.trans hS1.1) n0 n1 H p0 p1 p hn0p hn1p
    (g := g) (fun z ↦ congrArg f (hHval z).symm) hfcopy0 hfcopy1
  have hB0eq := attachment_complement_eq_marked_preimage
    (hW0Q.trans hS0.1) hWB0 hi0 hQ0 hmark0
  have hB1eq := attachment_complement_eq_marked_preimage
    (hW1Q.trans hS1.1) hWB1 hi1 hQ1 hmark1
  have hB0S : B0 ⊆ S0 := hB0eq.subset.trans inter_subset_left
  have hB1S : B1 ⊆ S1 := hB1eq.subset.trans inter_subset_left
  have hB0Z : MapsTo f0 B0 Z := fun _ hx ↦ (hB0eq.subset hx).2
  have hB1Z : MapsTo f1 B1 Z := fun _ hx ↦ (hB1eq.subset hx).2
  have hx0 : (x : X) = f0 a0 := by simpa only [U.source, P0.source] using hU i0
  have hy0 : (y : X) = f0 b0 := by simpa only [U.target, P0.target] using hU i1
  have hx1 : (x : X) = f1 a1 := by simpa only [V.source, P1.source] using hV i0
  have hy1 : (y : X) = f1 b1 := by simpa only [V.target, P1.target] using hV i1
  let C0 : Path x y :=
    { toFun t := ⟨f0 (q0 t), hB0Z (q0 t).property⟩
      continuous_toFun := (hf0.continuousOn.comp_continuous
        (continuous_subtype_val.comp q0.continuous)
        (fun t ↦ hB0S (q0 t).property)).subtype_mk _
      source' := Subtype.ext ((congrArg f0 hq00).trans hx0.symm)
      target' := Subtype.ext ((congrArg f0 hq01).trans hy0.symm) }
  let C1 : Path x y :=
    { toFun t := ⟨f1 (q1 t), hB1Z (q1 t).property⟩
      continuous_toFun := (hf1.continuousOn.comp_continuous
        (continuous_subtype_val.comp q1.continuous)
        (fun t ↦ hB1S (q1 t).property)).subtype_mk _
      source' := Subtype.ext ((congrArg f1 hq10).trans hx1.symm)
      target' := Subtype.ext ((congrArg f1 hq11).trans hy1.symm) }
  have hC0 (t : I01) : (C0 t : X) = f0 (q0 t) := rfl
  have hC1 (t : I01) : (C1 t : X) = f1 (q1 t) := rfl
  have hhom0 : C0.Homotopic U := by
    apply marked_interval_paths_homotopic q0 f0 (hf0.continuousOn.mono hB0S) hB0Z
      ((intervalChartPath q0).cast hq00.symm hq01.symm) P0
      (fun t ↦ (q0 t).property) _ C0 U (fun t ↦ hC0 t) hU
    intro t
    exact hB0eq.symm.subset ⟨hP0S t, hP0Z t⟩
  have hhom1 : C1.Homotopic V := by
    apply marked_interval_paths_homotopic q1 f1 (hf1.continuousOn.mono hB1S) hB1Z
      ((intervalChartPath q1).cast hq10.symm hq11.symm) P1
      (fun t ↦ (q1 t).property) _ C1 V (fun t ↦ hC1 t) hV
    intro t
    exact hB1eq.symm.subset ⟨hP1S t, hP1Z t⟩
  have hloopval (t : I01) : g (squareRimLoop t) = (r0.trans r1.symm) t :=
    congrArg (fun p : Path (f0 a0) (f0 a0) ↦ p t) hloop
  have hval (t : I01) : ((C0.trans C1.symm) t : X) = (r0.trans r1.symm) t := by
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs
    · exact (hC0 _).trans (hr0 _).symm
    · exact (hC1 _).trans (hr1 _).symm
  exact ⟨g, C0.trans C1.symm, hg, himage, hfrontier,
    fun t ↦ (hval t).trans (hloopval t).symm, hhom0.hcomp hhom1.symm₂,
    n0, n1, H, p, hn0, hn1, hH, hp, hn0p, hn1p, hsource⟩

theorem exists_normalized_marked_traversal
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
    (hagree : ∀ t : I01, f0 (p0 t) = f1 (p1 t))
    (Z : Set X) (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hQ1 : Q1 = (S1 ∩ f1 ⁻¹' Z) ∪ W1)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = {a0, b0})
    (hmark1 : W1 ∩ f1 ⁻¹' Z = {a1, b1})
    (P0 : Path a0 b0) (P1 : Path a1 b1)
    (hP0S : ∀ t : I01, P0 t ∈ S0) (hP1S : ∀ t : I01, P1 t ∈ S1)
    (hP0Z : ∀ t : I01, f0 (P0 t) ∈ Z) (hP1Z : ∀ t : I01, f1 (P1 t) ∈ Z)
    (x y : Z) (U V : Path x y)
    (hU : ∀ t : I01, (U t : X) = f0 (P0 t))
    (hV : ∀ t : I01, (V t : X) = f1 (P1 t)) :
    ∃ (g : V2 → X) (R : Path x x),
      PolyhedralPLInCharts e g D ∧ g '' D = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ z ∈ D, g z ∈ Z ↔ z ∈ Q) ∧
      (∀ t : I01, (R t : X) = g (squareRimLoop t)) ∧
      R.Homotopic (U.trans V.symm)  := by
  obtain ⟨g, R, hg, himage, hfrontier, hRval, hRhom, _⟩ :=
    exists_normalized_marked_traversal_with_sources e hcompat hS0 hS1 hW0 hW1
      hW0Q hW1Q hab0 hab1 p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree
      Z hQ0 hQ1 hmark0 hmark1 P0 P1 hP0S hP1S hP0Z hP1Z x y U V hU hV
  exact ⟨g, R, hg, himage, hfrontier, hRval, hRhom⟩

end PoincareConjecture.M76.Dehn
