import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.PrescribedAttachmentRim
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoIntervalDiskNormalization










set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)


noncomputable def squareDiskRimPath {X : Type*} [TopologicalSpace X] (f : V2 → X)
    (hf : ContinuousOn f D) : Path (f squareRimBase) (f squareRimBase) where
  toFun t := f (squareRimLoop t)
  continuous_toFun := hf.comp_continuous
    (continuous_subtype_val.comp squareRimLoop.continuous)
    (fun t ↦ sphere_subset_closedBall (squareRimLoop t).property)
  source' := congrArg (fun x : Q ↦ f x) squareRimLoop.source
  target' := congrArg (fun x : Q ↦ f x) squareRimLoop.target



theorem exists_normalized_prescribed_interval_disk_map
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
    (hp00 : (p0 (0 : unitInterval) : E0) = a0)
    (hp01 : (p0 (1 : unitInterval) : E0) = b0)
    (hp10 : (p1 (0 : unitInterval) : E1) = a1)
    (hp11 : (p1 (1 : unitInterval) : E1) = b1)
    {f0 : E0 → X} {f1 : E1 → X}
    (hf0 : PolyhedralPLInCharts e f0 S0) (hf1 : PolyhedralPLInCharts e f1 S1)
    (hagree : ∀ t : I01, f0 (p0 t) = f1 (p1 t)) :
    ∃ (B0 : Set E0) (B1 : Set E1) (hB0S : B0 ⊆ S0) (hB1S : B1 ⊆ S1)
      (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (p : I01 ≃ₜ TE) (g : P2 → X)
      (q0 : I01 ≃ₜ B0) (q1 : I01 ≃ₜ B1) (d : V2 → P2),
      let U := (fun x : S0 ↦ (n0 x : P2)) '' (Subtype.val ⁻¹' B0)
      let V := (fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' B1)
      IsFinitePLBallPair ℝ B0 {a0, b0} ∧ IsFinitePLBallPair ℝ B1 {a1, b1} ∧
      W0 ∪ B0 = Q0 ∧ W1 ∪ B1 = Q1 ∧
      W0 ∩ B0 = {a0, b0} ∧ W1 ∩ B1 = {a1, b1} ∧
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ p.IsFinitePL ∧
      (p (0 : unitInterval) : P2) = (0, 1) ∧
      (p (1 : unitInterval) : P2) = (0, 0) ∧
      (∀ t : I01, (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) = p t) ∧
      (∀ t : I01, (n1 ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩ : P2) = p t) ∧
      q0.IsFinitePL ∧ q1.IsFinitePL ∧
      (q0 (0 : unitInterval) : E0) = a0 ∧ (q0 (1 : unitInterval) : E0) = b0 ∧
      (q1 (0 : unitInterval) : E1) = a1 ∧ (q1 (1 : unitInterval) : E1) = b1 ∧
      U ∩ V = {(0, 1), (0, 0)} ∧ IsFinitePLBallPair P2 (TR ∪ TL) (U ∪ V) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S0, g (n0 x) = f0 x) ∧ (∀ x : S1, g (n1 x) = f1 x) ∧
      g '' (TR ∪ TL) = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ Z : Set X, (TR ∪ TL) ∩ g ⁻¹' Z =
        (fun x : S0 ↦ (n0 x : P2)) '' {x : S0 | f0 x ∈ Z} ∪
        (fun x : S1 ↦ (n1 x : P2)) '' {x : S1 | f1 x ∈ Z}) ∧
      FinitePiecewiseAffineOn d D ∧ Topology.IsEmbedding (fun x : D ↦ d x) ∧
      d '' D = TR ∪ TL ∧ (∀ x : D, d x ∈ U ∪ V ↔ (x : V2) ∈ Q) ∧
      (∀ t : I01, d (squareRimLoop (squareRimHalfTime false t)) =
        n0 ⟨q0 t, hB0S (q0 t).property⟩) ∧
      (∀ t : I01, d (squareRimLoop (squareRimHalfTime true t)) =
        n1 ⟨q1 t, hB1S (q1 t).property⟩) ∧
      PolyhedralPLInCharts e (g ∘ d) D ∧
      (g ∘ d) '' D = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ t : I01, (g ∘ d) (squareRimLoop (squareRimHalfTime false t)) = f0 (q0 t)) ∧
      (∀ t : I01, (g ∘ d) (squareRimLoop (squareRimHalfTime true t)) = f1 (q1 t)) ∧
      ∃ (r0 r1 : Path (f0 a0) (f0 b0)) (hcont : ContinuousOn (g ∘ d) D)
        (hbase : (g ∘ d) squareRimBase = f0 a0),
        (∀ t : I01, r0 t = f0 (q0 t)) ∧ (∀ t : I01, r1 t = f1 (q1 t)) ∧
        (squareDiskRimPath (g ∘ d) hcont).cast hbase.symm hbase.symm =
          r0.trans r1.symm := by
  obtain ⟨B0, B1, n0, n1, p, g, hB0, hB1, hWB0, hWB1, hi0, hi1,
    hn0, hn1, hp, hpzero, hpone, hn0p, hn1p, hg, hg0, hg1, hgimage, hball, hpre⟩ :=
    exists_prescribed_interval_disk_map e hcompat hS0 hS1 hW0 hW1 hW0Q hW1Q
      hab0 hab1 p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree
  have hB0S : B0 ⊆ S0 := (subset_union_right.trans hWB0.subset).trans hS0.1
  have hB1S : B1 ⊆ S1 := (subset_union_right.trans hWB1.subset).trans hS1.1
  obtain ⟨q0, hq0, hq00, hq01⟩ := hB0.exists_unitInterval_chart_with_endpoints hab0
  obtain ⟨q1, hq1, hq10, hq11⟩ := hB1.exists_unitInterval_chart_with_endpoints hab1
  let U := (fun x : S0 ↦ (n0 x : P2)) '' (Subtype.val ⁻¹' B0)
  let V := (fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' B1)
  obtain ⟨v0, hv0, hv0val⟩ := exists_prescribed_interval_image_chart n0 hn0 hB0 hB0S q0 hq0
  obtain ⟨v1, hv1, hv1val⟩ := exists_prescribed_interval_image_chart n1 hn1 hB1 hB1S q1 hq1
  have hinter : U ∩ V = {(0, 1), (0, 0)} := by
    have h := prescribed_attachment_complement_inter (hW0Q.trans hS0.1)
      (hW1Q.trans hS1.1) hB0S hB1S hi0 hi1 n0 n1 p0 p1 p
      hp00 hp01 hp10 hp11 hn0p hn1p
    simpa only [hpzero, hpone] using h
  have hv00 : (v0 (0 : unitInterval) : P2) = (0, 1) := by
    calc
      _ = (n0 ⟨q0 0, hB0S (q0 0).property⟩ : P2) := hv0val 0
      _ = (n0 ⟨p0 0, hS0.1 (hW0Q (p0 0).property)⟩ : P2) :=
        congrArg (fun x : S0 ↦ (n0 x : P2)) (Subtype.ext (hq00.trans hp00.symm))
      _ = (0, 1) := (hn0p 0).trans hpzero
  have hv01 : (v0 (1 : unitInterval) : P2) = (0, 0) := by
    calc
      _ = (n0 ⟨q0 1, hB0S (q0 1).property⟩ : P2) := hv0val 1
      _ = (n0 ⟨p0 1, hS0.1 (hW0Q (p0 1).property)⟩ : P2) :=
        congrArg (fun x : S0 ↦ (n0 x : P2)) (Subtype.ext (hq01.trans hp01.symm))
      _ = (0, 0) := (hn0p 1).trans hpone
  have hv10 : (v1 (0 : unitInterval) : P2) = (0, 1) := by
    calc
      _ = (n1 ⟨q1 0, hB1S (q1 0).property⟩ : P2) := hv1val 0
      _ = (n1 ⟨p1 0, hS1.1 (hW1Q (p1 0).property)⟩ : P2) :=
        congrArg (fun x : S1 ↦ (n1 x : P2)) (Subtype.ext (hq10.trans hp10.symm))
      _ = (0, 1) := (hn1p 0).trans hpzero
  have hv11 : (v1 (1 : unitInterval) : P2) = (0, 0) := by
    calc
      _ = (n1 ⟨q1 1, hB1S (q1 1).property⟩ : P2) := hv1val 1
      _ = (n1 ⟨p1 1, hS1.1 (hW1Q (p1 1).property)⟩ : P2) :=
        congrArg (fun x : S1 ↦ (n1 x : P2)) (Subtype.ext (hq11.trans hp11.symm))
      _ = (0, 0) := (hn1p 1).trans hpone
  obtain ⟨H, d, hH, hd, hdemb, hdimage, hdH, hdiff, hd0, hd1, _⟩ :=
    exists_two_interval_disk_normalization hball (by norm_num) hinter
      v0 v1 hv0 hv1 hv00 hv01 hv10 hv11
  have hd0' (t : I01) : d (squareRimLoop (squareRimHalfTime false t)) =
      n0 ⟨q0 t, hB0S (q0 t).property⟩ := (hd0 t).trans (hv0val t)
  have hd1' (t : I01) : d (squareRimLoop (squareRimHalfTime true t)) =
      n1 ⟨q1 t, hB1S (q1 t).property⟩ := (hd1 t).trans (hv1val t)
  obtain ⟨hgd, hgdimage⟩ := polyhedralPL_square_normalization e hg hd hdimage
  have hgd0 (t : I01) :
      (g ∘ d) (squareRimLoop (squareRimHalfTime false t)) = f0 (q0 t) := by
    change g (d _) = _
    rw [hd0']
    exact hg0 _
  have hgd1 (t : I01) :
      (g ∘ d) (squareRimLoop (squareRimHalfTime true t)) = f1 (q1 t) := by
    change g (d _) = _
    rw [hd1']
    exact hg1 _
  have ha : f0 a0 = f1 a1 := by simpa only [hp00, hp10] using hagree 0
  have hb : f0 b0 = f1 b1 := by simpa only [hp01, hp11] using hagree 1
  let r0 : Path (f0 a0) (f0 b0) :=
    { toFun := fun t ↦ f0 (q0 t)
      continuous_toFun := hf0.continuousOn.comp_continuous
        (continuous_subtype_val.comp q0.continuous) (fun t ↦ hB0S (q0 t).property)
      source' := congrArg f0 hq00
      target' := congrArg f0 hq01 }
  let r1 : Path (f0 a0) (f0 b0) :=
    { toFun := fun t ↦ f1 (q1 t)
      continuous_toFun := hf1.continuousOn.comp_continuous
        (continuous_subtype_val.comp q1.continuous) (fun t ↦ hB1S (q1 t).property)
      source' := (congrArg f1 hq10).trans ha.symm
      target' := (congrArg f1 hq11).trans hb.symm }
  have hbase : (g ∘ d) squareRimBase = f0 a0 := by
    have heq : squareRimLoop (squareRimHalfTime false 0) = squareRimBase :=
      Subtype.ext (squareRimHalf_zero false)
    simpa only [heq] using (hgd0 0).trans (congrArg f0 hq00)
  refine ⟨B0, B1, hB0S, hB1S, n0, n1, p, g, q0, q1, d,
    hB0, hB1, hWB0, hWB1, hi0, hi1, hn0, hn1, hp, hpzero, hpone, hn0p, hn1p,
    hq0, hq1, hq00, hq01, hq10, hq11, hinter, hball, hg, hg0, hg1, hgimage, hpre,
    hd, hdemb, hdimage, hdiff, hd0', hd1', hgd, hgdimage.trans hgimage, hgd0, hgd1,
    r0, r1, hgd.continuousOn, hbase, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  apply Path.ext
  funext t
  change (g ∘ d) (squareRimLoop t) = (r0.trans r1.symm) t
  rw [Path.trans_apply]
  split_ifs with ht
  · let s : I01 := ⟨2 * (t : ℝ), ⟨by linarith [t.property.1], by linarith⟩⟩
    have hs : squareRimHalfTime false s = t := by
      apply Subtype.ext
      change (2 * (t : ℝ)) / 2 = (t : ℝ)
      ring
    change (g ∘ d) (squareRimLoop t) = f0 (q0 s)
    rw [← hs]
    exact hgd0 s
  · let s : I01 := ⟨1 - (2 * (t : ℝ) - 1),
      ⟨by linarith [t.property.2], by linarith⟩⟩
    have hs : squareRimHalfTime true s = t := by
      apply Subtype.ext
      change 1 - (1 - (2 * (t : ℝ) - 1)) / 2 = (t : ℝ)
      ring
    change (g ∘ d) (squareRimLoop t) = f1 (q1 s)
    rw [← hs]
    exact hgd1 s

end PoincareConjecture.M76.Dehn
