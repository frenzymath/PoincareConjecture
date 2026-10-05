import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.NormalizedIntervalAttachment
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.MarkedIntervalDiskAttachment

/-!
# Proper square maps from the actual terminal interval attachment

The two original marked-boundary equations identify the entire rim of the
constructed attachment. Its square normalization therefore avoids the target
frontier everywhere in the disk interior while retaining both complete
complementary boundary parameters. See Dehn039, sections 5--7.
-/

set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel
open scoped unitInterval

namespace PoincareMT.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)

/-- Construct a square disk map with its exact frontier preimage and literal
two-interval rim traversal from the original terminal attachment data. -/
theorem exists_normalized_terminal_marked_disk_map
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
    (hagree : ∀ t : I01, f0 (p0 t) = f1 (p1 t))
    (Z : Set X) (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hQ1 : Q1 = (S1 ∩ f1 ⁻¹' Z) ∪ W1)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = {a0, b0})
    (hmark1 : W1 ∩ f1 ⁻¹' Z = {a1, b1}) :
    ∃ (B0 : Set E0) (B1 : Set E1) (q0 : I01 ≃ₜ B0) (q1 : I01 ≃ₜ B1)
      (g : V2 → X),
      IsFinitePLBallPair ℝ B0 {a0, b0} ∧ IsFinitePLBallPair ℝ B1 {a1, b1} ∧
      W0 ∪ B0 = Q0 ∧ W1 ∪ B1 = Q1 ∧
      W0 ∩ B0 = {a0, b0} ∧ W1 ∩ B1 = {a1, b1} ∧
      q0.IsFinitePL ∧ q1.IsFinitePL ∧
      (q0 (0 : unitInterval) : E0) = a0 ∧ (q0 (1 : unitInterval) : E0) = b0 ∧
      (q1 (0 : unitInterval) : E1) = a1 ∧ (q1 (1 : unitInterval) : E1) = b1 ∧
      PolyhedralPLInCharts e g D ∧ g '' D = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ x ∈ D, g x ∈ Z ↔ x ∈ Q) ∧
      (∀ t : I01, g (squareRimLoop (squareRimHalfTime false t)) = f0 (q0 t)) ∧
      (∀ t : I01, g (squareRimLoop (squareRimHalfTime true t)) = f1 (q1 t)) ∧
      ∃ (r0 r1 : Path (f0 a0) (f0 b0)) (hcont : ContinuousOn g D)
        (hbase : g squareRimBase = f0 a0),
        (∀ t : I01, r0 t = f0 (q0 t)) ∧ (∀ t : I01, r1 t = f1 (q1 t)) ∧
        (squareDiskRimPath g hcont).cast hbase.symm hbase.symm = r0.trans r1.symm := by
  obtain ⟨B0, B1, hB0S, hB1S, n0, n1, p, g, q0, q1, d, hdata⟩ :=
    exists_normalized_prescribed_interval_disk_map e hcompat hS0 hS1 hW0 hW1
      hW0Q hW1Q hab0 hab1 p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree
  dsimp only at hdata
  obtain ⟨hB0, hB1, hWB0, hWB1, hi0, hi1, _, _, _, _, _, _, _,
    hq0, hq1, hq00, hq01, hq10, hq11, _, _, _, _, _, _, hpre,
    _, _, hdimage, hdiff, _, _, hgd, hgdimage, hgd0, hgd1, hpaths⟩ := hdata
  have hrim := marked_attachment_rim_eq (fun x : S0 ↦ (n0 x : P2))
    (fun x : S1 ↦ (n1 x : P2)) (hW0Q.trans hS0.1) (hW1Q.trans hS1.1)
    hWB0 hWB1 hi0 hi1 hQ0
    (show Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ (∅ : Set E1)) ∪ W1 by simpa only [union_empty] using hQ1)
    hmark0 hmark1 (inter_empty W1) (hpre Z)
  simp only [preimage_empty, image_empty, union_empty] at hrim
  refine ⟨B0, B1, q0, q1, g ∘ d, hB0, hB1, hWB0, hWB1, hi0, hi1,
    hq0, hq1, hq00, hq01, hq10, hq11, hgd, hgdimage, ?_, hgd0, hgd1, hpaths⟩
  intro x hx
  have hdT : d x ∈ TR ∪ TL := hdimage.subset ⟨x, hx, rfl⟩
  have h := hdiff ⟨x, hx⟩
  rw [hrim] at h
  simpa only [mem_inter_iff, mem_preimage, hdT, true_and, Function.comp_apply] using h

end PoincareMT.M76.Dehn
