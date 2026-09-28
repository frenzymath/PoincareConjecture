import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.BandCoverage
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.UpperBandCoverage

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem sphere_image_not_mem_ball_image
    {V : Type*} [NormedAddCommGroup V] {F : V → V} (hF : Injective F)
    {x : V} (hx : x ∈ F '' sphere 0 1) : x ∉ F '' ball 0 1 := by
  rintro ⟨a, ha, heq⟩
  obtain ⟨b, hb, hbeq⟩ := hx
  have hab := hF (heq.trans hbeq.symm)
  subst b
  exact (ne_of_lt (mem_ball.mp ha)) (mem_sphere.mp hb)

theorem planar_rim_family_avoids_innermost_filling
    {ι V : Type*} [NormedAddCommGroup V]
    (A : ι → V → V) (hA : ∀ j, Injective (A j)) (i : ι)
    (hposition : ∀ j, j ≠ i →
      Disjoint (A i '' closedBall 0 1) (A j '' closedBall 0 1) ∨
        A i '' closedBall 0 1 ⊆ A j '' ball 0 1) :
    Disjoint (⋃ j, A j '' sphere 0 1) (A i '' ball 0 1) := by
  classical
  apply disjoint_left.mpr
  intro x hx hi
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  by_cases hji : j = i
  · subst j
    exact sphere_image_not_mem_ball_image (hA i) hj hi
  · rcases hposition j hji with hd | hn
    · exact disjoint_left.mp hd (image_mono ball_subset_closedBall hi)
        (image_mono sphere_subset_closedBall hj)
    · exact sphere_image_not_mem_ball_image (hA j) hj
        (hn (image_mono ball_subset_closedBall hi))

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_lower_band_avoidance
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    {r : Real} (hr : 0 < r)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y)
    (C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : ∀ j, (C j).source = univ ×ˢ Ioo (-r) r)
    (hcyl : ∀ j q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
        (data.ends.lowerCut + z) • (M.v : E3) +
          ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3))
    (hCrim : ∀ j, range (fun q : S1 => C j (q, 0)) =
      data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1)
    (A : data.ends.LowerCutIndex →
      (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)))
    (hArim : ∀ j, range (fun q : S1 =>
      (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))) =
          A j '' sphere 0 1)
    (i : data.ends.LowerCutIndex)
    (hposition : ∀ j, j ≠ i →
      Disjoint (A i '' closedBall 0 1) (A j '' closedBall 0 1) ∨
        A i '' closedBall 0 1 ⊆ A j '' ball 0 1) :
    ∃ w : Real, 0 < w ∧ 2 * w < r ∧
      ∀ y ∈ data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelBand,
        inner Real (M.v : E3) y ≤ data.ends.lowerCut + 2 * w →
          (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto (Q y) ∉ A i '' ball 0 1 := by
  obtain ⟨δ, hδ, hδr, _, hcoverage⟩ :=
    exists_terminal_lower_prepared_modelBand_coverage data Φ χ H hH hχ hplanar hlabels
      hr Q hQ C hCs hcyl hCrim
  have havoid := planar_rim_family_avoids_innermost_filling (fun j => ⇑(A j))
    (fun j => (A j).injective) i hposition
  refine ⟨δ / 4, by positivity, by linarith, ?_⟩
  intro y hy hh
  have hyband : data.toTerminalSaddleGeometry.flatten y ∈ data.toTerminalSaddleGeometry.modelBand := by
    obtain ⟨x, hx, rfl⟩ := hy
    simpa only [Diffeomorph.apply_symm_apply] using hx
  have hlower := ((terminal_physical_modelBand_mem_iff data y).mp hyband).2.1
  let z := inner Real (M.v : E3) y - data.ends.lowerCut
  have hz : z ∈ Icc 0 δ := ⟨by dsimp [z]; linarith, by dsimp [z]; linarith⟩
  have hyc : Q y ∈ ⋃ j, range (fun q : S1 => (data.ends.lowerCut + z) • (M.v : E3) +
      ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) := by
    rw [← hcoverage z hz]
    refine ⟨mem_image_of_mem _ hy, ?_⟩
    change inner Real (M.v : E3) (Q y) = _
    rw [hQ]
    dsimp [z]
    ring
  obtain ⟨j, q, heq⟩ := mem_iUnion.mp hyc
  apply disjoint_left.mp havoid
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  rw [← hArim j]
  refine ⟨q, ?_⟩
  rw [← heq]
  exact (congrArg Prod.snd ((heightCoordinates (norm_eq_of_mem_sphere M.v)).symm_apply_apply
    (data.ends.lowerCut + z, (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
      (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))))).symm

theorem exists_terminal_upper_band_avoidance
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    {r : Real} (hr : 0 < r)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y)
    (C : data.ends.UpperCutIndex → OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : ∀ j, (C j).source = univ ×ˢ Ioo (-r) r)
    (hcyl : ∀ j q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
        (-data.ends.upperCut + z) • (-(M.v : E3)) +
          ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3))
    (hCrim : ∀ j, range (fun q : S1 => C j (q, 0)) =
      data.modelDisk (data.labels.symm (.inr j)) '' sphere (0 : E2) 1)
    (A : data.ends.UpperCutIndex →
      (Hemisphere.Plane (-(M.v : E3))) ≃ₘ[Real] (Hemisphere.Plane (-(M.v : E3))))
    (hArim : ∀ j, range (fun q : S1 =>
      (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))) =
          A j '' sphere 0 1)
    (i : data.ends.UpperCutIndex)
    (hposition : ∀ j, j ≠ i →
      Disjoint (A i '' closedBall 0 1) (A j '' closedBall 0 1) ∨
        A i '' closedBall 0 1 ⊆ A j '' ball 0 1) :
    ∃ w : Real, 0 < w ∧ 2 * w < r ∧
      ∀ y ∈ data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelBand,
        inner Real (-(M.v : E3)) y ≤ -data.ends.upperCut + 2 * w →
          (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto (Q y) ∉ A i '' ball 0 1 := by
  have hQneg (y : E3) : inner Real (-(M.v : E3)) (Q y) = inner Real (-(M.v : E3)) y := by
    simp only [inner_neg_left, hQ]
  obtain ⟨δ, hδ, hδr, _, hcoverage⟩ :=
    exists_terminal_upper_prepared_modelBand_coverage data Φ χ H hH hχ hplanar hlabels
      hr Q hQ C hCs hcyl hCrim
  have havoid := planar_rim_family_avoids_innermost_filling (fun j => ⇑(A j))
    (fun j => (A j).injective) i hposition
  refine ⟨δ / 4, by positivity, by linarith, ?_⟩
  intro y hy hh
  have hyband : data.toTerminalSaddleGeometry.flatten y ∈ data.toTerminalSaddleGeometry.modelBand := by
    obtain ⟨x, hx, rfl⟩ := hy
    simpa only [Diffeomorph.apply_symm_apply] using hx
  have hupper := ((terminal_physical_modelBand_mem_iff data y).mp hyband).2.2
  have hlower : -data.ends.upperCut ≤ inner Real (-(M.v : E3)) y := by
    rw [inner_neg_left]
    linarith
  let z := inner Real (-(M.v : E3)) y + data.ends.upperCut
  have hz : z ∈ Icc 0 δ := ⟨by dsimp [z]; linarith, by dsimp [z]; linarith⟩
  have hyc : Q y ∈ ⋃ j, range (fun q : S1 => (-data.ends.upperCut + z) • (-(M.v : E3)) +
      ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) := by
    rw [← hcoverage z hz]
    refine ⟨mem_image_of_mem _ hy, ?_⟩
    change inner Real (-(M.v : E3)) (Q y) = _
    rw [hQneg]
    dsimp [z]
    ring
  obtain ⟨j, q, heq⟩ := mem_iUnion.mp hyc
  apply disjoint_left.mp havoid
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  rw [← hArim j]
  refine ⟨q, ?_⟩
  rw [← heq]
  exact (congrArg Prod.snd ((heightCoordinates (by simpa only [norm_neg] using norm_eq_of_mem_sphere M.v)).symm_apply_apply
    (-data.ends.upperCut + z, (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
      (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))))).symm

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
