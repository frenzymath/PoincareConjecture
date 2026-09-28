import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.UpperLevel.Parametrization

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Nested
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def retainedBand : Set S2 := height ⁻¹' Icc 1 (13 / 10)

def bandLeft (z : Real) : Real := max (levelAbscissa z) (-Real.sqrt (1-z^2))

def bandRight (z : Real) : Real := min (upperAbscissa z) (Real.sqrt (1-z^2))

def bandX (z t : Real) : Real := (1-t)*bandLeft z+t*bandRight z

def bandRectangle : Set (Real × Real) := Icc lowerRoot 1 ×ˢ Icc 0 1

def bandPatch (σ : Real) (w : Real × Real) : E3 :=
  vector (bandX w.1 w.2) (σ*Real.sqrt (1-w.1^2-(bandX w.1 w.2)^2)) w.1

theorem band_bounds {z : Real} (hz : z ∈ Icc lowerRoot 1) :
    bandLeft z ≤ bandRight z := by
  have hroot := Real.sqrt_nonneg (1-z^2)
  have hzlower : -1 ≤ z := by linarith [lowerRoot_bounds.1, hz.1]
  have hsq : 0 ≤ 1-z^2 := by nlinarith [hz.2]
  have hs := Real.sq_sqrt hsq
  have hU : 0 < upperAbscissa z := by
    dsimp [upperAbscissa]
    nlinarith [sq_nonneg (z-1/2)]
  have hL : levelAbscissa z ≤ Real.sqrt (1-z^2) := by
    by_cases hz0 : 0 ≤ z
    · have hLn : levelAbscissa z ≤ 0 := by
        dsimp [levelAbscissa]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hz.2])
      exact hLn.trans hroot
    · have hr : 0 ≤ levelRadicand z :=
        (levelRadicand_nonneg_iff z).mpr (Or.inl ⟨hz.1, by linarith⟩)
      dsimp [levelRadicand] at hr
      nlinarith
  dsimp [bandLeft, bandRight]
  apply max_le
  · apply le_min
    · dsimp [levelAbscissa, upperAbscissa]
      nlinarith
    · exact hL
  · exact le_min (by linarith) (by linarith)

theorem bandX_mem {z t : Real} (hz : z ∈ Icc lowerRoot 1) (ht : t ∈ Icc 0 1) :
    bandX z t ∈ Icc (bandLeft z) (bandRight z) := by
  have h := band_bounds hz
  dsimp [bandX]
  constructor <;> nlinarith [ht.1, ht.2]

theorem bandX_sq {z t : Real} (hz : z ∈ Icc lowerRoot 1) (ht : t ∈ Icc 0 1) :
    0 ≤ 1-z^2-(bandX z t)^2 := by
  have hx := bandX_mem hz ht
  have hzlower : -1 ≤ z := by linarith [lowerRoot_bounds.1, hz.1]
  have hs := Real.sq_sqrt (show 0 ≤ 1-z^2 by nlinarith [hz.2])
  have hlo : -Real.sqrt (1-z^2) ≤ bandX z t := (le_max_right _ _).trans hx.1
  have hhi : bandX z t ≤ Real.sqrt (1-z^2) := hx.2.trans (min_le_right _ _)
  nlinarith [Real.sqrt_nonneg (1-z^2)]

theorem bandPatch_continuous (σ : Real) : Continuous (bandPatch σ) := by
  unfold bandPatch bandX bandLeft bandRight levelAbscissa upperAbscissa vector
  fun_prop

theorem bandPatch_mem_sphere {σ : Real} (hσ : σ ^ 2 = 1)
    {w : Real × Real} (hw : w ∈ bandRectangle) : bandPatch σ w ∈ sphere (0 : E3) 1 := by
  have hs := Real.sq_sqrt (bandX_sq hw.1 hw.2)
  have hn : ‖bandPatch σ w‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, bandPatch,
      vector_zero, vector_one, vector_two, mul_pow, hσ, one_mul, hs]
    ring
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (bandPatch σ w)]

theorem height_bandPatch {σ : Real} (hσ : σ ^ 2 = 1)
    {w : Real × Real} (hw : w ∈ bandRectangle) :
    height ⟨bandPatch σ w, bandPatch_mem_sphere hσ hw⟩ ∈ Icc 1 (13 / 10) := by
  rw [height_apply]
  simp only [bandPatch, vector_zero, vector_one, vector_two, mul_pow, hσ,
    one_mul, Real.sq_sqrt (bandX_sq hw.1 hw.2)]
  have hx := bandX_mem hw.1 hw.2
  have hlo : levelAbscissa w.1 ≤ bandX w.1 w.2 := (le_max_left _ _).trans hx.1
  have hhi : bandX w.1 w.2 ≤ upperAbscissa w.1 := hx.2.trans (min_le_left _ _)
  dsimp [levelAbscissa] at hlo
  dsimp [upperAbscissa] at hhi
  constructor <;> nlinarith

theorem retainedBand_latitude {p : S2} (hp : p ∈ retainedBand) :
    (p : E3) 2 ∈ Icc lowerRoot 1 := by
  have hn : ((p : E3) 0)^2+((p : E3) 1)^2+((p : E3) 2)^2=1 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    exact hn.symm
  have hz : (p : E3) 2 ≤ 1 := by nlinarith [sq_nonneg ((p : E3) 0), sq_nonneg ((p : E3) 1)]
  refine ⟨?_, hz⟩
  by_cases hz0 : 0 ≤ (p : E3) 2
  · exact lowerRoot_bounds.2.le.trans hz0
  have hh : 1 ≤ height p := hp.1
  rw [height_apply] at hh
  have hx : levelAbscissa ((p : E3) 2) ≤ (p : E3) 0 := by
    dsimp [levelAbscissa]
    nlinarith
  have hL : 0 ≤ levelAbscissa ((p : E3) 2) := by
    dsimp [levelAbscissa]
    nlinarith
  have hr : 0 ≤ levelRadicand ((p : E3) 2) := by
    dsimp [levelRadicand]
    nlinarith [sq_nonneg ((p : E3) 1)]
  rcases (levelRadicand_nonneg_iff _).mp hr with hr | hr
  · exact hr.1
  · linarith [hr.1, lowerRoot_bounds.2, upperRoot_bounds.1]

end Poincare.Manifold.Schoenflies.Saddle.Nested

end

end M38Schoenflies
