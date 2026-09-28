import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimLoop









set_option autoImplicit false

open Set Metric
open scoped unitInterval

namespace PoincareConjecture.M76.Wall

open Dehn

local notation "V2" => (Fin 2 → ℝ)

private theorem edge_zero_coordinates (t : unitInterval) :
    (squareRimEdge 0 t : V2) = ![-1 + 2 * (t : ℝ), -1] := by
  change Path.segment (![-1, -1] : V2) ![1, -1] t = _
  ext i
  fin_cases i <;>
    simp [Path.segment_apply, AffineMap.lineMap_apply_module] <;> ring

private theorem edge_one_coordinates (t : unitInterval) :
    (squareRimEdge 1 t : V2) = ![1, -1 + 2 * (t : ℝ)] := by
  change Path.segment (![1, -1] : V2) ![1, 1] t = _
  ext i
  fin_cases i
  · simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  · simp [Path.segment_apply, AffineMap.lineMap_apply_module]
    ring

private theorem edge_two_coordinates (t : unitInterval) :
    (squareRimEdge 2 t : V2) = ![1 - 2 * (t : ℝ), 1] := by
  change Path.segment (![1, 1] : V2) ![-1, 1] t = _
  ext i
  fin_cases i
  · simp [Path.segment_apply, AffineMap.lineMap_apply_module]
    ring
  · simp [Path.segment_apply, AffineMap.lineMap_apply_module]

private theorem edge_three_coordinates (t : unitInterval) :
    (squareRimEdge 3 t : V2) = ![-1, 1 - 2 * (t : ℝ)] := by
  change Path.segment (![-1, 1] : V2) ![-1, -1] t = _
  ext i
  fin_cases i
  · simp [Path.segment_apply, AffineMap.lineMap_apply_module]
    ring
  · simp [Path.segment_apply, AffineMap.lineMap_apply_module]
    ring




theorem squareRimLoop_coordinates (t : unitInterval) :
    (squareRimLoop t : V2) =
      if (t : ℝ) ≤ 1 / 4 then ![-1 + 8 * (t : ℝ), -1]
      else if (t : ℝ) ≤ 1 / 2 then ![1, -3 + 8 * (t : ℝ)]
      else if (t : ℝ) ≤ 3 / 4 then ![5 - 8 * (t : ℝ), 1]
      else ![-1, 7 - 8 * (t : ℝ)] := by
  by_cases hq : (t : ℝ) ≤ 1 / 4
  · have hh : (t : ℝ) ≤ 1 / 2 := by linarith
    have hi : 2 * (t : ℝ) ≤ 1 / 2 := by linarith
    let s : unitInterval := ⟨2 * t, ⟨by linarith [t.property.1], by linarith⟩⟩
    let r : unitInterval := ⟨2 * s, ⟨by dsimp [s]; linarith [t.property.1],
      by dsimp [s]; linarith⟩⟩
    have hout : squareRimLoop t = ((squareRimEdge 0).trans (squareRimEdge 1)) s :=
      (Path.trans_apply _ _ t).trans (dif_pos hh)
    have hin : ((squareRimEdge 0).trans (squareRimEdge 1)) s = squareRimEdge 0 r :=
      (Path.trans_apply _ _ s).trans (dif_pos hi)
    have hval := congrArg (fun x : sphere (0 : V2) 1 => x.val) (hout.trans hin)
    rw [if_pos hq, hval, edge_zero_coordinates]
    ext i
    fin_cases i
    · change -1 + 2 * (2 * (2 * (t : ℝ))) = -1 + 8 * (t : ℝ)
      ring
    · rfl
  · by_cases hh : (t : ℝ) ≤ 1 / 2
    · have hi : ¬2 * (t : ℝ) ≤ 1 / 2 := by linarith
      let s : unitInterval := ⟨2 * t, ⟨by linarith [t.property.1], by linarith⟩⟩
      let r : unitInterval := ⟨2 * s - 1,
        ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩⟩
      have hout : squareRimLoop t = ((squareRimEdge 0).trans (squareRimEdge 1)) s :=
        (Path.trans_apply _ _ t).trans (dif_pos hh)
      have hin : ((squareRimEdge 0).trans (squareRimEdge 1)) s = squareRimEdge 1 r :=
        (Path.trans_apply _ _ s).trans (dif_neg hi)
      have hval := congrArg (fun x : sphere (0 : V2) 1 => x.val) (hout.trans hin)
      rw [if_neg hq, if_pos hh, hval, edge_one_coordinates]
      ext i
      fin_cases i
      · rfl
      · change -1 + 2 * (2 * (2 * (t : ℝ)) - 1) = -3 + 8 * (t : ℝ)
        ring
    · by_cases hthree : (t : ℝ) ≤ 3 / 4
      · have hi : 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
        let s : unitInterval := ⟨2 * t - 1,
          ⟨by linarith, by linarith [t.property.2]⟩⟩
        let r : unitInterval := ⟨2 * s,
          ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩⟩
        have hout : squareRimLoop t = ((squareRimEdge 2).trans (squareRimEdge 3)) s :=
          (Path.trans_apply _ _ t).trans (dif_neg hh)
        have hin : ((squareRimEdge 2).trans (squareRimEdge 3)) s = squareRimEdge 2 r :=
          (Path.trans_apply _ _ s).trans (dif_pos hi)
        have hval := congrArg (fun x : sphere (0 : V2) 1 => x.val) (hout.trans hin)
        rw [if_neg hq, if_neg hh, if_pos hthree, hval, edge_two_coordinates]
        ext i
        fin_cases i
        · change 1 - 2 * (2 * (2 * (t : ℝ) - 1)) = 5 - 8 * (t : ℝ)
          ring
        · rfl
      · have hi : ¬2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
        let s : unitInterval := ⟨2 * t - 1,
          ⟨by linarith, by linarith [t.property.2]⟩⟩
        let r : unitInterval := ⟨2 * s - 1,
          ⟨by dsimp [s]; linarith, by dsimp [s]; linarith [t.property.2]⟩⟩
        have hout : squareRimLoop t = ((squareRimEdge 2).trans (squareRimEdge 3)) s :=
          (Path.trans_apply _ _ t).trans (dif_neg hh)
        have hin : ((squareRimEdge 2).trans (squareRimEdge 3)) s = squareRimEdge 3 r :=
          (Path.trans_apply _ _ s).trans (dif_neg hi)
        have hval := congrArg (fun x : sphere (0 : V2) 1 => x.val) (hout.trans hin)
        rw [if_neg hq, if_neg hh, if_neg hthree, hval, edge_three_coordinates]
        ext i
        fin_cases i
        · rfl
        · change 1 - 2 * (2 * (2 * (t : ℝ) - 1) - 1) = 7 - 8 * (t : ℝ)
          ring

end PoincareConjecture.M76.Wall
