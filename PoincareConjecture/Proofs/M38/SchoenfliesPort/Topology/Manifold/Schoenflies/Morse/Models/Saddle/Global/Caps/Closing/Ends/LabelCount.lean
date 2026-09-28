import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.EndCount

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_cut_indices_nonempty (data : TerminalSaddleData M P p e) :
    Nonempty data.ends.LowerCutIndex ∧ Nonempty data.ends.UpperCutIndex := by
  have hsqrt : Real.sqrt data.eta ≤ data.r := by
    have hs := Real.sq_sqrt data.eta_pos.le
    nlinarith [data.r_pos, data.eta_lt, data.delta_lt, Real.sqrt_nonneg data.eta]
  have hlevel (i : Fin 2) :
      {q : S2 | inner Real (M.v : E3) (g q) =
        inner Real (M.v : E3) (g p) + (if i = 0 then -data.eta else data.eta)}.Nonempty := by
    let x : E2 := EuclideanSpace.single i (Real.sqrt data.eta)
    let t : Real := if i = 0 then -data.eta else data.eta
    have ht : t ∈ Icc (-data.delta) data.delta := by
      dsimp [t]
      split_ifs <;> constructor <;> linarith [data.eta_pos, data.eta_lt]
    have hxs : x ∈ closedSquare data.r := by
      fin_cases i <;> simp [x, closedSquare, abs_of_nonneg (Real.sqrt_nonneg _),
        hsqrt, data.r_pos.le]
    have hxt : -(x 0)^2 + (x 1)^2 = t := by
      fin_cases i <;> simp [x, t, Real.sq_sqrt data.eta_pos.le]
    have hmem : (data.D ∘ g) (e x) ∈
        (data.D ∘ g) '' {q : S2 | inner Real (M.v : E3) (g q) =
          inner Real (M.v : E3) (g p) + t} := by
      rw [(data.flattened_levels t ht).2.1]
      exact Or.inl ⟨x, ⟨hxs, hxt⟩, rfl⟩
    obtain ⟨q, hq, _⟩ := hmem
    exact ⟨q, hq⟩
  constructor
  · obtain ⟨q, hq⟩ := hlevel 0
    have hcut : q ∈ {q : S2 | inner Real (M.v : E3) (g q) = data.ends.lowerCut} := by
      simpa [data.lowerCut_eq, sub_eq_add_neg] using hq
    rw [← data.ends.iUnion_range_lowerCutCircle] at hcut
    obtain ⟨i, _⟩ := mem_iUnion.mp hcut
    exact ⟨i⟩
  · obtain ⟨q, hq⟩ := hlevel 1
    have hcut : q ∈ {q : S2 | inner Real (M.v : E3) (g q) = data.ends.upperCut} := by
      simpa [data.upperCut_eq] using hq
    rw [← data.ends.iUnion_range_upperCutCircle] at hcut
    obtain ⟨i, _⟩ := mem_iUnion.mp hcut
    exact ⟨i⟩

theorem terminal_cap_label_counts (data : TerminalSaddleData M P p e) :
    (Nat.card data.ends.LowerCutIndex = 1 ∧ Nat.card data.ends.UpperCutIndex = 2) ∨
      (Nat.card data.ends.LowerCutIndex = 2 ∧ Nat.card data.ends.UpperCutIndex = 1) := by
  obtain ⟨hl, hu⟩ := terminal_cut_indices_nonempty data
  let := hl
  let := hu
  have hlpos : 0 < Nat.card data.ends.LowerCutIndex := Nat.card_pos
  have hupos : 0 < Nat.card data.ends.UpperCutIndex := Nat.card_pos
  have htotal : Nat.card data.ends.EndIndex = 3 := by
    rw [← Nat.card_congr data.labels]
    simp
  rw [data.ends.card_endIndex_eq_sum] at htotal
  omega

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
