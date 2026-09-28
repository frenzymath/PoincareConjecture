import PoincareConjecture.Proofs.M76.Mathlib.SquareShellIdentity
import PoincareConjecture.Proofs.M76.Mathlib.SquareShellSequenceIncidence
import PoincareConjecture.Proofs.M76.Mathlib.LocallyFinitePLFamilyGluing

set_option autoImplicit false

open Set Filter Topology Geometry

namespace SquareShell

theorem exists_sequence_openPartialHomeomorph {a b : ℕ → ℝ} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (ha : StrictAnti a) (hb : StrictAnti b)
    (habove : ∀ n, c < a n) (hbabove : ∀ n, d < b n)
    (halim : Tendsto a atTop (𝓝 c)) (hblim : Tendsto b atTop (𝓝 d)) :
    ∃ H : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      H.source = {x | ‖x‖ ∈ Ioo c (a 0)} ∧
      H.target = {y | ‖y‖ ∈ Ioo d (b 0)} ∧
      H ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
      ∀ n (x : ℝ × ℝ), x ∈ shell (a (n + 1)) (a n) →
        ‖H x‖ = radiusMap (a (n + 1)) (a n) (b (n + 1)) (b n) ‖x‖ ∧
        (a (n + 1) = b (n + 1) → a n = b n → H x = x) := by
  have hex (n : ℕ) := exists_fixed_radius_homeomorph
    (hc.trans_lt (habove (n + 1))) (ha (Nat.lt_succ_self n))
    (hd.trans_lt (hbabove (n + 1))) (hb (Nat.lt_succ_self n))
  choose e he hdata hfixed using hex
  have hradius := fun n x => (hdata n x).1
  have hoverlap := sequence_shell_overlap_iff ha hb e hradius
  have hagree := sequence_shell_agree ha e (fun n x => (hdata n x).2.1)
    (fun n x => (hdata n x).2.2)
  let U : Set (ℝ × ℝ) := {x | ‖x‖ ∈ Ioo c (a 0)}
  let V : Set (ℝ × ℝ) := {y | ‖y‖ ∈ Ioo d (b 0)}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_norm
  have hV : IsOpen V := isOpen_Ioo.preimage continuous_norm
  have hUS : U ⊆ ⋃ n, shell (a (n + 1)) (a n) := by
    rw [iUnion_sequence_shells_eq ha habove halim]
    exact fun _ hx => ⟨hx.1, hx.2.le⟩
  have hVT : V ⊆ ⋃ n, shell (b (n + 1)) (b n) := by
    rw [iUnion_sequence_shells_eq hb hbabove hblim]
    exact fun _ hy => ⟨hy.1, hy.2.le⟩
  obtain ⟨H, hHS, hHT, hPL, _, hHval, _⟩ :=
    Homeomorph.exists_openPartialHomeomorph_of_finitePL_family
      (fun n => shell (a (n + 1)) (a n)) (fun n => shell (b (n + 1)) (b n))
      e he hoverlap hagree U V hU hV hUS hVT
      (sequence_shell_open_membership ha hb habove hbabove e hradius)
      (fun _ hx => exists_sequence_shell_neighborhood ha halim hx)
      (fun _ hy => exists_sequence_shell_neighborhood hb hblim hy)
  refine ⟨H, hHS, hHT, ?_, ?_⟩
  · apply (mem_piecewiseAffineGroupoid_iff_forward H).mpr
    rw [hHS]
    exact hPL
  · intro n x hx
    refine ⟨(congrArg norm (hHval n ⟨x, hx⟩)).trans (hdata n ⟨x, hx⟩).1, ?_⟩
    intro hl hu
    exact (hHval n ⟨x, hx⟩).trans (hfixed n hl hu ⟨x, hx⟩)

end SquareShell
