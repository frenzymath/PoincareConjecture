import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D



theorem exists_compatible_padded_windows {I : Type*} [Finite I] [Nonempty I]
    (U : I → Set ℝ) (R : I → I → Prop) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, ∃ j, R i j ∧ t ∈ U j) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : Fin N → I,
      (∀ i : Fin N, Icc ((i.val : ℝ) / N - 1 / (4 * (N : ℝ)))
        (((i.val : ℝ) + 1) / N + 1 / (4 * (N : ℝ))) ⊆ U (c i)) ∧
      (∀ i j : Fin N, i.val + 1 = j.val → R (c i) (c j)) := by
  classical
  let T := {t : ℝ // t ∈ Icc (0 : ℝ) 1}
  choose f hfR hfU using fun (t : T) (i : I) => hcover t.val t.property i
  let W : T → Set ℝ := fun t => ⋂ i, U (f t i)
  have hW (t : T) : IsOpen (W t) := isOpen_iInter_of_finite fun i => hU (f t i)
  have hWcover : Icc (0 : ℝ) 1 ⊆ ⋃ t, W t := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, mem_iInter.mpr (hfU ⟨t, ht⟩)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hW hWcover
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  have hNR : (0 : ℝ) < N := (div_pos (by norm_num) hδ).trans hN
  have hN0 : 0 < N := by exact_mod_cast hNR
  have hmesh : 2 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNR]
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have hcenters (i : Fin N) :
      ∃ t : T, ball ((i.val : ℝ) / N) δ ⊆ W t := by
    apply hball
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hNR.le
    · apply (div_le_one hNR).mpr
      exact_mod_cast i.isLt.le
  choose w hw using hcenters
  have hpad (i : Fin N) (a : I) :
      Icc ((i.val : ℝ) / N - 1 / (4 * (N : ℝ)))
        (((i.val : ℝ) + 1) / N + 1 / (4 * (N : ℝ))) ⊆ U (f (w i) a) := by
    intro s hs
    apply mem_iInter.mp (hw i ?_) a
    rw [mem_ball, Real.dist_eq, abs_lt]
    have hpos : (0 : ℝ) < 1 / N := one_div_pos.mpr hNR
    have hquarter : (1 : ℝ) / (4 * N) = (1 / (N : ℝ)) / 4 := by ring
    have htwo : (2 : ℝ) / N = 2 * (1 / (N : ℝ)) := by ring
    rw [mem_Icc, add_div, hquarter] at hs
    rw [htwo] at hmesh
    constructor <;> linarith [hs.1, hs.2]
  let w' : ℕ → T := fun j => if h : j < N then w ⟨j, h⟩ else w ⟨0, hN0⟩
  have hw' (i : Fin N) : w' i.val = w i := dif_pos i.isLt
  let a : I := Classical.choice ‹Nonempty I›
  let d : ℕ → I := Nat.rec (f (w' 0) a) (fun k previous => f (w' (k + 1)) previous)
  refine ⟨N, hN0, fun i => d i.val, ?_, ?_⟩
  · rintro ⟨i, hi⟩ s hs
    cases i with
    | zero =>
        change s ∈ U (f (w' 0) a)
        rw [hw' ⟨0, hi⟩]
        exact hpad ⟨0, hi⟩ a hs
    | succ i =>
        change s ∈ U (f (w' (i + 1)) (d i))
        rw [hw' ⟨i + 1, hi⟩]
        exact hpad ⟨i + 1, hi⟩ (d i) hs
  · intro i j hij
    change R (d i.val) (d j.val)
    rw [← hij]
    exact hfR (w' (i.val + 1)) (d i.val)

end PoincareConjecture.M25.Topology3D
