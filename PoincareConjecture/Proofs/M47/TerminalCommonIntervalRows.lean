import PoincareConjecture.Proofs.M47.TerminalCommonIntervalAssembly
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoherence
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalDiagonal









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (H : ∀ k, M33RegularHistoryData (W k)) (t : ℕ → ℝ)
  (ht : ∀ k, t k ∈ (H k).generalized.interval)
  (x : ∀ k, ((H k).generalized.slice (t k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W H t ht x hPositive hDiverges


theorem terminalCommonInterval_coherent_row
    (k n : ℕ) (T B : ℕ → ℝ) (hT : Monotone T) {A eta : ℝ}
    (hc : ∀ j ≤ n, Nonempty (ControlledBlowupCylinder V k A (T j) (B j) eta)) :
    ∃ e : ControlledBlowupCylinder V k A (T n) (B n) eta,
      ∀ j (hj : j ≤ n), ∀ s (hs : s ∈ Icc (-T j) 0), ∀ y ∈ (V).baseBall k A,
        |((V).flow k).curvatureNorm
          (e.embedding.pointMap s ⟨(neg_le_neg (hT hj)).trans hs.1, hs.2⟩ y)| ≤
            B j * (V).scale k := by
  obtain ⟨e⟩ := hc n le_rfl
  refine ⟨e, ?_⟩
  intro j hj s hs y hy
  obtain ⟨f⟩ := hc j hj
  have hsource : IsOpen ((V).baseBall k A) := M04.initial_ball_isOpen _ _ _
  have hsLong : s ∈ Icc (-T n) 0 := ⟨(neg_le_neg (hT hj)).trans hs.1, hs.2⟩
  have hI : Icc s 0 ⊆ Icc (-T n) 0 := Icc_subset_Icc hsLong.1 le_rfl
  have hJ : Icc s 0 ⊆ Icc (-T j) 0 := Icc_subset_Icc hs.1 le_rfl
  have hterminal : e.embedding.pointMap 0 (hI ⟨hs.2, le_rfl⟩) y =
      f.embedding.pointMap 0 (hJ ⟨hs.2, le_rfl⟩) y :=
    (e.zero_identity _ y hy).trans (f.zero_identity _ y hy).symm
  have hagree := terminalCommonInterval_generalized_eq (H k) e.embedding f.embedding
    ordConnected_Icc ordConnected_Icc hsource hsource hs.2 hI hJ y hy y hy hterminal
  have hpoint : e.embedding.pointMap s hsLong y = f.embedding.pointMap s hs y :=
    congrArg (fun z => (⟨t k + s / (V).scale k, z⟩ : (H k).generalized.point)) hagree
  rw [hpoint]
  exact f.curvature_bound s hs y hy



theorem terminalCommonInterval_actual_diagonal
    (T B : ℕ → ℝ) (hT : Monotone T)
    (hc : ∀ j : ℕ, ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k in atTop, Nonempty (ControlledBlowupCylinder V k A (T j) (B j) eta)) :
    ∃ beta : ℕ → ℕ, StrictMono beta ∧ ∀ n : ℕ,
      ∃ e : ControlledBlowupCylinder V (beta n) (n + 1) (T n) (B n) (1 / (n + 1)),
        ∀ j (hj : j ≤ n), ∀ s (hs : s ∈ Icc (-T j) 0),
          ∀ y ∈ (V).baseBall (beta n) (n + 1),
            |((V).flow (beta n)).curvatureNorm
              (e.embedding.pointMap s ⟨(neg_le_neg (hT hj)).trans hs.1, hs.2⟩ y)| ≤
                B j * (V).scale (beta n) := by
  obtain ⟨beta, hbeta, hb⟩ := terminalCommonInterval_diagonal_cylinders V T B hc
  exact ⟨beta, hbeta, fun n => terminalCommonInterval_coherent_row F W H t ht x
    hPositive hDiverges (beta n) n T B hT (hb n)⟩

end PoincareConjecture.M47
