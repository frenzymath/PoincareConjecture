import PoincareConjecture.Proofs.M76.Mathlib.SquareShellHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.DecreasingIntervalCover










set_option autoImplicit false

open Set Filter Topology

namespace SquareShell



theorem iUnion_sequence_shells {a : ℕ → ℝ} (ha : StrictAnti a) (N : ℕ) :
    (⋃ i ∈ Finset.range (N + 1), shell (a (i + 1)) (a i)) = shell (a (N + 1)) (a 0) := by
  ext p
  change (p ∈ ⋃ i ∈ Finset.range (N + 1), shell (a (i + 1)) (a i)) ↔
    ‖p‖ ∈ Icc (a (N + 1)) (a 0)
  conv_rhs => rw [← ha.iUnion_adjacent_Icc N]
  simp only [mem_iUnion, shell, mem_ofPred_eq]



theorem iUnion_sequence_shells_eq {a : ℕ → ℝ} {c : ℝ}
    (ha : StrictAnti a) (hc : ∀ n, c < a n) (hlim : Tendsto a atTop (𝓝 c)) :
    (⋃ n, shell (a (n + 1)) (a n)) = {p : ℝ × ℝ | ‖p‖ ∈ Ioc c (a 0)} := by
  ext p
  change (p ∈ ⋃ n, shell (a (n + 1)) (a n)) ↔ ‖p‖ ∈ Ioc c (a 0)
  conv_rhs => rw [← ha.iUnion_adjacent_Icc_eq_Ioc hc hlim]
  simp only [mem_iUnion, shell, mem_ofPred_eq]




theorem exists_sequence_shell_neighborhood {a : ℕ → ℝ} {c : ℝ}
    (ha : StrictAnti a) (hlim : Tendsto a atTop (𝓝 c))
    {p : ℝ × ℝ} (hp : ‖p‖ ∈ Ioo c (a 0)) :
    ∃ J : Finset ℕ, p ∈ interior (⋃ i ∈ J, shell (a (i + 1)) (a i)) := by
  have hevent := hlim.eventually (isOpen_Iio.mem_nhds hp.1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨Finset.range (N + 1), ?_⟩
  rw [iUnion_sequence_shells ha N]
  apply mem_interior_iff_mem_nhds.mpr
  have hopen : IsOpen {x : ℝ × ℝ | ‖x‖ ∈ Ioo (a (N + 1)) (a 0)} :=
    isOpen_Ioo.preimage continuous_norm
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨hN (N + 1) (Nat.le_succ N), hp.2⟩)
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

end SquareShell
