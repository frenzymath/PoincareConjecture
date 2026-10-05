import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.SquareShellHomeomorph
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.DecreasingIntervalCover

/-!
# Finite neighborhoods in a convergent square-shell family

Pulling the exact decreasing interval identities back by the
continuous product norm gives the complete shell cover and
finite initial unions around every nonlimiting point. See
Hatcher p. 7, Hamilton 1976, p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Filter Topology

namespace SquareShell

/-- A finite initial family of nested square shells has
exactly its two outermost boundary radii. See M76 derivation 270. -/
theorem iUnion_sequence_shells {a : ℕ → ℝ} (ha : StrictAnti a) (N : ℕ) :
    (⋃ i ∈ Finset.range (N + 1), shell (a (i + 1)) (a i)) = shell (a (N + 1)) (a 0) := by
  ext p
  change (p ∈ ⋃ i ∈ Finset.range (N + 1), shell (a (i + 1)) (a i)) ↔
    ‖p‖ ∈ Icc (a (N + 1)) (a 0)
  conv_rhs => rw [← ha.iUnion_adjacent_Icc N]
  simp only [mem_iUnion, shell, mem_ofPred_eq]

/-- The full shell family covers exactly the open-inner,
closed-outer radial annulus. See M76 derivation 270. -/
theorem iUnion_sequence_shells_eq {a : ℕ → ℝ} {c : ℝ}
    (ha : StrictAnti a) (hc : ∀ n, c < a n) (hlim : Tendsto a atTop (𝓝 c)) :
    (⋃ n, shell (a (n + 1)) (a n)) = {p : ℝ × ℝ | ‖p‖ ∈ Ioc c (a 0)} := by
  ext p
  change (p ∈ ⋃ n, shell (a (n + 1)) (a n)) ↔ ‖p‖ ∈ Ioc c (a 0)
  conv_rhs => rw [← ha.iUnion_adjacent_Icc_eq_Ioc hc hlim]
  simp only [mem_iUnion, shell, mem_ofPred_eq]

/-- Every point strictly between the limiting and outer
radii has an ambient neighborhood in a finite initial union
of the actual shells. See M76 derivation 270. -/
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
