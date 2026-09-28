import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.MinimizingSequence
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryNormalization

set_option autoImplicit false

open Set Filter Complex
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65Plateau_normalizedMinimizingSequence (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (hfill : Nonempty (LipschitzSpanningDisk g γ))
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ disks : ℕ → LipschitzSpanningDisk g γ,
      (∀ n, fillingArea g γ ≤ (disks n).area ∧
        (disks n).area < fillingArea g γ + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => (disks n).area) atTop (𝓝 (fillingArea g γ)) ∧
      ∀ n, ((disks n).reparameterization.inverse a).val = orthonormalBasisOneI.repr 1 ∧
        ((disks n).reparameterization.inverse b).val = orthonormalBasisOneI.repr (-1) ∧
        (((disks n).reparameterization.inverse c).val = orthonormalBasisOneI.repr I ∨
          ((disks n).reparameterization.inverse c).val = orthonormalBasisOneI.repr (-I)) := by
  classical
  obtain ⟨original, hbounds, hlimit⟩ := m65Plateau_minimizingSequence g γ hfill
  choose disks harea hfirst hsecond hthird using fun n =>
    m65SpanningDisk_threePointNormalization (original n) a b c hab hac hbc
  refine ⟨disks, ?_, ?_, fun n => ⟨hfirst n, hsecond n, hthird n⟩⟩
  · intro n
    rw [harea n]
    exact hbounds n
  · have heq : (fun n => (disks n).area) = (fun n => (original n).area) := funext harea
    rw [heq]
    exact hlimit

end PoincareConjecture
