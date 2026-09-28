import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.RadialExtension
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.Infimum
import PoincareConjecture.Proofs.M60.Mathlib.RelativeSmoothing
import PoincareConjecture.Proofs.M58.Cor18_28_Fillings
import Mathlib.Geometry.Manifold.Metrizable











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [SecondCountableTopology M]



theorem m60_exists_c1_disk_of_null (γ : C1FreeLoopSpace (M := M))
    (hnull : IsNullHomotopicLoop γ) :
    ∃ F : LoopPlane → M, ContMDiff (𝓡 2) (𝓡 3) 1 F ∧
      ∀ z : LoopCircle, F z.val = γ z := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace LoopAmbient M
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨e, he, hboundary, hregular⟩ := m60_exists_boundary_regular_extension γ hnull
  obtain ⟨F, hF, hEq⟩ := M60.exists_c1_eqOn_compl_of_compact (F := LoopAmbient)
    (⟨e, he⟩ : C(LoopPlane, M))
    (isCompact_closedBall (0 : LoopPlane) (1 / 2 : ℝ))
    (isOpen_ball (x := (0 : LoopPlane)) (ε := (3 / 4 : ℝ)))
    (show closedBall (0 : LoopPlane) (1 / 2 : ℝ) ⊆ ball 0 (3 / 4 : ℝ) from by
      intro z hz
      rw [mem_closedBall, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right]
      linarith)
    (by
      intro z hz
      apply hregular z
      simpa only [mem_closedBall, dist_zero_right, not_le] using hz)
  refine ⟨F, hF, ?_⟩
  intro z
  have hz : z.val ∈ (ball (0 : LoopPlane) (3 / 4 : ℝ))ᶜ := by
    simp only [mem_compl_iff, mem_ball, dist_zero_right, z.property]
    norm_num
  exact (hEq hz).trans (hboundary z)



theorem m60_exists_lipschitz_disk_of_null (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (hnull : IsNullHomotopicLoop γ) :
    Nonempty (LipschitzSpanningDisk g γ) := by
  obtain ⟨F, hF, hboundary⟩ := m60_exists_c1_disk_of_null γ hnull
  exact ⟨Proofs.M58.spanningDiskOfC1 g γ F hF hboundary⟩



theorem m60FillingData_of_null (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (hnull : IsNullHomotopicLoop γ) :
    Nonempty (FillingAreaData g γ) := by
  obtain ⟨D⟩ := m60_exists_lipschitz_disk_of_null g γ hnull
  exact ⟨m60FillingData_of_disk g γ D⟩

end PoincareConjecture
