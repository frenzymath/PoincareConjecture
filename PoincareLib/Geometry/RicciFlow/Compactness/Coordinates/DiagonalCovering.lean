import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.IndexedCovering
import PoincareLib.Topology.Sequences.Diagonal

/-!
# Diagonal selection of controlled source-chart covers

Each integer source-radius stage has its own fixed finite chart index set. A
single strict subsequence makes every earlier stage available at each later
index, and retains all metric-jet bounds whose order is no larger than the
stage index.

Reference: Morgan--Tian, Proposition 5.14, pp. 90--91.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.PointedRicciFlowCompactnessHypotheses

theorem exists_diagonal_normalChartCovers
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hn : 1 ≤ n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ R ρ a b : ℕ → ℝ, ∃ N : ℕ → ℕ,
        (∀ j, 0 < ρ j ∧ 2 * ρ j < R j ∧ 0 < a j ∧ 0 < b j) ∧
        ∀ k j, j ≤ k →
          let C := H.sequence.carrier (σ k)
          let F := H.sequence.flow (σ k)
          letI : TopologicalSpace C.carrier := C.topologicalSpace
          letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
          letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
          ∃ cover : NormalChartCover F.metricAt F.base T' T (j + 1)
            (R j) (ρ j) (a j) (b j) (N j),
            cover.centre 0 = F.base := by
  classical
  choose R ρ a b hρ hρR ha hb N hcover using fun j : ℕ =>
    H.eventually_nonempty_normalChartCover hn (A := ((j : ℝ) + 1)) (by positivity)
  let P : ℕ → ℕ → Prop := fun j k =>
    let C := H.sequence.carrier k
    let F := H.sequence.flow k
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    Nonempty (NormalChartCover F.metricAt F.base T' T ((j : ℝ) + 1)
      (R j) (ρ j) (a j) (b j) (N j))
  have hP : ∀ j, ∀ᶠ k in atTop, P j k := by
    intro j
    filter_upwards [hcover j] with k hk
    exact hk
  obtain ⟨σ, hσ, hPσ⟩ := Poincare.exists_strictMono_forall_le_of_eventually hP
  refine ⟨σ, hσ, R, ρ, a, b, N, ?_, ?_⟩
  · intro j
    exact ⟨hρ j, hρR j, ha j, hb j⟩
  · intro k j hkj
    let C := H.sequence.carrier (σ k)
    let F := H.sequence.flow (σ k)
    let : TopologicalSpace C.carrier := C.topologicalSpace
    let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    obtain ⟨cover⟩ := hPσ k j hkj
    exact ⟨cover, cover.centre_zero⟩

end PoincareMT.PointedRicciFlowCompactnessHypotheses
