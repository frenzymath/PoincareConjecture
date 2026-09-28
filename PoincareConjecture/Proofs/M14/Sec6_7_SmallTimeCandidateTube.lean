import PoincareConjecture.Proofs.M14.Sec6_7_CompactSurvival
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}




theorem exists_smallTimeCandidate_tube (E : M14ExponentialFamily G T x)
    {B : Set (G.Horizontal x)} (hB : IsCompact B) {O : Set G.Point}
    (hO : IsOpen O) (hxO : x ∈ O) {δ : ℝ} (hδ : 0 < δ)
    (hwindow : Icc (T - δ) T ⊆ I.domain) :
    ∃ N K U : Set (G.Horizontal x), IsOpen N ∧ B ⊆ N ∧ N ⊆ K ∧
      IsCompact K ∧ K ⊆ U ∧ IsOpen U ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
        ∀ W ∈ U, ∀ σ ∈ Icc 0 η,
          (W, Real.sqrt σ) ∈ E.domain ∧ E.gamma W (Real.sqrt σ) ∈ O := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  obtain ⟨R, _hR, hBR⟩ := hB.isBounded.exists_pos_norm_le
  let N := Metric.ball (0 : G.Horizontal x) (R + 1)
  let K := Metric.closedBall (0 : G.Horizontal x) (R + 1)
  let U := Metric.ball (0 : G.Horizontal x) (R + 2)
  let L := Metric.closedBall (0 : G.Horizontal x) (R + 2)
  have hBN : B ⊆ N := by
    intro W hW
    change dist W 0 < R + 1
    rw [dist_zero_right]
    exact (hBR W hW).trans_lt (lt_add_one R)
  have hKU : K ⊆ U := by
    intro W hW
    change dist W 0 ≤ R + 1 at hW
    change dist W 0 < R + 2
    linarith
  obtain ⟨η, hη, hηδ, hsurv⟩ := compact_initial_survival_and_capture E
    (B := L) (isCompact_closedBall _ _) ⟨O, hO, hxO, Subset.rfl⟩ hδ hwindow
  exact ⟨N, K, U, Metric.isOpen_ball, hBN, Metric.ball_subset_closedBall,
    isCompact_closedBall _ _, hKU, Metric.isOpen_ball, η, hη, hηδ,
    fun W hW => hsurv W (Metric.ball_subset_closedBall hW)⟩

end PoincareConjecture.M14
