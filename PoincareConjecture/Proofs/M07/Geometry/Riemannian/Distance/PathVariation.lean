import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Topology.EMetricSpace.BoundedVariation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem eVariationOn_le_pathELength_of_edist_le
    (g : RiemannianMetric n M) {X : Type*} [PseudoEMetricSpace X]
    {γ : ℝ → M} {η : ℝ → X} {a b : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    (hη : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      EDist.edist (η s) (η t) ≤ g.edist (γ s) (γ t)) :
    eVariationOn η (Icc a b) ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply iSup_le
  rintro ⟨k, u, hmono, hu⟩
  have hseg (i : ℕ) : EDist.edist (η (u (i + 1))) (η (u i)) ≤
      Manifold.pathELength (𝓡 n) γ (u i) (u (i + 1)) := by
    rw [edist_comm]
    exact (hη _ (hu i) _ (hu (i + 1))).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc (hu i).1 (hu (i + 1)).2)) rfl rfl
        (hmono (Nat.le_succ i)))
  have hsum (m : ℕ) :
      ∑ i ∈ Finset.range m, Manifold.pathELength (𝓡 n) γ (u i) (u (i + 1)) =
        Manifold.pathELength (𝓡 n) γ (u 0) (u m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih,
        Manifold.pathELength_add (hmono (Nat.zero_le m)) (hmono (Nat.le_succ m))]
  exact (Finset.sum_le_sum (fun i _ => hseg i)).trans
    ((hsum k).trans_le (Manifold.pathELength_mono (hu 0).1 (hu k).2))

end PoincareConjecture.RiemannianMetric
