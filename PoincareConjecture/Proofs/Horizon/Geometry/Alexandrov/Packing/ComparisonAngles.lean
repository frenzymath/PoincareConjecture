import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.HyperbolicHinge
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.TangentComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.Angle.Packing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Alexandrov

universe u v

namespace PoincareConjecture.RiemannianMetric

theorem exists_comparisonAngle_packing_bound
    (n : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ N : ℕ,
      ∀ {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M],
      ∀ (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) →
      ∀ (p : M) {ι : Type v} [Fintype ι] (q : ι → M),
        (∀ i, q i ≠ p) →
        (∀ i j, i ≠ j →
          α ≤ Poincare.Alexandrov.comparisonAngle
            (g.edist p (q i)).toReal (g.edist p (q j)).toReal
            (g.edist (q i) (q j)).toReal) →
        Fintype.card ι ≤ N := by
  classical
  obtain ⟨N, hN⟩ := Poincare.Euclidean.exists_card_le_of_unit_angle_separated
    (EuclideanSpace ℝ (Fin n)) hα
  refine ⟨N, ?_⟩
  intro M _ _ _ _ _ g D hcomplete hsec p ι _ q hq hsep
  let : MetricSpace M := g.toMetricSpace
  let : Nonempty M := ⟨p⟩
  let : ConnectedSpace M := ⟨inferInstance⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let r : ι → ℝ := fun i => (g.edist p (q i)).toReal
  have hr (i : ι) : 0 < r i := by
    change 0 < dist p (q i)
    exact dist_pos.mpr (hq i).symm
  choose γ hγ0 hγend hγgeo hγspeed hγmin using fun i =>
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hcomplete p (q i) (hr i)
  let T : ι → TangentSpace (𝓡 n) p :=
    fun i => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) 0 1
  have hT (i : ι) : ‖T i‖ = 1 := by
    change g.tangentNorm p (T i) = 1
    have heq := congrArg (fun x : M => g.tangentNorm x
      (show EuclideanSpace ℝ (Fin n) from T i)) (hγ0 i)
    exact heq.symm.trans (hγspeed i 0 ⟨le_rfl, (hr i).le⟩)
  have hangle (i j : ι) :
      comparisonAngle (r i) (r j) (dist (q i) (q j)) ≤
        InnerProductGeometry.angle (T i) (T j) := by
    apply comparisonAngle_le_angle_of_cosh_le (hr i) (hr j) (hT i) (hT j)
    have h := Alexandrov.hyperbolic_hinge g D hcomplete hsec (hr i) (hr j)
      (hγgeo i) (hγgeo j) (hγ0 i) (hγ0 j) (hγspeed j) (hγmin i) (hγmin j)
    rw [show γ i (r i) = q i from hγend i,
      show γ j (r j) = q j from hγend j] at h
    exact h
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  let b := (g.orthonormalBasis p).reindex (finCongr hdim)
  apply hN (fun i => b.repr (T i))
  · intro i
    exact (b.repr.norm_map (T i)).trans (hT i)
  · intro i j hij
    change α ≤ InnerProductGeometry.angle
      (b.repr.toLinearIsometry (T i)) (b.repr.toLinearIsometry (T j))
    rw [b.repr.toLinearIsometry.angle_map]
    exact (hsep i j hij).trans (hangle i j)

end PoincareConjecture.RiemannianMetric
