import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.HyperbolicHinge
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.TangentComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.LowerCurvature











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Alexandrov

namespace PoincareConjecture.RiemannianMetric

theorem curvatureGEnegOne_of_sectional_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) :
    @Poincare.Alexandrov.CurvatureGEnegOne M g.toMetricSpace := by
  let : MetricSpace M := g.toMetricSpace
  intro q hq
  let : Nonempty M := ⟨q 0⟩
  let : ConnectedSpace M := ⟨inferInstance⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let vtx : Fin 3 → M := fun i => q ⟨i.val + 1, by omega⟩
  let r : Fin 3 → ℝ := fun i => (g.edist (q 0) (vtx i)).toReal
  have hr (i : Fin 3) : 0 < r i := by
    change 0 < dist (q 0) (vtx i)
    apply dist_pos.mpr
    exact hq.ne (by dsimp [vtx]; intro h; have := congrArg Fin.val h; simp at this)
  choose γ hγ0 hγend hγgeo hγspeed hγmin using fun i =>
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hcomplete (q 0) (vtx i) (hr i)
  let T : Fin 3 → TangentSpace (𝓡 n) (q 0) :=
    fun i => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) 0 1
  have hT (i : Fin 3) : ‖T i‖ = 1 := by
    change g.tangentNorm (q 0) (T i) = 1
    have heq := congrArg (fun x : M => g.tangentNorm x
      (show EuclideanSpace ℝ (Fin n) from T i)) (hγ0 i)
    exact heq.symm.trans (hγspeed i 0 ⟨le_rfl, (hr i).le⟩)
  have hangle (i j : Fin 3) :
      comparisonAngle (r i) (r j) (dist (vtx i) (vtx j)) ≤
        InnerProductGeometry.angle (T i) (T j) := by
    apply comparisonAngle_le_angle_of_cosh_le (hr i) (hr j) (hT i) (hT j)
    have h := Alexandrov.hyperbolic_hinge g D hcomplete hsec (hr i) (hr j)
      (hγgeo i) (hγgeo j) (hγ0 i) (hγ0 j) (hγspeed j) (hγmin i) (hγmin j)
    rw [show γ i (r i) = vtx i from hγend i,
      show γ j (r j) = vtx j from hγend j] at h
    exact h
  have hsum := add_le_add (add_le_add (hangle 0 1) (hangle 0 2)) (hangle 1 2)
  exact hsum.trans (angle_sum_le_two_pi (T 0) (T 1) (T 2))

end PoincareConjecture.RiemannianMetric
