import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzConfinedEnergy
import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerEuler
import PoincareConjecture.Proofs.M14.Sec6_2_EulerEquation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}





theorem exists_confined_minimizers_with_uniform_square_speed
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {N F0 : Set G.Point} {δ H D CR Cgrad : ℝ}
    (hδ : 0 < δ) (hD : 0 ≤ D) (hCR : 0 ≤ CR) (hCgrad : 0 ≤ Cgrad)
    (hclock : ∀ q ∈ N, δ ≤ Real.sqrt (T - G.spacetime.timeFunction q) ∧
      Real.sqrt (T - G.spacetime.timeFunction q) ≤ H)
    (hmin : ∀ q ∈ N, ∃ p : M14BackwardPath G T 0 (T - G.spacetime.timeFunction q) x q,
      M14IsMinimizing p ∧ ∀ s ∈ Icc 0 (T - G.spacetime.timeFunction q), p.curve s ∈ F0)
    (hL : ∀ q ∈ N, ∀ p : M14BackwardPath G T 0 (T - G.spacetime.timeFunction q) x q,
      M14IsMinimizing p → M14BackwardLAction G p ≤ D)
    (hRic : ∀ q ∈ F0, ∀ v w : G.Horizontal q, |horizontalRicci G.leafwise q v w| ≤
      CR * Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
        Real.sqrt (G.spacetime.horizontalMetric.inner q w w))
    (hgrad : ∀ q ∈ F0, ∀ v : G.Horizontal q,
      |M14HorizontalScalarDifferential G q v.val| ≤
        Cgrad * Real.sqrt (G.spacetime.horizontalMetric.inner q v v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ N,
      ∃ p : M14BackwardPath G T 0 (T - G.spacetime.timeFunction q) x q,
        M14IsMinimizing p ∧ ∃ R : M14SquareRootPath G p,
          ∃ ER : M14PullbackExtension G R.curve
            (M14SqrtParameterInterval 0 (T - G.spacetime.timeFunction q)) R.horizontal_velocity,
            (∀ s ∈ M14SqrtParameterInterval 0 (T - G.spacetime.timeFunction q), ∀ W,
              M14SquareRootEulerResidual G R ER s W = 0) ∧
            ∀ s ∈ M14SqrtParameterInterval 0 (T - G.spacetime.timeFunction q),
              G.spacetime.horizontalMetric.inner (R.curve s)
                (R.horizontal_velocity s) (R.horizontal_velocity s) + 4 * s ^ 2 ≤ C ^ 2 := by
  let A := 2 * H ^ 2 * Cgrad + 4 * H * CR
  let B := Real.exp (A * H) * (2 * D + 4 * ((n : ℝ) * CR) * H ^ 3 + H)
  refine ⟨Real.sqrt (B / δ + 4 * H ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro q hq
  obtain ⟨p, hp, hconf⟩ := hmin q hq
  obtain ⟨E0, hE0⟩ := minimizerEulerStatement hCoordinates hM12 T 0 _ x q p hp
  obtain ⟨R, ER, hEuler⟩ := squareRootRegularizationStatement hCoordinates hM12
    T 0 _ x q p E0 hE0
  have hconfR (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0
      (T - G.spacetime.timeFunction q)) : R.curve s ∈ F0 := by
    rw [R.agrees s hs]
    apply hconf
    have hs0 : 0 ≤ s := by simpa only [Real.sqrt_zero] using hs.1
    exact ⟨sq_nonneg s, (sq_le_sq₀ hs0 (Real.sqrt_nonneg _) |>.mpr hs.2).trans
      (Real.sq_sqrt p.tau_lt.le).le⟩
  refine ⟨p, hp, R, ER, hEuler, ?_⟩
  intro s hs
  exact squareRoot_energy_uniform_bound hM12 R ER hEuler hδ (hclock q hq).1
    (hclock q hq).2 hCR hCgrad hD (hL q hq p hp)
    (fun r hr => hRic (R.curve r) (hconfR r hr))
    (fun r hr => hgrad (R.curve r) (hconfR r hr)) hs

end PoincareConjecture.M14
