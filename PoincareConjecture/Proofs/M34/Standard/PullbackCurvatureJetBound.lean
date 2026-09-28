import PoincareConjecture.Proofs.M34.Standard.CurvatureJetNorm
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.Perturbation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option synthInstance.maxHeartbeats 100000 in





theorem curvatureDerivativeNorm_bound_of_pullback_jets
    (n m : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : Type*} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      {g : RiemannianMetric n M} (D : LeviCivitaData g)
      {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
      ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
      (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
      ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
      (∀ j ≤ 2 + m, ‖iteratedFDeriv ℝ j (g.pullbackCoefficients e) x‖ ≤ H) →
      (∀ v, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e x v v) →
      D.curvatureDerivativeNorm m (e x) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := curvatureDerivativeNorm_bound_of_coefficient_jets n m ha H
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g D U hU e he hinv x hx hjets hell
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hx (g.pullbackCoefficients e) hcoeff (fun y _ u v => g.symm (e y) _ _)
    (fun y hy w hw => by
      apply g.pos (e y)
      intro hz
      apply hw
      apply (hinv y hy).injective
      rw [map_zero]
      convert! hz using 1)
  have hmetric (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) (u v) :
      gE.inner y u v = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v) :=
    congrArg (fun B => B u v) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  rw [← DE.curvatureDerivativeNorm_eq_pullback D hV (he.mono hVU)
    (fun y hy => hinv y (hVU hy)) hmetric m hxV]
  apply hbound gE DE x
  · intro j hj
    rw [(hB.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact hjets j hj
  · intro v
    rw [heq x hxV]
    exact hell v

end PoincareConjecture.M34
