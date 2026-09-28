import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.JetBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.PullbackRicci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.Perturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.SpacetimeBounds

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_affine_pullback_ricci_component_jet_bound
    (n q : ℕ) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {g : RiemannianMetric n M} (D : LeviCivitaData g)
        {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e x v v) →
        (∀ v, g.pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ s ≤ q + 1, D.curvatureDerivativeNorm s (e x) ≤ K s) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j (g.pullbackCoefficients e) x‖ ≤ A ^ j) →
        ∀ p r : Fin n, ‖iteratedFDeriv ℝ (q + 1)
          (fun y => D.ricci (e y)
            (mfderiv (𝓡 n) (𝓡 n) e y (EuclideanSpace.basisFun (Fin n) ℝ p))
            (mfderiv (𝓡 n) (𝓡 n) e y (EuclideanSpace.basisFun (Fin n) ℝ r))) x‖ ≤
          C * (1 + ‖iteratedFDeriv ℝ (q + 1) (g.pullbackCoefficients e) x‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_affine_ricci_component_jet_bound
    n q (Real.sqrt b) (Real.sqrt_nonneg b) K hK ha b A hA
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g D U hU e he hi x hx hlower hupper hcurv hjets p r
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hx (g.pullbackCoefficients e) hcoeff (fun y _ u v => g.symm (e y) _ _)
    (fun y hy w hw => by
      apply g.pos (e y)
      intro hz
      apply hw
      apply (hi y hy).injective
      rw [map_zero]
      convert! hz using 1)
  have hmetric (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) (u v) :
      gE.inner y u v = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v) :=
    congrArg (fun B => B u v) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  have hRic : (fun y => DE.ricci y (EuclideanSpace.basisFun (Fin n) ℝ p)
      (EuclideanSpace.basisFun (Fin n) ℝ r)) =ᶠ[𝓝 x]
      (fun y => D.ricci (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y (EuclideanSpace.basisFun (Fin n) ℝ p))
        (mfderiv (𝓡 n) (𝓡 n) e y (EuclideanSpace.basisFun (Fin n) ℝ r))) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact DE.ricci_eq_of_local_isometry D hV (he.mono hVU) hmetric hy _ _
  have hnorm (w : EuclideanSpace ℝ (Fin n)) : gE.tangentNorm x w ≤ Real.sqrt b * ‖w‖ := by
    have h := Real.sqrt_le_sqrt (hupper w)
    rw [Real.sqrt_mul hb, Real.sqrt_sq (norm_nonneg w)] at h
    change Real.sqrt (gE.euclideanCoefficients x w w) ≤ _
    rw [heq x hxV]
    exact h
  have hell (w : EuclideanSpace ℝ (Fin n)) : a * ‖w‖ ^ 2 ≤ gE.euclideanCoefficients x w w := by
    rw [heq x hxV]
    exact hlower w
  have hnormB : ‖gE.euclideanCoefficients x‖ ≤ b := by
    apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
    · exact gE.symm x
    · intro v
      have hn : 0 ≤ gE.euclideanCoefficients x v v := (mul_nonneg ha.le (sq_nonneg _)).trans
        (hell v)
      rw [abs_of_nonneg hn, heq x hxV]
      exact hupper v
  have hcurvE (m : ℕ) : DE.curvatureDerivativeNorm m x = D.curvatureDerivativeNorm m (e x) :=
    DE.curvatureDerivativeNorm_eq_pullback D hV (he.mono hVU)
      (fun y hy => hi y (hVU hy)) hmetric m hxV
  have h := hbound gE DE x hnormB hell hnorm
    (fun s hs => by rw [hcurvE]; exact hcurv s hs)
    (fun j hj hjq => by rw [(hB.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]; exact hjets j hj hjq) p r
  rw [(hRic.iteratedFDeriv (𝕜 := ℝ) (q + 1)).eq_of_nhds,
    (hB.iteratedFDeriv (𝕜 := ℝ) (q + 1)).eq_of_nhds] at h
  exact h

end PoincareConjecture.SpacetimeBounds
