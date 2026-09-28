import PoincareConjecture.Proofs.M09.GeometryAssembly
import PoincareConjecture.Proofs.M09.FixedTimeDensity





set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
  [SecondCountableTopology M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialGeometry_regular_locus {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M)
    (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) (hτ : 0 < τ) (hmax : τ < τmax) :
    ∃ U : Set M, IsOpen U ∧ Dense U ∧ Set.Nonempty U ∧
      ∀ q ∈ U, Nonempty (ReducedLengthRegularPoint F T τmax p q τ) := by
  let U : Set M := (fun q : M ↦ (q, τ)) ⁻¹' G.regularImage
  have hUopen : IsOpen U := by
    change IsOpen ((fun q : M ↦ (q, τ)) ⁻¹' G.regular_chart.target)
    exact G.regular_chart.open_target.preimage (continuous_id.prodMk continuous_const)
  let S : Set M := {q : M | ∃ Z : TangentSpace (𝓡 n) p,
      (Z, τ) ∈ G.toLExponentialFamily.regularDomain ∧
      G.toLExponentialFamily.gamma Z τ = q}
  have hSdense : Dense S := lExponentialFamily_dense_regular_endpoints F hM04 T τmax hτmax
    hwindow hcurvature hL p G.toLExponentialFamily τ hτ hmax
  have hSU : S ⊆ U := by
    intro q hq
    obtain ⟨Z, hreg, hend⟩ := hq
    have hsrc : (Z, τ) ∈ G.regular_chart.source := by
      rw [G.regular_source]
      exact hreg
    have htarget : G.regular_chart (Z, τ) ∈ G.regular_chart.target :=
      G.regular_chart.map_source hsrc
    change (q, τ) ∈ G.regularImage
    rw [← hend, ← G.regular_forward (Z, τ)]
    exact htarget
  have hUdense : Dense U := hSdense.mono hSU
  have hUnonempty : U.Nonempty := by
    obtain ⟨q, hq⟩ := hSdense.nonempty
    exact ⟨q, hSU hq⟩
  refine ⟨U, hUopen, hUdense, hUnonempty, ?_⟩
  intro q hq
  exact ⟨G.regular_point (q, τ) hq⟩

end PoincareConjecture.Proofs.M09
