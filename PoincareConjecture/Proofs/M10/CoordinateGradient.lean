import PoincareConjecture.Proofs.M10.PreferredMetric
import PoincareConjecture.Proofs.M10.EndpointCoordinates
import PoincareConjecture.Proofs.M10.TerminalGradient
import PoincareConjecture.Proofs.M10.RegularGerms

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem coordinate_terminal_pairing (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (q₀ : M)
    (z : TangentSpace (𝓡 n) p × ℝ)
    (hreg : z ∈ G.toLExponentialFamily.regularDomain)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (v : TangentSpace (𝓡 n) q₀) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ ((fun x ↦ reducedLength F T p x z.2) ∘ (extChartAt (𝓡 n) q₀).symm)
        (endpointCoordinates G q₀ z) v =
      coordinateBackwardMetric F T q₀ (endpointCoordinates G q₀ z, z.2)
        (fderiv ℝ (endpointCoordinates G q₀) z (0, 1)) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  obtain ⟨hτ, hmax, hmin, _⟩ := hreg.1
  have hsrc : z ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have htgt : (G.gamma z.1 z.2, z.2) ∈ G.regularImage := by
    change (G.gamma z.1 z.2, z.2) ∈ G.regular_chart.target
    simpa only [G.regular_forward] using G.regular_chart.map_source hsrc
  have hr := G.regular_point (G.gamma z.1 z.2, z.2) htgt
  have hd := (reducedLength_space_contMDiffAt hr).mdifferentiableAt (by simp)
  have hpair := reducedLength_differential_eq_terminal_pairing hL G z.1 hτ hmax hmin hd
    hreg.2.2 (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v (G.gamma z.1 z.2))
  have hc := preferredField_scalar_derivative q₀ v hq hd
  change fderiv ℝ ((fun x ↦ reducedLength F T p x z.2) ∘ (extChartAt (𝓡 n) q₀).symm)
      (extChartAt (𝓡 n) q₀ (G.gamma z.1 z.2)) v = _
  rw [hc, hpair, endpointCoordinates_time G q₀ z ⟨mem_univ _, hτ, hmax⟩ hq]
  have hchart : G.gamma z.1 z.2 ∈ (extChartAt (𝓡 n) q₀).source := by
    simpa only [extChartAt_source] using hq
  dsimp only [coordinateBackwardMetric, endpointCoordinates]
  rw [(extChartAt (𝓡 n) q₀).left_inv hchart]
  have hmetric := backwardMetricCoordinates_apply (F := F) (T := T) q₀
    (G.gamma z.1 z.2, z.2) hq (curveVelocity (G.gamma z.1) z.2)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v (G.gamma z.1 z.2))
  rw [preferredField_coordinates q₀ v hq] at hmetric
  exact hmetric.symm

end PoincareConjecture.M10
