import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Geodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.ChangeCoordinates








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem IsGeodesicOn.hasDerivAt_in_chart
    {g : RiemannianMetric n M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hs : IsOpen s) (p : M)
    (hp : MapsTo γ s (extChartAt (𝓡 n) p).source) :
    let q := fun t => extChartAt (𝓡 n) p (γ t)
    ∀ t ∈ s, HasDerivAt q (deriv q t) t ∧
      HasDerivAt (deriv q)
        (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (q t) (deriv q t) (deriv q t)) t := by
  dsimp only
  let Q := fun t => extChartAt (𝓡 n) p (γ t)
  intro t ht
  obtain ⟨r, q, w, hlocal⟩ := hγ t ht
  let f := fun y => extChartAt (𝓡 n) p ((extChartAt (𝓡 n) r).symm y)
  have heq : Q =ᶠ[𝓝 t] (fun u => f (q u)) := by
    filter_upwards [hlocal] with u hu
    exact congrArg (extChartAt (𝓡 n) p) hu.1
  have htransport : ∀ᶠ u in 𝓝 t,
      HasDerivAt (fun v => f (q v)) (fderiv ℝ f (q u) (w u)) u ∧
      HasDerivAt (fun v => fderiv ℝ f (q v) (w v))
        (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (f (q u)) (fderiv ℝ f (q u) (w u)) (fderiv ℝ f (q u) (w u))) u := by
    filter_upwards [hlocal, hs.mem_nhds ht] with u hu hus
    exact g.hasDerivAt_chart_geodesic_change_coordinates r p hu.2.1
      (hu.1 ▸ hp hus) hu.2.2.1 hu.2.2.2
  have hQ : ∀ᶠ u in 𝓝 t, HasDerivAt Q (fderiv ℝ f (q u) (w u)) u := by
    filter_upwards [htransport, eventually_eventually_nhds.mpr heq] with u hu hueq
    exact hu.1.congr_of_eventuallyEq hueq
  have hvelocity : deriv Q =ᶠ[𝓝 t] (fun u => fderiv ℝ f (q u) (w u)) :=
    hQ.mono fun _ hu => hu.deriv
  refine ⟨hQ.self_of_nhds.differentiableAt.hasDerivAt, ?_⟩
  have hW := htransport.self_of_nhds.2.congr_of_eventuallyEq hvelocity
  have hqt := heq.self_of_nhds
  have hwt := hvelocity.self_of_nhds
  simpa only [Q, hqt, hwt] using hW

end PoincareConjecture.RiemannianMetric
