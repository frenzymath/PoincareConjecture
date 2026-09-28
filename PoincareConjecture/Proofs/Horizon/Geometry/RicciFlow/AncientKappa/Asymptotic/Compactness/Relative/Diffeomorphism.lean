import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.InverseLimit







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

theorem exists_relative_diffeomorph
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    (hmetric : ∀ k, (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0) :
    letI := (L.limitFlow.metricAt 0).toMetricSpace
    letI := (G.limitFlow.metricAt 0).toMetricSpace
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ e : Diffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier L.limitCarrier.carrier ∞,
        Isometry e ∧
        (∀ Q : Set G.limitCarrier.carrier, IsCompact Q →
          TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
            (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) e atTop Q) ∧
        (∀ Q : Set L.limitCarrier.carrier, IsCompact Q →
          TendstoUniformlyOn (fun k y ↦ ((G.embedding (σ k)).inverse
            (0, ((L.embedding (σ k)).toFun (0, y)).2)).2) e.symm atTop Q) := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  obtain ⟨σ, hσ, e, hconv⟩ := exists_relative_isometryEquiv C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hmetric
  have hinv := tendstoUniformlyOn_inverse_relative_limit C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hσ e hconv
  have he := contMDiff_relative_limit C F H G L hGtime hLtime hGcomplete hLcomplete
    hsource hmetric hσ e e.continuous hconv
  have hei := contMDiff_relative_limit C H F L G hLtime hGtime hLcomplete hGcomplete
    (fun k r ↦ (hsource k r).symm) (fun k ↦ (hmetric k).symm) hσ
    e.symm e.symm.continuous hinv
  let E : Diffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier L.limitCarrier.carrier ∞ :=
    ⟨e.toEquiv, he, hei⟩
  exact ⟨σ, hσ, E, e.isometry, hconv, hinv⟩

end PoincareConjecture.PointedGeometricConvergence
