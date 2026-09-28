import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Relative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem relativeCoordinateMap_pullback_at_time
    {n : ℕ} {C : FlowCarrier.{0} n} {a b c d : ℝ}
    {F : ℕ → BasedFlow n a b C} {H : ℕ → BasedFlow n c d C}
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier) (k : ℕ)
    (hGzero : a < 0 ∧ 0 < b) (hLzero : c < 0 ∧ 0 < d)
    (t : ℝ) (hGt : t ∈ Ioo a b) (hLt : t ∈ Ioo c d)
    (hmetric : (F (G.subsequence k)).metricAt t = (H (L.subsequence k)).metricAt t)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hsmooth : ContDiffOn ℝ ∞ (G.relativeCoordinateMap L qG qL k) U)
    (hrel : ∀ y ∈ U,
      let x := (extChartAt (𝓡 n) qG).symm y
      let z := ((L.embedding k).inverse (0, ((G.embedding k).toFun (0, x)).2)).2
      x ∈ G.exhaustion k ∧ z ∈ L.exhaustion k ∧
        z ∈ (extChartAt (𝓡 n) qL).source ∧
        ((L.embedding k).toFun (0, z)).2 = ((G.embedding k).toFun (0, x)).2) :
    ∀ y ∈ U, ∀ v w,
      L.pulledChartCoefficients qL k t (G.relativeCoordinateMap L qG qL k y)
        (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y v)
        (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y w) =
      G.pulledChartCoefficients qG k t y v w := by
  intro y hy v w
  let f := fun x ↦ ((L.embedding k).inverse (0, ((G.embedding k).toFun (0, x)).2)).2
  let cg := extChartAt (𝓡 n) qG
  let cl := extChartAt (𝓡 n) qL
  let p := fun z ↦ ((G.embedding k).toFun (t, cg.symm z)).2
  let q := fun z ↦ ((L.embedding k).toFun (t, cl.symm z)).2
  have hchart : cl.symm (G.relativeCoordinateMap L qG qL k y) = f (cg.symm y) :=
    cl.left_inv (hrel y hy).2.2.1
  have hq : MDifferentiableAt (𝓡 n) (𝓡 n) q
      (G.relativeCoordinateMap L qG qL k y) := by
    have hc := (contMDiffOn_extChartAt_symm (n := ∞) qL).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) qL).mem_nhds
        (cl.map_source (hrel y hy).2.2.1))
    have he := (L.embedding k).spatialMap_contMDiffAt (L.exhaustion_open k) hLt
      (hrel y hy).2.1
    change ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun x ↦ ((L.embedding k).toFun (t, x)).2) (f (cg.symm y)) at he
    rw [← hchart] at he
    exact (he.comp _ hc).mdifferentiableAt (by simp)
  have heq : q ∘ G.relativeCoordinateMap L qG qL k =ᶠ[𝓝 y] p := by
    filter_upwards [hU.mem_nhds hy] with z hz
    change ((L.embedding k).toFun (t, cl.symm (cl (f (cg.symm z))))).2 = _
    rw [cl.left_inv (hrel z hz).2.2.1]
    exact ((L.embedding k).spatial_eq_of_mem hLt hLzero (hrel z hz).2.1).trans
      ((hrel z hz).2.2.2.trans
        ((G.embedding k).spatial_eq_of_mem hGzero hGt (hrel z hz).1))
  have hid := ((H (L.subsequence k)).metricAt t).pullbackCoefficients_comp_of_eventuallyEq
    hq ((hsmooth.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) heq v w
  change ((H (L.subsequence k)).metricAt t).pullbackCoefficients q
      (G.relativeCoordinateMap L qG qL k y)
      (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y v)
      (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y w) =
    ((F (G.subsequence k)).metricAt t).pullbackCoefficients p y v w
  rw [hmetric]
  exact hid

end PoincareConjecture.PointedGeometricConvergence
