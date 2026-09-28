import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Maps







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

noncomputable def relativeCoordinateMap
    {n : ℕ} {C : FlowCarrier.{0} n} {a b c d : ℝ}
    {F : ℕ → BasedFlow n a b C} {H : ℕ → BasedFlow n c d C}
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y ↦ extChartAt (𝓡 n) qL
    (((L.embedding k).inverse
      (0, ((G.embedding k).toFun (0, (extChartAt (𝓡 n) qG).symm y)).2)).2)

theorem relativeCoordinateMap_smooth_pullback_on
    {n : ℕ} {C : FlowCarrier.{0} n} {a b c d : ℝ}
    {F : ℕ → BasedFlow n a b C} {H : ℕ → BasedFlow n c d C}
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier) (k : ℕ)
    (hLtime : c < 0 ∧ 0 < d)
    (hmetric : (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hUc : U ⊆ (extChartAt (𝓡 n) qG).target)
    (hrel : ∀ y ∈ U,
      let f := fun x ↦ ((L.embedding k).inverse
        (0, ((G.embedding k).toFun (0, x)).2)).2
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ f ((extChartAt (𝓡 n) qG).symm y) ∧
      f ((extChartAt (𝓡 n) qG).symm y) ∈ L.exhaustion k ∧
      f ((extChartAt (𝓡 n) qG).symm y) ∈ (extChartAt (𝓡 n) qL).source ∧
      ((L.embedding k).toFun (0, f ((extChartAt (𝓡 n) qG).symm y))).2 =
        ((G.embedding k).toFun (0, (extChartAt (𝓡 n) qG).symm y)).2) :
    ContDiffOn ℝ ∞ (G.relativeCoordinateMap L qG qL k) U ∧
      ∀ y ∈ U, ∀ v w,
        L.pulledChartCoefficients qL k 0 (G.relativeCoordinateMap L qG qL k y)
          (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y v)
          (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y w) =
        G.pulledChartCoefficients qG k 0 y v w := by
  let f := fun x ↦ ((L.embedding k).inverse
    (0, ((G.embedding k).toFun (0, x)).2)).2
  let cg := extChartAt (𝓡 n) qG
  let cl := extChartAt (𝓡 n) qL
  have hsmooth (y) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ (G.relativeCoordinateMap L qG qL k) y := by
    have hc := (contMDiffOn_extChartAt_symm (n := ∞) qG).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) qG).mem_nhds (hUc hy))
    have hl := (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := qL)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source (I := 𝓡 n) qL).mem_nhds (hrel y hy).2.2.1)
    exact contMDiffAt_iff_contDiffAt.mp (hl.comp y ((hrel y hy).1.comp y hc))
  refine ⟨fun y hy ↦ (hsmooth y hy).contDiffWithinAt, ?_⟩
  intro y hy v w
  let p := fun z ↦ ((G.embedding k).toFun (0, cg.symm z)).2
  let q := fun z ↦ ((L.embedding k).toFun (0, cl.symm z)).2
  have hchart : cl.symm (G.relativeCoordinateMap L qG qL k y) = f (cg.symm y) :=
    cl.left_inv (hrel y hy).2.2.1
  have hq : MDifferentiableAt (𝓡 n) (𝓡 n) q
      (G.relativeCoordinateMap L qG qL k y) := by
    have hc := (contMDiffOn_extChartAt_symm (n := ∞) qL).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) qL).mem_nhds
        (cl.map_source (hrel y hy).2.2.1))
    have he := (L.embedding k).spatialMap_contMDiffAt (L.exhaustion_open k) hLtime
      (hrel y hy).2.1
    change ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun x ↦ ((L.embedding k).toFun (0, x)).2) (f (cg.symm y)) at he
    rw [← hchart] at he
    exact (he.comp _ hc).mdifferentiableAt (by simp)
  have heq : q ∘ G.relativeCoordinateMap L qG qL k =ᶠ[𝓝 y] p := by
    filter_upwards [hU.mem_nhds hy] with z hz
    change ((L.embedding k).toFun (0, cl.symm (cl (f (cg.symm z))))).2 = _
    rw [cl.left_inv (hrel z hz).2.2.1]
    exact (hrel z hz).2.2.2
  have hid := ((H (L.subsequence k)).metricAt 0).pullbackCoefficients_comp_of_eventuallyEq
    hq ((hsmooth y hy).differentiableAt (by simp)) heq v w
  change ((H (L.subsequence k)).metricAt 0).pullbackCoefficients q
      (G.relativeCoordinateMap L qG qL k y)
      (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y v)
      (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y w) =
    ((F (G.subsequence k)).metricAt 0).pullbackCoefficients p y v w
  rw [hmetric]
  exact hid

theorem eventually_relativeCoordinateMap_smooth_pullback_on
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    (hmetric : ∀ k, (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hUc : U ⊆ (extChartAt (𝓡 n) qG).target)
    {r : ℝ} (hr : 0 < r)
    (hUr : MapsTo (extChartAt (𝓡 n) qG).symm U (G.limitFlow.ballAt 0 r))
    (htarget : ∀ᶠ k in atTop, ∀ y ∈ U,
      ((L.embedding k).inverse
        (0, ((G.embedding k).toFun (0, (extChartAt (𝓡 n) qG).symm y)).2)).2 ∈
        (extChartAt (𝓡 n) qL).source) :
    ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (G.relativeCoordinateMap L qG qL k) U ∧
      ∀ y ∈ U, ∀ v w,
        L.pulledChartCoefficients qL k 0 (G.relativeCoordinateMap L qG qL k y)
          (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y v)
          (fderiv ℝ (G.relativeCoordinateMap L qG qL k) y w) =
        G.pulledChartCoefficients qG k 0 y v w := by
  obtain ⟨j, hj⟩ := L.exists_exhaustion_superset
    ((L.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hLcomplete
      L.limitFlow.base (4 * r))
  filter_upwards [eventually_relative_map_smooth C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hr, eventually_ge_atTop j, htarget]
    with k hk hjk hkt
  apply G.relativeCoordinateMap_smooth_pullback_on L qG qL k hLtime (hmetric k) hU hUc
  intro y hy
  exact ⟨hk.2.1 _ (hUr hy),
    L.exhaustion_monotone hjk (hj (subset_closure (hk.1 (hUr hy)))),
    hkt y hy, hk.2.2 _ (hUr hy)⟩

end PoincareConjecture.PointedGeometricConvergence
