import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Exponential









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem mfderiv_globalGeodesic_zero (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (g.globalGeodesic hc p v) 0 1 = v := by
  obtain ⟨hγ, hzero, hvel⟩ := g.globalGeodesic_spec hc p v
  have hchart := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞)
    (mem_chart_source _ p)).mdifferentiableAt (by simp)
  have hcomp := congrArg (fun L => L 1)
    (mfderiv_comp_of_eq hchart ((hγ.contMDiffAt (mem_univ 0)).mdifferentiableAt
      (by simp)) hzero)
  rw [mfderiv_eq_fderiv] at hcomp
  change deriv (fun t => extChartAt (𝓡 n) p (g.globalGeodesic hc p v t)) 0 = _ at hcomp
  rw [hvel.deriv] at hcomp
  change v = (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p)
    (g.globalGeodesic hc p v 0))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (g.globalGeodesic hc p v) 0 1) at hcomp
  have hreplace := congrArg (fun y : M =>
    (show EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) from
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) y)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (g.globalGeodesic hc p v) 0 1)) hzero
  have hid := congrArg (fun L => L
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (g.globalGeodesic hc p v) 0 1))
    (mfderiv_extChartAt_self (I := 𝓡 n) (x := p))
  exact (hcomp.trans (hreplace.trans hid)).symm


theorem hasDerivAt_globalGeodesic_in_chart (g : RiemannianMetric n M)
    (hc : MetricComplete g) (a : M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) a).target)
    (v : EuclideanSpace ℝ (Fin n)) :
    let c := extChartAt (𝓡 n) a
    let γ := g.globalGeodesic hc (c.symm x) (mfderiv (𝓡 n) (𝓡 n) c.symm x v)
    HasDerivAt (fun t => c (γ t)) v 0 := by
  dsimp only
  let c := extChartAt (𝓡 n) a
  let w := mfderiv (𝓡 n) (𝓡 n) c.symm x v
  let γ := g.globalGeodesic hc (c.symm x) w
  obtain ⟨hγ, hzero, _⟩ := g.globalGeodesic_spec hc (c.symm x) w
  change γ 0 = c.symm x at hzero
  have hp : γ 0 ∈ c.source := by rw [hzero]; exact c.map_target hx
  have hd := (hγ.hasDerivAt_chart_at (mem_univ 0) a hp).1
  have hchart : MDifferentiableAt (𝓡 n) (𝓡 n) c (c.symm x) :=
    mdifferentiableAt_extChartAt (I := 𝓡 n)
      (by simpa only [c, extChartAt_source] using c.map_target hx)
  have hcomp := congrArg (fun L => L 1)
    (mfderiv_comp_of_eq hchart ((hγ.contMDiffAt (mem_univ 0)).mdifferentiableAt
      (by simp)) hzero)
  rw [mfderiv_eq_fderiv] at hcomp
  change deriv (fun t => c (γ t)) 0 = _ at hcomp
  change deriv (fun t => c (γ t)) 0 =
    (mfderiv (𝓡 n) (𝓡 n) c (γ 0))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at hcomp
  have hu : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = w :=
    g.mfderiv_globalGeodesic_zero hc (c.symm x) w
  rw [hu] at hcomp
  have hreplace := congrArg (fun y : M =>
    (show EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) from
      mfderiv (𝓡 n) (𝓡 n) c y) w) hzero
  have hinv := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓡 n) hx
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hinv
  have hinv' := congrArg (fun L => L v) hinv
  exact hd.congr_deriv (hcomp.trans (hreplace.trans hinv'))



noncomputable def chartGlobalExponential (g : RiemannianMetric n M)
    (hc : MetricComplete g) (a : M)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : M :=
  let c := extChartAt (𝓡 n) a
  g.globalExponential hc (c.symm z.1) (mfderiv (𝓡 n) (𝓡 n) c.symm z.1 z.2)



theorem contMDiffAt_chartGlobalExponential (g : RiemannianMetric n M)
    (hc : MetricComplete g) (a : M)
    {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hz : z.1 ∈ (extChartAt (𝓡 n) a).target) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (𝓡 n) ∞ (g.chartGlobalExponential hc a) z := by
  let c := extChartAt (𝓡 n) a
  let Γ := fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    g.globalGeodesic hc (c.symm y.1) (mfderiv (𝓡 n) (𝓡 n) c.symm y.1 y.2)
  have hgeo : ∀ᶠ y in 𝓝 z, g.IsGeodesicOn (Γ y) univ :=
    Eventually.of_forall fun y => (g.globalGeodesic_spec hc _ _).1
  have hzero (y) : Γ y 0 = c.symm y.1 := (g.globalGeodesic_spec hc _ _).2.1
  have hbase : ContMDiffAt
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (𝓡 n) ∞ (fun y => Γ y 0) z := by
    have hsymm := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) a).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds hz)
    have hcomp := hsymm.comp z (contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst)
    exact hcomp.congr_of_eventuallyEq (Eventually.of_forall hzero)
  have hvel : ContDiffAt ℝ ∞ (fun y => deriv (fun t => c (Γ y t)) 0) z := by
    apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds hz)] with y hy
    exact (g.hasDerivAt_globalGeodesic_in_chart hc a hy y.2).deriv
  have hvel' := contDiffAt_chart_velocity_transition hgeo (mem_univ (0 : ℝ)) hbase
    a (Γ z 0) (by rw [hzero]; exact c.map_target hz) (mem_extChartAt_source (Γ z 0)) hvel
  exact contMDiffAt_geodesic_endpoint hgeo convex_univ (mem_univ (0 : ℝ))
    (mem_univ (1 : ℝ)) hbase hvel'

end PoincareConjecture.RiemannianMetric
