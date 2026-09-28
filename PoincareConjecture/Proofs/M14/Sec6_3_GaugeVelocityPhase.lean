import PoincareConjecture.Proofs.M14.Sec6_3_InteriorEuler
import PoincareConjecture.Proofs.M14.Sec6_3_EulerGaugeResidual
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)

theorem squareRootEuler_gauge_velocityPhase
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
    {a c : ℝ} (hac : a < c) (hsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
    (hrec : ∀ r ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β r) = R.curve r)
    (hclock : ∀ r ∈ Icc a c, (β r).1.val = T - r ^ 2)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo a c)
    (heuler : ∀ Z : G.Horizontal (R.curve s), M14SquareRootEulerResidual G R E s Z = 0) :
    let q := fun r => (β r).2.val
    HasDerivAt (fun r => (q r, deriv q r))
      (Proofs.M09.regularizedCoordinatePhase
        (M08.chartActionMetric W.flow T x₀) (chartActionScalar W.flow T x₀)
        (s, (q s, deriv q s))) s := by
  let q := fun r => (β r).2.val
  have hsC : s ∈ Icc a c := ⟨hs.1.le, hs.2.le⟩
  have hnear : Icc a c ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have htime (r : ℝ) (hr : r ∈ Icc a c) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr]
    exact (β r).1.property
  have htarget : q s ∈ (extChartAt (𝓡 n) x₀).target := by
    have hval : extChartAt (𝓡 n) x₀ (β s).2 = q s := by
      rw [extChartAt_coe]
      rfl
    rw [← hval]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  have hacc := closedChartEulerCurve_velocityPhase W.flow T x₀ hM04 htime hsC hnear
    q htarget (fun w => by
      let Z := horizontalFieldOfGauge b hrec (fun _ => w) s
      have hres := squareRootEulerResidual_gauge R b hCoordinates hscalar W hM04 x₀
        hac hsub hβ hrec hclock E hsC w
        (horizontalFieldOfGauge_heq b hrec (fun _ => w) hsC)
      exact hres.symm.trans (heuler Z))
  have hq : ContDiffOn ℝ ∞ q (Icc a c) := gaugeLift_spatialCurve_contDiffOn b hβ
  have hqd := ((hq.contDiffAt hnear).differentiableAt (by simp)).hasDerivAt
  have hqdd := ((((hq.mono Ioo_subset_Icc_self).deriv_of_isOpen isOpen_Ioo
    (m := ∞) (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt
      (by simp)).hasDerivAt
  rw [hacc] at hqdd
  exact hqd.prodMk hqdd

end PoincareConjecture.M14
