import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.CompatibleSquareCurve
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.OrdinaryLiftedPath
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Path.RegularizedAction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.LGeometry.Path.RegularizedAction

/-!
# The actual square-root path in the retained ordinary product

The ordinary smooth representative is lifted at the actual physical
clock. The horizontal velocity agrees with the backward path in the
interior, and the full within derivative holds at both endpoints.
Source: Morgan-Tian Proposition 12.13, pp. 304-306; section 4 of
`proof-work/tasks/M34/derivations/ordinary-square-survival.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}

/-- The square-time clock remains in the actual ordinary flow domain,
including its closed parameter endpoints (Proposition 12.13). -/
theorem ordinarySquarePath_clockMem {T tau : ℝ} (q : BackwardTimePath F T 0 tau)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval 0 tau) : T - s ^ 2 ∈ I.domain := by
  have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
  have hsq := (sq_le_sq₀ hs0 (Real.sqrt_nonneg tau)).mpr hs.2
  rw [Real.sq_sqrt q.ordered.le] at hsq
  exact q.time_mem (s ^ 2) ⟨sq_nonneg s, hsq⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every actual ordinary square-root representative lifts to the exact
M14 square-root path record, retaining its endpoint derivative data
(Proposition 12.13, pp. 304-306). -/
noncomputable def ordinarySquarePath
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T tau : ℝ} (q : BackwardTimePath F T 0 tau) (A : SqrtRegularPath q) :
    M14SquareRootPath (ordinaryProductLGeometry R hRicci) (ordinaryLiftedPath R hRicci q) where
  curve := compatibleSquareCurve R.product.productCylinder T A.curve
  domain := sqrtParameterInterval 0 tau
  interval_subset := Subset.rfl
  smooth := compatibleSquareCurve_smooth R.product.productCylinder T
    (fun _ hs => ordinarySquarePath_clockMem q hs) (A.smooth.mono A.interval_subset)
  agrees := by
    intro s hs
    change R.product.productCylinder.toSpacetime
      ((R.product.timeIntervals.interval I).realParam (T - s ^ 2), A.curve s) =
      R.product.productCylinder.toSpacetime
        ((R.product.timeIntervals.interval I).realParam (T - s ^ 2), q.curve (s ^ 2))
    rw [A.agrees s hs]
  curve_time := fun _ hs => compatibleSquareCurve_time R.product.productCylinder T A.curve
    (ordinarySquarePath_clockMem q hs)
  horizontal_velocity := compatibleSquareHorizontal R.product.productCylinder
    R.product.productMetric T A.curve
  horizontal_agrees := by
    intro s hs
    have hcast (z w : R.product.spacetime.Point) (h : z = w)
        (v : R.product.spacetime.Horizontal w) :
        ((h.symm ▸ v) : R.product.spacetime.Horizontal z).val = v.val := by
      cases h
      rfl
    apply Subtype.ext
    rw [hcast]
    · change (R.product.productMetric.spatialTangentEquiv
        ((R.product.timeIntervals.interval I).realParam (T - s ^ 2)) (A.curve s)
        (curveVelocity A.curve s)).val =
        ((2 * s) • R.product.productMetric.spatialTangentEquiv
          ((R.product.timeIntervals.interval I).realParam (T - s ^ 2)) (q.curve (s ^ 2))
          (curveVelocity q.curve (s ^ 2))).val
      rw [PoincareMT.M08.sqrtRegularPath_velocity A hs, map_smul,
        A.agrees s ⟨hs.1.le, hs.2.le⟩]
    · change R.product.productCylinder.toSpacetime
        ((R.product.timeIntervals.interval I).realParam (T - s ^ 2), A.curve s) =
        R.product.productCylinder.toSpacetime
          ((R.product.timeIntervals.interval I).realParam (T - s ^ 2), q.curve (s ^ 2))
      rw [A.agrees s ⟨hs.1.le, hs.2.le⟩]
  derivative_eq := by
    intro s hs
    have hK : UniqueDiffOn ℝ (sqrtParameterInterval 0 tau) := by
      simpa only [sqrtParameterInterval, Real.sqrt_zero] using
        (uniqueDiffOn_Icc (Real.sqrt_pos.mpr q.ordered))
    exact compatibleSquareCurve_derivative R.product.productCylinder R.product.productMetric T
      (fun _ hr => ordinarySquarePath_clockMem q hr) hs (hK s hs)
      ((A.smooth.contMDiffAt (A.open_domain.mem_nhds (A.interval_subset hs))).mdifferentiableAt
        (by simp))

end PoincareMT.M34
