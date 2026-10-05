import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Raw.FamilyAssembly
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Periodic.Boundary
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.CircleLift
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Profile.Primitive
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.NullLoopHomotopy

/-!
# The flattening circle relabeling

The closed M63 flattening homeomorphism induces the explicit M60 circle
reparameterization needed to identify a polygon boundary with its flattened
C1 loop.  This file only constructs the boundary relabeling; null fillings
and annuli remain separate M64 data.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareMT

/-- The fixed angular period is nonzero. Source: Auxiliary step for MT Definition 19.18 and
Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_curvePeriod_ne : curvePeriod ≠ 0 := by
  dsimp [curvePeriod]
  positivity

/-- Identify the quotient angle circle with the contract's unit-circle model. Source:
Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
noncomputable def m64AngleLoopCircle : AddCircle curvePeriod ≃ₜ LoopCircle := by
  exact (AddCircle.homeomorphCircle m64_curvePeriod_ne).trans
    m60LoopCircleHomeomorphCircle.symm

/-- The quotient-angle identification agrees with the literal angular circle parameter.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64AngleLoopCircle_apply (x : ℝ) :
    m64AngleLoopCircle (x : AddCircle curvePeriod) = m64LoopCircleParam x := by
  change m60LoopCircleHomeomorphCircle.symm (AddCircle.homeomorphCircle
    m64_curvePeriod_ne (x : AddCircle curvePeriod)) = m64LoopCircleParam x
  apply m60LoopCircleHomeomorphCircle.injective
  rw [m60LoopCircleHomeomorphCircle.apply_symm_apply]
  change (AddCircle.homeomorphCircle m64_curvePeriod_ne) (x : AddCircle curvePeriod) =
    m60LoopCircleHomeomorphCircle
      ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩
  rw [m60LoopCircleHomeomorphCircle_angular]
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  simp [curvePeriod]

/-- The strictly monotone periodic flattening lift descends to a circle homeomorphism.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
noncomputable def m64FlatteningCircleHomeomorph
    (N : ℕ) (hN : 0 < N) : LoopCircle ≃ₜ LoopCircle := by
  classical
  let e : AddCircle curvePeriod ≃ₜ AddCircle curvePeriod :=
    Classical.choose (m63Flattening_circle_homeomorph hN)
  have he : ∀ x : ℝ, e (x : AddCircle curvePeriod) =
      (m63Flattening N x : AddCircle curvePeriod) :=
    Classical.choose_spec (m63Flattening_circle_homeomorph hN)
  let h : LoopCircle ≃ₜ LoopCircle :=
    m64AngleLoopCircle.symm.trans (e.symm.trans m64AngleLoopCircle)
  exact h

/-- Circle reparameterization induced by the M63 flattening homeomorphism. Source: Auxiliary
step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
noncomputable def m64CircleReparamFromFlattening
    (N : ℕ) (hN : 0 < N) : CircleReparameterization := {
  map := m64FlatteningCircleHomeomorph N hN
  inverse := (m64FlatteningCircleHomeomorph N hN).symm
  left_inverse := (m64FlatteningCircleHomeomorph N hN).left_inv
  right_inverse := (m64FlatteningCircleHomeomorph N hN).right_inv
  continuous_map := (m64FlatteningCircleHomeomorph N hN).continuous
  continuous_inverse := (m64FlatteningCircleHomeomorph N hN).symm.continuous }

/-- The inverse flattening circle reparameterization inverts the flattened angular
parameter. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64CircleReparamFromFlattening_apply
    (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (m64CircleReparamFromFlattening N hN).map
        (m64LoopCircleParam (m63Flattening N x)) =
      m64LoopCircleParam x := by
  classical
  let e : AddCircle curvePeriod ≃ₜ AddCircle curvePeriod :=
    Classical.choose (m63Flattening_circle_homeomorph hN)
  have he : ∀ x : ℝ, e (x : AddCircle curvePeriod) =
      (m63Flattening N x : AddCircle curvePeriod) :=
    Classical.choose_spec (m63Flattening_circle_homeomorph hN)
  change (m64FlatteningCircleHomeomorph N hN)
      (m64LoopCircleParam (m63Flattening N x)) = m64LoopCircleParam x
  let h : LoopCircle ≃ₜ LoopCircle :=
    m64AngleLoopCircle.symm.trans (e.symm.trans m64AngleLoopCircle)
  change h (m64LoopCircleParam (m63Flattening N x)) = m64LoopCircleParam x
  rw [← m64AngleLoopCircle_apply x, ← m64AngleLoopCircle_apply (m63Flattening N x)]
  dsimp [h]
  rw [m64AngleLoopCircle.symm_apply_apply, ← he, e.symm_apply_apply]

/-- The actual raw polygon boundary is the flattened family composed with the inverse
relabeling. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_polygon_boundary_eq_flattened_family
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N)
    {polygon : M63GeodesicPolygon g D N}
    {boundary : M64PolygonBoundary polygon}
    {family : C1FreeLoopSpace (M := M)}
    (hfamily : ∀ x, periodicFreeLoop family x = m63FlattenedPolygon polygon x) :
    ∀ w : LoopCircle,
      boundary.map w = family ((m64CircleReparamFromFlattening N hN).map w) := by
  classical
  intro w
  let e : AddCircle curvePeriod ≃ₜ AddCircle curvePeriod :=
    Classical.choose (m63Flattening_circle_homeomorph hN)
  have he : ∀ x : ℝ, e (x : AddCircle curvePeriod) =
      (m63Flattening N x : AddCircle curvePeriod) :=
    Classical.choose_spec (m63Flattening_circle_homeomorph hN)
  obtain ⟨x, hx, hwx⟩ := Proofs.M58.exists_angularPoint w
  let y : AddCircle curvePeriod := e.symm (x : AddCircle curvePeriod)
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective y
  have hflat : (m63Flattening N v : AddCircle curvePeriod) =
      (x : AddCircle curvePeriod) := by
    rw [← he v, hv, e.apply_symm_apply]
  have hparam : m64LoopCircleParam (m63Flattening N v) = w := by
    have hangle := congrArg m64AngleLoopCircle hflat
    rw [m64AngleLoopCircle_apply (m63Flattening N v),
      m64AngleLoopCircle_apply x] at hangle
    exact hangle.trans (by
      apply Subtype.ext
      simpa [m64LoopCircleParam, Proofs.M58.angularPoint] using hwx)
  rw [← hparam, boundary.angular_eq]
  rw [m64CircleReparamFromFlattening_apply N hN v]
  have hboundary : periodicFreeLoop family v =
      family (m64LoopCircleParam v) := by
    change family.extension (m64LoopCircleParam v).1 =
      family.toFun (m64LoopCircleParam v)
    exact family.boundary _
  rw [← hboundary, hfamily v]
  rfl

/-- Retain the exact inverse circle reparameterization for every member of the M63 family.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_raw_boundary_reparam_of_M63
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta : ℝ} (A : M63RawApproximation F Gamma zeta) :
    ∀ z : LoopTwoSphere, ∃ boundary : M64PolygonBoundary (A.polygon z),
      ∃ r : CircleReparameterization, ∀ w : LoopCircle,
        boundary.map w = (A.family z) (r.map w) := by
  intro z
  obtain ⟨boundary⟩ := exists_polygon_boundary (A.polygon z)
  refine ⟨boundary, m64CircleReparamFromFlattening A.count A.count_positive, ?_⟩
  exact m64_polygon_boundary_eq_flattened_family A.count_positive
    (A.angular_eq z)

/-- Precompose a continuous null extension to transport nullity under the boundary
relabeling. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64RawNullLoop_of_boundary_reparam
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {family : C1FreeLoopSpace (M := M)}
    (hfamily : IsNullHomotopicLoop family)
    (reparam : CircleReparameterization)
    {boundary : ContinuousMap LoopCircle M}
    (hboundary : ∀ w : LoopCircle,
      boundary w = family (reparam.map w)) :
    M64RawNullLoop boundary := by
  have hsphere : Metric.sphere (0 : LoopPlane) 1 = {z : LoopPlane | ‖z‖ = 1} := by
    ext z
    simp only [Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq]
  let e : Metric.sphere (0 : LoopPlane) 1 ≃ₜ LoopCircle :=
    Homeomorph.setCongr hsphere
  let rSphere : C(Metric.sphere (0 : LoopPlane) 1, Metric.sphere (0 : LoopPlane) 1) := {
    toFun := fun z => e.symm (reparam.map (e z))
    continuous_toFun := e.symm.continuous.comp
      (reparam.continuous_map.comp e.continuous) }
  have hnullSphere : (m59LoopSphereMap family).Nullhomotopic :=
    (m59NullLoop_iff_sphereMap_nullhomotopic family).mp hfamily
  obtain ⟨extension, hextension⟩ := Proofs.M59.exists_extension_of_sphere_nullhomotopic
    ((m59LoopSphereMap family).comp rSphere) (hnullSphere.comp_left rSphere)
  refine ⟨extension, extension.continuous, ?_⟩
  intro z
  let zs : Metric.sphere (0 : LoopPlane) 1 :=
    ⟨z.val, by simpa [Metric.mem_sphere, dist_zero_right] using z.property⟩
  have he : e zs = z := by
    apply Subtype.ext
    rfl
  have hres := hextension zs
  rw [hboundary z]
  change extension z.val = family (reparam.map z)
  rw [hres]
  dsimp [ContinuousMap.comp, m59LoopSphereMap, rSphere, zs]
  rw [he]
  rfl

end PoincareMT
