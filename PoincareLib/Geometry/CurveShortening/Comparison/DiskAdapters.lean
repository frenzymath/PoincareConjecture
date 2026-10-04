import PoincareLib.Geometry.CurveShortening.Comparison.Annulus

/-!
# Exact C1 and raw-boundary disk transports for M64

The same disk map, entire boundary homeomorphism, Lipschitz constant and
Jacobian integral are retained. Equality of the area ranges is valid even
when the ranges are empty; it makes no geometric existence claim.

Morgan--Tian context: Chapter 19, Sections 19.3-19.7, printed pp. 447-481; the frozen M64
contracts and project comparison erratum specify the final interfaces.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {gamma : C1FreeLoopSpace (M := M)}

/-- Forget the C1 boundary record while preserving every disk field. Source: Auxiliary step
for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
def m64RawDiskOfC1 (D : LipschitzSpanningDisk g gamma) :
    M64RawSpanningDisk g (m64C1Boundary gamma) where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization
  boundary_eq := D.boundary_eq
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

/-- Restore the given C1 boundary record without changing the disk map or requiring any
regularity of its boundary homeomorphism. Source: Auxiliary step for MT Lemma 19.30, p. 462;
the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
def m64C1DiskOfRaw (D : M64RawSpanningDisk g (m64C1Boundary gamma)) :
    LipschitzSpanningDisk g gamma where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization
  boundary_eq := D.boundary_eq
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

/-- These field-preserving transports are inverse, including the retained map and boundary
reparameterization, not just their area values. Source: Auxiliary step for MT Lemma 19.30,
p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
def m64C1RawDiskEquiv :
    LipschitzSpanningDisk g gamma ≃ M64RawSpanningDisk g (m64C1Boundary gamma) where
  toFun := m64RawDiskOfC1
  invFun := m64C1DiskOfRaw
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Forgetting the C1 boundary record preserves the literal disk area. Source: Auxiliary
step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64RawDiskOfC1_area (D : LipschitzSpanningDisk g gamma) :
    (m64RawDiskOfC1 D).area = D.area := rfl

/-- Restoring the C1 boundary record preserves the literal disk area. Source: Auxiliary step
for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64C1DiskOfRaw_area (D : M64RawSpanningDisk g (m64C1Boundary gamma)) :
    (m64C1DiskOfRaw D).area = D.area := rfl

/-- The two admissible classes have exactly the same area range. Source: Auxiliary step for
MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64RawDiskAreaRange_c1 :
    m64RawDiskAreaRange g (m64C1Boundary gamma) =
      Set.range (fun D : LipschitzSpanningDisk g gamma => D.area) := by
  ext area
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨m64C1DiskOfRaw D, hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨m64RawDiskOfC1 D, hD⟩

/-- Equality of the totalized infima; nonemptiness is a separate geometric obligation
whenever these values are used as filling areas. Source: Auxiliary step for MT Lemma 19.30,
p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64RawFillingArea_c1 :
    m64RawFillingArea g (m64C1Boundary gamma) = fillingArea g gamma := by
  unfold m64RawFillingArea fillingArea
  rw [m64RawDiskAreaRange_c1]

end PoincareMT
