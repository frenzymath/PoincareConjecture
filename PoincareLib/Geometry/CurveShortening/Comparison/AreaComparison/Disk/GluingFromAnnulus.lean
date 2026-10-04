import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Polar.AnnulusArea
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Disk.BoundaryRegularization
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Collar.Gluing

/-!
# Actual disk gluing across an arbitrary rectangle annulus

The proved polar collar is attached to an exactly parametrized disk. M60
boundary regularization then applies the construction to every supplied
Lipschitz spanning disk with no regularity assumption on its homeomorphism.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {c0 c1 : ℝ → M}

/-- Glue the actual polar collar of a rectangle annulus to an exact-boundary spanning disk.
Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64DiskGluing_of_exact_boundary_annulus
    (A : M64Annulus g c0 c1) (gamma0 gamma1 : C1FreeLoopSpace (M := M))
    (h0 : ∀ x, periodicFreeLoop gamma0 x = c0 x)
    (h1 : ∀ x, periodicFreeLoop gamma1 x = c1 x)
    (D : LipschitzSpanningDisk g gamma0)
    (hD : ∀ z : LoopCircle, D.map z = gamma0 z) :
    ∃ D' : LipschitzSpanningDisk g gamma1, D'.area ≤ D.area + A.area := by
  let H := m64PolarAnnulusMap A.map
  let sigma : CircleReparameterization := {
    map := id
    inverse := id
    left_inverse := fun _ => rfl
    right_inverse := fun _ => rfl
    continuous_map := continuous_id
    continuous_inverse := continuous_id }
  have hmatch (z : LoopPlane) (hz : ‖z‖ = (1 / 2 : ℝ)) :
      D.map ((1 / 2 : ℝ)⁻¹ • z) = H z := by
    let theta := m60PlaneAngle z
    have hpolar : (1 / 2 : ℝ) • Proofs.M58.angularPoint theta = z := by
      simpa only [hz] using m60PlaneAngle_polar z
    have hnorm : (1 / 2 : ℝ)⁻¹ • z = Proofs.M58.angularPoint theta := by
      rw [← hpolar, smul_smul, inv_mul_cancel₀ (by norm_num : (1 / 2 : ℝ) ≠ 0), one_smul]
    let q : LoopCircle := ⟨Proofs.M58.angularPoint theta, Proofs.M58.norm_angularPoint theta⟩
    calc
      _ = D.map (Proofs.M58.angularPoint theta) := congrArg D.map hnorm
      _ = gamma0 q := hD q
      _ = periodicFreeLoop gamma0 theta := (gamma0.boundary q).symm
      _ = c0 theta := h0 theta
      _ = H ((1 / 2 : ℝ) • Proofs.M58.angularPoint theta) :=
        (m64Annulus_polar_traces A theta).1.symm
      _ = H z := congrArg H hpolar
  have hboundary (z : LoopCircle) : H z = gamma1 (sigma.map z) := by
    let theta := m60PlaneAngle z
    have hang : Proofs.M58.angularPoint theta = z.val := by
      simpa only [z.property, one_smul] using m60PlaneAngle_polar z.val
    let q : LoopCircle := ⟨Proofs.M58.angularPoint theta, Proofs.M58.norm_angularPoint theta⟩
    have hq : q = z := Subtype.ext hang
    calc
      H z = H (Proofs.M58.angularPoint theta) := congrArg H hang.symm
      _ = c1 theta := (m64Annulus_polar_traces A theta).2
      _ = periodicFreeLoop gamma1 theta := (h1 theta).symm
      _ = gamma1 q := gamma1.boundary q
      _ = gamma1 (sigma.map z) := by rw [hq]; rfl
  obtain ⟨L, hL, hLip⟩ := m64Annulus_polar_lipschitz A
  obtain ⟨D', _hmap, harea⟩ := m60DiskGluing_of_collar g D
    (r := 1 / 2) (by norm_num) (by norm_num) H sigma hmatch hboundary hL hLip
    (m64Annulus_polar_area_integrable A)
  refine ⟨D', ?_⟩
  rw [harea]
  exact add_le_add le_rfl (m64Annulus_polar_area_le A)

/-- Every supplied spanning disk extends across the actual annulus with area at most their
area sum. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64DiskGluing_of_annulus
    (A : M64Annulus g c0 c1) (gamma0 gamma1 : C1FreeLoopSpace (M := M))
    (h0 : ∀ x, periodicFreeLoop gamma0 x = c0 x)
    (h1 : ∀ x, periodicFreeLoop gamma1 x = c1 x)
    (D : LipschitzSpanningDisk g gamma0) :
    ∃ D' : LipschitzSpanningDisk g gamma1, D'.area ≤ D.area + A.area := by
  obtain ⟨E, hE, harea⟩ := m64ExactBoundaryDisk_of_disk D
  obtain ⟨D', hD'⟩ := m64DiskGluing_of_exact_boundary_annulus A gamma0 gamma1 h0 h1 E hE
  exact ⟨D', by simpa only [harea] using hD'⟩

end PoincareMT
