import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Corner.RayNormalization

/-!
# Exact disk-sector area for arbitrary nondegenerate corner rays

The constructed orthogonal normalization preserves area and the disk.
Positive coefficient rescaling identifies its cone with the reference
cone, yielding the actual Euclidean angle in the area formula.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory InnerProductGeometry
open scoped ENNReal Topology

namespace PoincareMT

/-- The positive cone of an arbitrary nondegenerate pair of complex rays occupies the exact
fraction of a disk determined by their angle. Source: Morgan--Tian Proposition 19.35,
printed pp. 467-481, especially Claim 19.40, pp. 470-471; the explicit project tangent-fan
derivation is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_complex_corner_cone_volume
    {R : ℝ} (hR : 0 < R) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hangle : angle x y ∈ Ioo (0 : ℝ) Real.pi) :
    volume {z : ℂ | ‖z‖ < R ∧
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = s • x + t • y} =
        ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal (angle x y) := by
  obtain ⟨E, hEx, hEy⟩ := m64Intrinsic_complex_corner_normalization hx hy hangle
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hEy
  have hnx := norm_pos_iff.mpr hx
  have hny := norm_pos_iff.mpr hy
  let v : ℂ := (Real.cos (angle x y) : ℂ) +
    (Real.sin (angle x y) : ℂ) * Complex.I
  change E y = (‖y‖ : ℂ) * v at hEy
  have hcone (z : ℂ) :
      (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = s • x + t • y) ↔
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ E z = (s : ℂ) + (t : ℂ) * v := by
    constructor
    · rintro ⟨s, t, hs, ht, rfl⟩
      refine ⟨s * ‖x‖, t * ‖y‖, mul_pos hs hnx, mul_pos ht hny, ?_⟩
      rw [map_add, map_smul, map_smul, hEx, hEy]
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    · rintro ⟨s, t, hs, ht, heq⟩
      refine ⟨s / ‖x‖, t / ‖y‖, div_pos hs hnx, div_pos ht hny, ?_⟩
      apply E.injective
      rw [heq, map_add, map_smul, map_smul, hEx, hEy]
      simp only [Complex.real_smul, Complex.ofReal_div]
      have hnx' : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hnx.ne'
      have hny' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
      field_simp
  let C : Set ℂ := {z | ‖z‖ < R ∧
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = (s : ℂ) + (t : ℂ) * v}
  have hset : {z : ℂ | ‖z‖ < R ∧
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = s • x + t • y} = E ⁻¹' C := by
    ext z
    change (‖z‖ < R ∧ _) ↔ (‖E z‖ < R ∧ _)
    rw [E.norm_map, hcone]
  rw [hset, E.measurePreserving.measure_preimage_emb E.toHomeomorph.measurableEmbedding]
  exact m64Intrinsic_complex_reference_cone_volume hR hangle

end PoincareMT
