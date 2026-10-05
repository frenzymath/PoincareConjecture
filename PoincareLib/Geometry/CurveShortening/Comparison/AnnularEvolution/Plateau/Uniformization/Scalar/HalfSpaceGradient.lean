import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.BoundaryContinuous

/-!
# Continuous derivative representatives through the annular boundary

In two dimensions, compactly supported H2 functions on a half-space
have continuous representatives through its boundary. Lowering the
initial exponent to 3/2 and applying the actual half-space Sobolev
estimate gives W1,6; even reflection and Morrey embedding then provide
the continuous representative. Applying this to each H2 weak first
derivative of an H3 function supplies actual continuous gradients.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareMT.M64Uniformization

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential BoundaryExtension EuclideanEmbedding

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

private theorem scalar_wholeSpace_continuous_representative
    {u : Plane → ℝ} (hc : HasCompactSupport u) (hu : MemW1p 6 u univ) :
    ∃ F : Plane → ℝ, Continuous F ∧ u =ᵐ[volume] F := by
  obtain ⟨R, hR, hKR⟩ := hc.isBounded.subset_ball_lt 0 (0 : Plane)
  obtain ⟨χ, hχ, hχc, -, hχone, hχs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hc Metric.isOpen_ball hKR
  have huB : MemWkp 1 (ENNReal.ofReal 6) u (Metric.ball (0 : Plane) (4 * R)) := by
    apply MemWkp.one_iff_memW1p.mpr
    simpa using Euclidean.MemW1p.mono_set Metric.isOpen_ball (subset_univ _) hu
  obtain ⟨F, hF, hFu⟩ := EuclideanMorrey.morrey_iteratedFDeriv_representative
    (by norm_num : (2 : ℝ) < 6) (by positivity : 0 < 4 * R) 0 huB
  have hχu (x : Plane) : χ x * u x = u x := by
    by_cases hx : u x = 0
    · simp [hx]
    · rw [hχone x (subset_tsupport u hx), one_mul]
  have hball : Metric.ball (0 : Plane) (4 * R / 4) = Metric.ball (0 : Plane) R := by
    congr 1
    ring
  rw [hball] at hFu
  have hFu' : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Plane) R → u x = F x :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hFu
  refine ⟨fun x => χ x * F x, hχ.continuous.mul hF.continuous, ?_⟩
  filter_upwards [hFu'] with x hx
  by_cases hxB : x ∈ Metric.ball (0 : Plane) R
  · rw [← hx hxB, hχu]
  · have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxB (hKR h))
    have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxB (hχs h))
    simp [hu0, hχ0]

/-- Actual planar H2 regularity supplies a continuous representative through the half-space
boundary, without a zero-trace assumption. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalar_halfSpace_H2_continuous_extension {u : Plane → ℝ}
    (hc : HasCompactSupport u) (hu : MemWkp 2 2 u Half) :
    ∃ F : Plane → ℝ, Continuous F ∧ u =ᵐ[volume.restrict Half] F := by
  have hup : MemWkp 2 (ENNReal.ofReal (3 / 2)) u Half :=
    EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset 2
      isOpen_halfSpace (isClosed_tsupport u) hc.measure_lt_top.ne
      (by norm_num) (by norm_num) (subset_refl _) hu
  have hu6 : MemWkp 1 6 u Half := by
    convert! BoundaryEmbedding.memWkp_subcritical 1
      (by norm_num : (1 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2) hc hup using 1 ;
      norm_num
  have he : MemW1p 6 (evenReflect u) univ :=
    memW1p_evenReflect (by norm_num) (by norm_num) hu6.memW1p
  obtain ⟨F, hF, hae⟩ := scalar_wholeSpace_continuous_representative
    (hasCompactSupport_evenReflect hc) he
  refine ⟨F, hF, ?_⟩
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem isOpen_halfSpace.measurableSet]
    with x hx hxH
  exact (evenReflect_eq_on_halfSpace u hxH).symm.trans hx

/-- The two actual weak first derivatives of a compactly supported H3 function have
continuous representatives through the half-space boundary. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalar_halfSpace_H3_continuous_gradient {u : Plane → ℝ}
    (hc : HasCompactSupport u) (hu : MemWkp 3 2 u Half) :
    ∃ G : Fin 2 → Plane → ℝ, (∀ i, Continuous (G i)) ∧
      ∀ i, chosenWeakPartial' 2 i u Half =ᵐ[volume.restrict Half] G i := by
  let v (i : Fin 2) := iteratedZeroExtension 2 Half (tsupport u) 1 (fun _ : Fin 1 => i) u
  have hvc (i : Fin 2) : HasCompactSupport (v i) :=
    hasCompactSupport_iteratedZeroExtension hc (isClosed_tsupport u) (subset_refl _) 1 _
  have hv (i : Fin 2) : MemWkp 2 2 (v i) Half := by
    simpa using iteratedZeroExtension_memWkp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      isOpen_halfSpace (isClosed_tsupport u) 1 3 (by omega) (fun _ : Fin 1 => i) hu
      (subset_refl _)
  have hvae (i : Fin 2) : v i =ᵐ[volume.restrict Half] chosenWeakPartial' 2 i u Half := by
    have h := iteratedZeroExtension_ae_eq_iterWeakPartial (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      isOpen_halfSpace (isClosed_tsupport u) 1 3 (by omega) (fun _ : Fin 1 => i) hu
      (subset_refl _)
    simpa only [iterWeakPartial_succ, iterWeakPartial_zero] using h
  choose G hGc hG using fun i => scalar_halfSpace_H2_continuous_extension (hvc i) (hv i)
  exact ⟨G, hGc, fun i => (hvae i).symm.trans (hG i)⟩

end PoincareMT.M64Uniformization
