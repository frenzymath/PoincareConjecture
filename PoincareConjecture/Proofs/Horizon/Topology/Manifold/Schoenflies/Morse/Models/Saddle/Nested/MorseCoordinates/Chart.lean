import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.MorseCoordinates.Factors
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.MorseCoordinates.LowerHemisphere

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private def axisSwap : E3 ≃ₗᵢ[Real] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 Real Real (Equiv.swap (0 : Fin 3) 2)

private theorem axisSwap_apply (p : E3) (i : Fin 3) :
    axisSwap p i = p (Equiv.swap 0 2 i) := rfl

private theorem axisSwap_involutive (p : E3) : axisSwap (axisSwap p) = p := by
  ext i
  simp only [axisSwap_apply, Equiv.swap_apply_self]

private theorem axisSwap_mem (p : S2) : axisSwap p ∈ sphere (0 : E3) 1 := by
  rw [mem_sphere_zero_iff_norm, axisSwap.norm_map]
  exact norm_eq_of_mem_sphere p

private def sphereAxisSwap : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞ where
  toFun p := ⟨axisSwap p, axisSwap_mem p⟩
  invFun p := ⟨axisSwap p, axisSwap_mem p⟩
  left_inv p := Subtype.ext (axisSwap_involutive p)
  right_inv p := Subtype.ext (axisSwap_involutive p)
  contMDiff_toFun :=
    (axisSwap.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := 2))).codRestrict_sphere axisSwap_mem
  contMDiff_invFun :=
    (axisSwap.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := 2))).codRestrict_sphere axisSwap_mem

private def chartTranslation (z : Real) : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun q := q + z • EuclideanSpace.single 0 1
  invFun q := q - z • EuclideanSpace.single 0 1
  left_inv q := by simp
  right_inv q := by simp
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private theorem chartTranslation_zero (z : Real) (q : E2) :
    chartTranslation z q 0 = z + q 0 := by
  change (q + z • EuclideanSpace.single 0 1 : E2) 0 = _
  simp [add_comm]

private theorem chartTranslation_one (z : Real) (q : E2) :
    chartTranslation z q 1 = q 1 := by
  change (q + z • EuclideanSpace.single 0 1 : E2) 1 = _
  simp

private theorem chartTranslation_norm_sq (z : Real) (q : E2) :
    ‖chartTranslation z q‖^2 = (z + q 0)^2 + (q 1)^2 := by
  rw [norm_sq_two, chartTranslation_zero, chartTranslation_one]

private theorem chartTranslation_mem_ball_iff (z : Real) (q : E2) :
    chartTranslation z q ∈ ball (0 : E2) 1 ↔ q ∈ coordinateDomain z := by
  rw [mem_ball_zero_iff]
  change ‖chartTranslation z q‖ < 1 ↔ 0 < 1 - (z + q 0)^2 - (q 1)^2
  have hn := chartTranslation_norm_sq z q
  constructor <;> intro h <;> nlinarith [norm_nonneg (chartTranslation z q)]

def negativeSphereChart (z : Real) : OpenPartialHomeomorph E2 S2 :=
  ((chartTranslation z).toHomeomorph.toOpenPartialHomeomorph.trans lowerSphereChart).trans
    sphereAxisSwap.toHomeomorph.toOpenPartialHomeomorph

theorem negativeSphereChart_source (z : Real) :
    (negativeSphereChart z).source = coordinateDomain z := by
  ext q
  simp only [negativeSphereChart, OpenPartialHomeomorph.trans_source, mem_inter_iff,
    mem_preimage, Homeomorph.toOpenPartialHomeomorph_source, mem_univ, true_and, and_true,
    lowerSphereChart_source]
  exact chartTranslation_mem_ball_iff z q

theorem negativeSphereChart_target (z : Real) :
    (negativeSphereChart z).target = {p : S2 | (p : E3) 0 < 0} := by
  apply Set.ext
  intro p
  change (p ∈ (univ : Set S2) ∧
    (sphereAxisSwap.symm p : E3) 2 < 0 ∧
      lowerSphereChart.symm (sphereAxisSwap.symm p) ∈ (univ : Set E2)) ↔ _
  simp only [mem_univ, and_true, true_and, mem_ofPred_eq]
  change axisSwap p 2 < 0 ↔ (p : E3) 0 < 0
  simp [axisSwap_apply]

theorem negativeSphereChart_smooth (z : Real) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (negativeSphereChart z) (negativeSphereChart z).source := by
  have hi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun q => lowerSphereChart (chartTranslation z q))
      (negativeSphereChart z).source :=
    lowerSphereChart_smooth.comp (chartTranslation z).contMDiff.contMDiffOn (fun _ hq => hq.1.2)
  exact sphereAxisSwap.contMDiff.comp_contMDiffOn hi

theorem negativeSphereChart_symm_smooth (z : Real) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (negativeSphereChart z).symm :=
  (chartTranslation z).symm.contMDiff.comp
    (lowerSphereChart_symm_smooth.comp sphereAxisSwap.symm.contMDiff)

theorem negativeSphereChart_coe {z : Real} {q : E2}
    (hq : q ∈ (negativeSphereChart z).source) :
    (negativeSphereChart z q : E3) = vector (-(chartRoot z q)) (q 1) (z + q 0) := by
  have ht : chartTranslation z q ∈ lowerSphereChart.source := hq.1.2
  change axisSwap (lowerSphereChart (chartTranslation z q)) = _
  rw [lowerSphereChart_coe ht]
  ext i
  fin_cases i <;>
    simp [axisSwap_apply, lowerSphereGraph, chartTranslation_zero, chartTranslation_one,
      chartTranslation_norm_sq, chartRoot, sub_add_eq_sub_sub, Equiv.swap_apply_def]

theorem negativeSphereChart_zero_mem {z : Real} (hz : 0 < 1 - z^2) :
    0 ∈ (negativeSphereChart z).source := by
  rw [negativeSphereChart_source]
  simpa [coordinateDomain] using hz

theorem negativeSphereChart_zero {z : Real} (hz : 0 < 1 - z^2) :
    (negativeSphereChart z 0 : E3) = vector (-(meridianRoot z)) 0 z := by
  rw [negativeSphereChart_coe (negativeSphereChart_zero_mem hz)]
  simp [chartRoot, meridianRoot]

theorem height_negativeSphereChart {z : Real} {q : E2}
    (hq : q ∈ (negativeSphereChart z).source) :
    height (negativeSphereChart z q) = chartHeight z q := by
  have hd : q ∈ coordinateDomain z := negativeSphereChart_source z ▸ hq
  have hr : (chartRoot z q)^2 = 1 - (z + q 0)^2 - (q 1)^2 :=
    Real.sq_sqrt (show 0 ≤ 1 - (z + q 0)^2 - (q 1)^2 from le_of_lt hd)
  rw [height_apply, negativeSphereChart_coe hq]
  simp only [vector_zero, vector_one, vector_two, neg_sq]
  rw [hr]
  dsimp [chartHeight]
  ring

end Poincare.Manifold.Schoenflies.Saddle.Nested
