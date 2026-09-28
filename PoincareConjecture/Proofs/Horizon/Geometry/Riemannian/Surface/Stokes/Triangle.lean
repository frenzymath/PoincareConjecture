import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Stokes.Rectangle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval Topology ContDiff Manifold

namespace PoincareConjecture.Surface

theorem isCompact_standardTriangle :
    IsCompact {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
  have hc : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  apply (isCompact_Icc (a := ((0, 0) : ℝ × ℝ)) (b := (1, 1))).of_isClosed_subset hc
  intro p hp
  exact ⟨⟨hp.1, hp.2.1⟩, ⟨by linarith [hp.2.2, hp.2.1], by linarith [hp.2.2, hp.1]⟩⟩

theorem integral_standardTriangle_eq_iterated
    (F : ℝ × ℝ → ℝ)
    (hF : ContinuousOn F {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) :
    (∫ p in {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}, F p) =
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), F (u, v) := by
  let T := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
  have hm : MeasurableSet T := isCompact_standardTriangle.measurableSet
  have hi : Integrable (T.indicator F) :=
    (integrable_indicator_iff hm).mpr (hF.integrableOn_compact isCompact_standardTriangle)
  rw [← integral_indicator hm]
  change (∫ p, T.indicator F p ∂volume.prod volume) = _
  rw [integral_prod _ hi]
  have hslice (u : ℝ) : (∫ v : ℝ, T.indicator F (u, v)) =
      (Icc (0 : ℝ) 1).indicator (fun u => ∫ v in Icc (0 : ℝ) (1 - u), F (u, v)) u := by
    by_cases hu : u ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hu]
      rw [← integral_indicator measurableSet_Icc]
      congr 1
      funext v
      have hv : (u, v) ∈ T ↔ v ∈ Icc (0 : ℝ) (1 - u) := by
        dsimp [T]
        constructor <;> intro h
        · exact ⟨h.2.1, by linarith [h.2.2]⟩
        · exact ⟨hu.1, h.1, by linarith [h.2]⟩
      simp only [indicator, hv]
    · rw [indicator_of_notMem hu]
      apply integral_eq_zero_of_ae
      apply Filter.Eventually.of_forall
      intro v
      apply indicator_of_notMem
      intro hv
      apply hu
      exact ⟨hv.1, by linarith [hv.2.1, hv.2.2]⟩
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hu.2), integral_Icc_eq_integral_Ioc]

private def triangleMap (p : ℝ × ℝ) : ℝ × ℝ := (p.1, (1 - p.1) * p.2)

private theorem contDiff_triangleMap : ContDiff ℝ 1 triangleMap :=
  contDiff_fst.prodMk ((contDiff_const.sub contDiff_fst).mul contDiff_snd)

private theorem curl_triangle_pullback
    (P Q : ℝ × ℝ → ℝ) (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (p : ℝ × ℝ) :
    fderiv ℝ (fun z => (1 - z.1) * Q (triangleMap z)) p (1, 0) -
        fderiv ℝ (fun z => P (triangleMap z) - z.2 * Q (triangleMap z)) p (0, 1) =
      (1 - p.1) * (fderiv ℝ Q (triangleMap p) (1, 0) -
        fderiv ℝ P (triangleMap p) (0, 1)) := by
  have hT := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
    (((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).sub hasFDerivAt_fst).mul
      hasFDerivAt_snd)
  have hPc := ((hP.differentiable one_ne_zero)
      (triangleMap p)).hasFDerivAt.comp p hT
  have hQc := ((hQ.differentiable one_ne_zero)
      (triangleMap p)).hasFDerivAt.comp p hT
  have hA := hPc.sub (hasFDerivAt_snd.mul hQc)
  have hB := ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).sub
    hasFDerivAt_fst).mul hQc
  simp only [Pi.sub_def, Pi.mul_def, Function.comp_def] at hA hB
  rw [hA.fderiv, hB.fderiv]
  simp
  have hvec : (1, -p.2) = (1, 0) + (-p.2) • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hvec' : (0, 1 - p.1) = (1 - p.1) • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [hvec, hvec']
  simp only [map_add, map_smul, smul_eq_mul]
  ring

theorem integral_curl_triangle
    (P Q : ℝ × ℝ → ℝ) (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x),
      fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) =
      (∫ x in (0 : ℝ)..1, P (x, 0)) -
        (∫ x in (0 : ℝ)..1, P (x, 1 - x) - Q (x, 1 - x)) -
        ∫ y in (0 : ℝ)..1, Q (0, y) := by
  let A : ℝ × ℝ → ℝ := fun z => P (triangleMap z) - z.2 * Q (triangleMap z)
  let B : ℝ × ℝ → ℝ := fun z => (1 - z.1) * Q (triangleMap z)
  have hA : ContDiff ℝ 1 A :=
    (hP.comp contDiff_triangleMap).sub
      (contDiff_snd.mul (hQ.comp contDiff_triangleMap))
  have hB : ContDiff ℝ 1 B :=
    (contDiff_const.sub contDiff_fst).mul (hQ.comp contDiff_triangleMap)
  have hstokes := integral_curl_rectangle A B hA hB (a₁ := 0) (b₁ := 1)
    (a₂ := 0) (b₂ := 1) zero_le_one zero_le_one
  have hcurl : ∀ z, fderiv ℝ B z (1, 0) - fderiv ℝ A z (0, 1) =
      (1 - z.1) * (fderiv ℝ Q (triangleMap z) (1, 0) -
        fderiv ℝ P (triangleMap z) (0, 1)) := by
    intro z
    exact curl_triangle_pullback P Q hP hQ z
  simp_rw [hcurl] at hstokes
  simp only [A, B, triangleMap, mul_zero, sub_zero, zero_mul, sub_self,
    one_mul, mul_one, intervalIntegral.integral_zero, add_zero] at hstokes
  convert hstokes using 1
  apply intervalIntegral.integral_congr
  intro x hx
  simpa [smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun y => fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1))
      (1 - x)).symm

private theorem exists_contDiff_extension_near_closed
    {K U : Set (ℝ × ℝ)} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    ∃ f' : ℝ × ℝ → ℝ, ContDiff ℝ 1 f' ∧
      ∀ x ∈ K, f' =ᶠ[nhds x] f := by
  obtain ⟨χ, hzero, hone, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, ℝ × ℝ)
      hU.isClosed_compl hK (disjoint_left.mpr fun x hxU hxK => hxU (hKU hxK)) (n := 1)
  have hχ : ContDiff ℝ 1 χ := contMDiff_iff_contDiff.mp χ.contMDiff
  refine ⟨fun x => χ x * f x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [hone.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp [hy]

theorem integral_curl_triangle_of_contDiffOn
    (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (htriangle : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x),
      fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) =
      (∫ x in (0 : ℝ)..1, P (x, 0)) -
        (∫ x in (0 : ℝ)..1, P (x, 1 - x) - Q (x, 1 - x)) -
        ∫ y in (0 : ℝ)..1, Q (0, y) := by
  let K : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
  have hK : IsClosed K :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  obtain ⟨P', hP', hPeq⟩ := exists_contDiff_extension_near_closed hK hU htriangle hP
  obtain ⟨Q', hQ', hQeq⟩ := exists_contDiff_extension_near_closed hK hU htriangle hQ
  have hbottom (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) : (x, 0) ∈ K := by
    rw [uIcc_of_le zero_le_one] at hx
    exact ⟨hx.1, le_rfl, by simpa using hx.2⟩
  have hdiagonal (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) : (x, 1 - x) ∈ K := by
    rw [uIcc_of_le zero_le_one] at hx
    exact ⟨hx.1, sub_nonneg.mpr hx.2, by linarith⟩
  have hleft (y : ℝ) (hy : y ∈ uIcc (0 : ℝ) 1) : (0, y) ∈ K := by
    rw [uIcc_of_le zero_le_one] at hy
    exact ⟨le_rfl, hy.1, by simpa using hy.2⟩
  have hi : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x),
      fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) =
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x),
      fderiv ℝ Q' (x, y) (1, 0) - fderiv ℝ P' (x, y) (0, 1)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (sub_nonneg.mpr hx.2)] at hy
    have hxy : (x, y) ∈ K := ⟨hx.1, hy.1, by linarith [hy.2]⟩
    dsimp only
    rw [(hPeq _ hxy).fderiv_eq (𝕜 := ℝ), (hQeq _ hxy).fderiv_eq (𝕜 := ℝ)]
  rw [hi, integral_curl_triangle P' Q' hP' hQ']
  apply congrArg₂ (fun s t : ℝ => s - t)
  · apply congrArg₂ (fun s t : ℝ => s - t)
    · apply intervalIntegral.integral_congr
      intro x hx
      exact (hPeq _ (hbottom x hx)).self_of_nhds
    · apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [(hPeq _ (hdiagonal x hx)).self_of_nhds,
        (hQeq _ (hdiagonal x hx)).self_of_nhds]
  · apply intervalIntegral.integral_congr
    intro y hy
    exact (hQeq _ (hleft y hy)).self_of_nhds

end PoincareConjecture.Surface
