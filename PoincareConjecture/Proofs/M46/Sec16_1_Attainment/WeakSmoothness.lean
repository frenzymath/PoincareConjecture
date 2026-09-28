import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.WeakRegularity
import PoincareConjecture.Proofs.M14.Mathlib.QuadraticMinimizerRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace PoincareConjecture.Proofs.M46

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace




theorem weak_quadratic_minimum_smooth {a b : ℝ} (hab : a < b)
    {S : Set E} (hS : IsOpen S)
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DB : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Icc a b ×ˢ S)) (hV : ContinuousOn V (Icc a b ×ˢ S))
    (hDB : ContDiffOn ℝ ∞ DB (Icc a b ×ˢ S)) (hDV : ContDiffOn ℝ ∞ DV (Icc a b ×ˢ S))
    (hBd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => B (z.1, x)) (DB z) z.2)
    (hVd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => V (z.1, x)) (DV z) z.2)
    (hsym : ∀ z ∈ Icc a b ×ˢ S, ∀ v w : E, B z v w = B z w v)
    (hpos : ∀ z ∈ Icc a b ×ˢ S, ∀ v : E, v ≠ 0 → 0 < B z v v)
    (u : ℝ → E) (hu : ContinuousOn u (Icc a b)) (hmem : MapsTo u (Icc a b) S)
    (w : M08.ChartL2 E a b)
    (hprimitive : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, w r)
    (hmin : ∀ eta : ℝ → E, ContDiff ℝ ∞ eta → tsupport eta ⊆ Ioo a b →
      IsLocalMin (fun e : ℝ => ∫ s in a..b,
        B (s, u s + e • eta s) (w s + e • deriv eta s) (w s + e • deriv eta s) / 2 +
          V (s, u s + e • eta s)) 0) :
    ContDiffOn ℝ ∞ u (Icc a b) := by
  have hreg := weak_quadratic_minimum_contDiffOn hab hS B V DB DV hB.continuousOn hV
    hDB.continuousOn hDV.continuousOn hBd hVd hsym hpos u hu hmem w hprimitive hmin
  have hvelocity : (w : ℝ → E) =ᵐ[volume.restrict (Icc a b)] derivWithin u (Icc a b) := by
    filter_upwards [M08.chart_primitive_ae_hasDerivAt hab.le u w hprimitive,
      ae_restrict_mem measurableSet_Icc] with s hs hmems
    exact (hs.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab s hmems)).symm
  apply (ODE.contDiffOn_of_quadratic_local_minima hab B V DB DV hB hV hDB hDV
    hBd hVd hsym hpos u hreg hmem ?_).1
  intro eta heta hsupp
  obtain ⟨K, _, huK, hKS⟩ := exists_compact_between
    (isCompact_Icc.image_of_continuousOn hu) hS hmem.image_subset
  obtain ⟨delta, hdelta, _, hshift⟩ :=
    M08.exists_uniform_affine_tube u eta hu heta.continuous.continuousOn huK
  refine ⟨delta, hdelta, fun s hs e he => hKS (hshift e (abs_lt.mpr he) hs), ?_⟩
  have heq (e : ℝ) :
      (∫ s in a..b, B (s, u s + e • eta s)
        (derivWithin u (Icc a b) s + e • deriv eta s)
        (derivWithin u (Icc a b) s + e • deriv eta s) / 2 + V (s, u s + e • eta s)) =
      ∫ s in a..b, B (s, u s + e • eta s)
        (w s + e • deriv eta s) (w s + e • deriv eta s) / 2 + V (s, u s + e • eta s) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hab.le]
    filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hvelocity] with s hs
    rw [hs]
  simpa only [heq] using hmin eta heta hsupp

end PoincareConjecture.Proofs.M46
