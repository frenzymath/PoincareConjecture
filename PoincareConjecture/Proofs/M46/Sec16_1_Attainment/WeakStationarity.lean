import PoincareConjecture.Proofs.M08.ChartPerturbation
import PoincareConjecture.Proofs.M08.ChartStationarity
import Mathlib.Analysis.Calculus.LocalExtr.Basic









set_option autoImplicit false
set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace PoincareConjecture.Proofs.M46

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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



theorem compact_three_norm_bounds {Y A B C : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
    {K : Set Y} (hK : IsCompact K) (f : Y → A) (g : Y → B) (h : Y → C)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (hh : ContinuousOn h K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ K, ‖f z‖ ≤ D ∧ ‖g z‖ ≤ D ∧ ‖h z‖ ≤ D := by
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hf.norm.add hg.norm |>.add hh.norm)
  refine ⟨|D|, abs_nonneg _, ?_⟩
  intro z hz
  have hv := hD z hz
  simp only [Pi.add_apply] at hv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hv
  exact ⟨by linarith [norm_nonneg (g z), norm_nonneg (h z), le_abs_self D],
    by linarith [norm_nonneg (f z), norm_nonneg (h z), le_abs_self D],
    by linarith [norm_nonneg (f z), norm_nonneg (g z), le_abs_self D]⟩




theorem weak_quadratic_affine_stationary {a b : ℝ} (hab : a ≤ b)
    {S : Set E} (hS : IsOpen S)
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DB : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hB : ContinuousOn B (Icc a b ×ˢ S)) (hV : ContinuousOn V (Icc a b ×ˢ S))
    (hDB : ContinuousOn DB (Icc a b ×ˢ S)) (hDV : ContinuousOn DV (Icc a b ×ˢ S))
    (hBd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => B (z.1, x)) (DB z) z.2)
    (hVd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => V (z.1, x)) (DV z) z.2)
    (hsym : ∀ z ∈ Icc a b ×ˢ S, ∀ v w : E, B z v w = B z w v)
    (u w : ℝ → E) (hu : ContinuousOn u (Icc a b)) (hmem : MapsTo u (Icc a b) S)
    (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (eta nu : ℝ → E) (heta : ContinuousOn eta (Icc a b))
    (hnu : ContinuousOn nu (Icc a b))
    (hmin : IsLocalMin (fun e : ℝ => ∫ s in a..b,
      B (s, u s + e • eta s) (w s + e • nu s) (w s + e • nu s) / 2 +
        V (s, u s + e • eta s)) 0) :
    (∫ s in a..b, DB (s, u s) (eta s) (w s) (w s) / 2 +
      B (s, u s) (w s) (nu s) + DV (s, u s) (eta s)) = 0 := by
  obtain ⟨K, hK, huK, hKS⟩ := exists_compact_between
    (isCompact_Icc.image_of_continuousOn hu) hS hmem.image_subset
  obtain ⟨delta, hdelta, hdelta1, hshift⟩ :=
    M08.exists_uniform_affine_tube u eta hu heta huK
  have hsub : Icc a b ×ˢ K ⊆ Icc a b ×ˢ S := prod_mono_right hKS
  obtain ⟨C, hC, hcoeff⟩ := compact_three_norm_bounds (isCompact_Icc.prod hK)
    B DB DV (hB.mono hsub) (hDB.mono hsub) (hDV.mono hsub)
  obtain ⟨D, hD, hdir⟩ := compact_three_norm_bounds isCompact_Icc eta nu nu heta hnu hnu
  have hd := M08.affine_chart_action_hasDerivAt hab hdelta hdelta1 hC hD K u w eta nu
    hu hw heta hnu (fun s x => B (s, x)) (fun s x => V (s, x))
    (fun s x => DB (s, x)) (fun s x => DV (s, x))
    (hB.mono hsub) (hV.mono hsub) (hDB.mono hsub) (hDV.mono hsub)
    (fun e he s hs => hshift e (abs_lt.mpr he) hs)
    (fun s hs x hx => hBd (s, x) ⟨hs, hKS hx⟩)
    (fun s hs x hx => hVd (s, x) ⟨hs, hKS hx⟩)
    (fun s hs x hx => hsym (s, x) ⟨hs, hKS hx⟩)
    (fun s hs x hx => hcoeff (s, x) ⟨hs, hx⟩)
    (fun s hs => ⟨(hdir s hs).1, (hdir s hs).2.1⟩)
  exact hmin.hasDerivAt_eq_zero hd.2

end PoincareConjecture.Proofs.M46
