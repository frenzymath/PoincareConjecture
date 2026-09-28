import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusCutCompletion
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "D" => Set.ofPred (fun p : LoopPlane =>
  p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1)
local notation "half" => curvePeriod / 2
local notation "v" => annulusPoint (curvePeriod / 2) 0




theorem m64AnnulusCutCompletion_contMDiffOn
    {f g : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f D) (hg : ContMDiffOn (𝓡 2) (𝓡 n) 1 g D)
    (hleft : EqOn f (fun p => g (p + v))
      {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) half ∧ p 1 ∈ Icc (0 : ℝ) 1})
    (hright : EqOn f (fun p => g (p - v))
      {p : LoopPlane | p 0 ∈ Ioo half curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1}) :
    ContMDiffOn (𝓡 2) (𝓡 n) 1 (m64AnnulusCutCompletion f g) m64AnnulusDomain := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  intro p hp
  by_cases hp0 : p 0 = 0
  · let O : Set LoopPlane := {q | q 0 < half}
    have hO : O ∈ 𝓝 p := (isOpen_lt (by fun_prop) continuous_const).mem_nhds
      (by change p 0 < half; rw [hp0]; exact half_pos hP)
    have hm : MapsTo (fun q : LoopPlane => q + v) (m64AnnulusDomain ∩ O) D := by
      intro q hq
      change (q + v) 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ (q + v) 1 ∈ Icc (0 : ℝ) 1
      simp only [PiLp.add_apply, annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, add_zero]
      have hqx : q 0 < half := hq.2
      exact ⟨⟨by linarith [hq.1.1], by linarith⟩, hq.1.2.2⟩
    have hpO : p ∈ m64AnnulusDomain ∩ O := ⟨hp, mem_of_mem_nhds hO⟩
    have hs : ContMDiff (𝓡 2) (𝓡 2) 1 (fun q : LoopPlane => q + v) :=
      (contDiff_id.add contDiff_const).contMDiff
    have hc := (hg (p + v) (hm hpO)).comp p (hs p).contMDiffWithinAt hm
    have hc' := hc.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds hO))
    apply hc'.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with q hq hqO
    change m64AnnulusCutCompletion f g q = g (q + v)
    by_cases hq0 : q 0 = 0
    · simp only [m64AnnulusCutCompletion, if_pos hq0]
    · have hqP : q 0 ≠ curvePeriod := by intro h; change q 0 < half at hqO; linarith
      simp only [m64AnnulusCutCompletion, if_neg hq0, if_neg hqP]
      exact hleft ⟨⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hqO⟩, hq.2.2⟩
  by_cases hpP : p 0 = curvePeriod
  · let O : Set LoopPlane := {q | half < q 0}
    have hO : O ∈ 𝓝 p := (isOpen_lt continuous_const (by fun_prop)).mem_nhds
      (by change half < p 0; rw [hpP]; linarith)
    have hm : MapsTo (fun q : LoopPlane => q - v) (m64AnnulusDomain ∩ O) D := by
      intro q hq
      change (q - v) 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ (q - v) 1 ∈ Icc (0 : ℝ) 1
      simp only [PiLp.sub_apply, annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, sub_zero]
      have hqx : half < q 0 := hq.2
      exact ⟨⟨by linarith, by linarith [hq.1.2.1]⟩, hq.1.2.2⟩
    have hpO : p ∈ m64AnnulusDomain ∩ O := ⟨hp, mem_of_mem_nhds hO⟩
    have hs : ContMDiff (𝓡 2) (𝓡 2) 1 (fun q : LoopPlane => q - v) :=
      (contDiff_id.sub contDiff_const).contMDiff
    have hc := (hg (p - v) (hm hpO)).comp p (hs p).contMDiffWithinAt hm
    have hc' := hc.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds hO))
    apply hc'.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with q hq hqO
    change m64AnnulusCutCompletion f g q = g (q - v)
    have hq0 : q 0 ≠ 0 := by intro h; change half < q 0 at hqO; linarith
    by_cases hqP : q 0 = curvePeriod
    · simp only [m64AnnulusCutCompletion, if_neg hq0, if_pos hqP]
    · simp only [m64AnnulusCutCompletion, if_neg hq0, if_neg hqP]
      exact hright ⟨⟨hqO, lt_of_le_of_ne hq.2.1 hqP⟩, hq.2.2⟩
  · have hx : p 0 ∈ Ioo (0 : ℝ) curvePeriod :=
      ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2.1 hpP⟩
    have hO : {q : LoopPlane | q 0 ∈ Ioo (0 : ℝ) curvePeriod} ∈ 𝓝 p :=
      (isOpen_Ioo.preimage (by fun_prop)).mem_nhds hx
    have hc : ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain p :=
      (hf p ⟨hx, hp.2.2⟩).mono_of_mem_nhdsWithin (by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with q hq hqx
        exact ⟨hqx, hq.2.2⟩)
    apply hc.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [mem_nhdsWithin_of_mem_nhds hO] with q hq
    exact m64AnnulusCutCompletion_interior f g hq

end PoincareConjecture
