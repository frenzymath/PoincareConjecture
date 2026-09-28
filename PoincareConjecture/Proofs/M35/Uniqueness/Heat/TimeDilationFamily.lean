import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CompactFamilyDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dilationTime_mem {a b T B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hBT : b * T ≤ B) (s : Icc a b) (t : Icc (0 : ℝ) T) :
    s.val * t.val ∈ Icc 0 B :=
  ⟨mul_nonneg (ha.trans s.property.1) t.property.1,
    (mul_le_mul s.property.2 t.property.2 t.property.1 (ha.trans hab)).trans hBT⟩

def compactDilationJet {a b T B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) (k : ℕ) (s : ℝ) :
    C(Icc (0 : ℝ) T, E) where
  toFun t := t.val ^ k • iteratedDerivWithin k A (Icc 0 B)
    ((projIcc a b hab s).val * t.val)
  continuous_toFun := by
    apply (continuous_subtype_val.pow k).smul
    exact (hA.continuousOn_iteratedDerivWithin
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k).le (uniqueDiffOn_Icc hB)).comp_continuous
      (continuous_const.mul continuous_subtype_val)
      (fun t => dilationTime_mem ha hab hBT (projIcc a b hab s) t)

theorem compactDilationJet_apply {a b T B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) (k : ℕ)
    {s : ℝ} (hs : s ∈ Icc a b) (t : Icc (0 : ℝ) T) :
    compactDilationJet ha hab hBT hB A hA k s t =
      t.val ^ k • iteratedDerivWithin k A (Icc 0 B) (s * t.val) := by
  change t.val ^ k • iteratedDerivWithin k A (Icc 0 B)
    ((projIcc a b hab s).val * t.val) = _
  rw [projIcc_of_mem hab hs]

theorem compactDilationJet_joint_continuous {a b T B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) (k : ℕ) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) T => compactDilationJet ha hab hBT hB A hA k p.1 p.2) := by
  apply ((continuous_subtype_val.comp continuous_snd).pow k).smul
  apply (hA.continuousOn_iteratedDerivWithin
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k).le (uniqueDiffOn_Icc hB)).comp_continuous
    (((continuous_subtype_val.comp continuous_projIcc).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  intro p
  exact dilationTime_mem ha hab hBT (projIcc a b hab p.1) p.2

theorem hasDerivWithinAt_compactDilationJet {a b T B : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) (k : ℕ)
    {s : ℝ} (hs : s ∈ Icc a b) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => compactDilationJet ha hab.le hBT hB A hA k r t)
      (compactDilationJet ha hab.le hBT hB A hA (k + 1) s t) (Icc a b) s := by
  have htime := dilationTime_mem ha hab.le hBT ⟨s, hs⟩ t
  have hdA := (hA.differentiableOn_iteratedDerivWithin (m := k)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
    (uniqueDiffOn_Icc hB) _ htime).hasDerivWithinAt
  rw [← iteratedDerivWithin_succ] at hdA
  have hdtime : HasDerivWithinAt (fun r : ℝ => r * t.val) t.val (Icc a b) s := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id s).mul_const t.val).hasDerivWithinAt
  have hd := (hdA.scomp s hdtime
    (fun r hr => dilationTime_mem ha hab.le hBT ⟨r, hr⟩ t)).const_smul (t.val ^ k)
  have hd' : HasDerivWithinAt
      (fun r => t.val ^ k • iteratedDerivWithin k A (Icc 0 B) (r * t.val))
      (t.val ^ (k + 1) • iteratedDerivWithin (k + 1) A (Icc 0 B) (s * t.val)) (Icc a b) s := by
    simpa only [Function.comp_def, Pi.smul_def, ← mul_smul, ← pow_succ] using hd
  rw [compactDilationJet_apply ha hab.le hBT hB A hA (k + 1) hs t]
  exact hd'.congr_of_mem
    (fun r hr => compactDilationJet_apply ha hab.le hBT hB A hA k hr t) hs

theorem contDiffOn_compactDilation {a b T B : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) :
    ContDiffOn ℝ ∞ (compactDilationJet ha hab.le hBT hB A hA 0) (Icc a b) :=
  contDiffOn_compact_family_of_jets hab _
    (fun k _ hs t => hasDerivWithinAt_compactDilationJet ha hab hBT hB A hA k hs t)
    (fun k => (compactDilationJet_joint_continuous ha hab.le hBT hB A hA k).continuousOn)

end PoincareConjecture.M35.Uniqueness.Heat
