import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.SmoothAnnulus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

noncomputable def m65SweptMap (c : ℝ → ℝ → M) (s t : ℝ) (p : LoopPlane) : M :=
  c (p 0) (s + (t - s) * Real.smoothTransition (p 1))

theorem m65SweptTime_mem {s t : ℝ} (hst : s ≤ t) (y : ℝ) :
    s + (t - s) * Real.smoothTransition y ∈ Set.Icc s t := by
  have h0 := mul_nonneg (sub_nonneg.mpr hst) (Real.smoothTransition.nonneg y)
  have h1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one y) (sub_nonneg.mpr hst)
  constructor <;> linarith

theorem m65SweptMap_contMDiff {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b) :
    ContMDiff (𝓡 2) (𝓡 n) ∞ (m65SweptMap c s t) := by
  have hp : ContDiff ℝ ∞
      (fun p : LoopPlane => (p 0, s + (t - s) * Real.smoothTransition (p 1))) := by
    fun_prop
  exact hc.joint_smooth.comp_contMDiff hp.contMDiff (fun p =>
    ⟨Set.mem_univ _, has.trans_le (m65SweptTime_mem hst (p 1)).1,
      (m65SweptTime_mem hst (p 1)).2.trans_lt htb⟩)

noncomputable def m65InteriorSweptAnnulus (g : RiemannianMetric n M)
    {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b) :
    M64Annulus g (fun x => c x s) (fun x => c x t) :=
  m65AnnulusOfContMDiff g (m65SweptMap c s t)
    ((m65SweptMap_contMDiff hc has hst htb).of_le (by simp))
    (by
      intro x y
      change c (x + curvePeriod) (s + (t - s) * Real.smoothTransition y) =
        c x (s + (t - s) * Real.smoothTransition y)
      exact hc.periodic _ ⟨has.le.trans (m65SweptTime_mem hst y).1,
        (m65SweptTime_mem hst y).2.trans htb.le⟩ x)
    (by
      intro x
      change c x (s + (t - s) * Real.smoothTransition 0) = c x s
      rw [Real.smoothTransition.zero, mul_zero, add_zero])
    (by
      intro x
      change c x (s + (t - s) * Real.smoothTransition 1) = c x t
      rw [Real.smoothTransition.one, mul_one, add_sub_cancel])

@[simp] theorem m65InteriorSweptAnnulus_map (g : RiemannianMetric n M)
    {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b) :
    (m65InteriorSweptAnnulus g hc has hst htb).map = m65SweptMap c s t := rfl

end PoincareConjecture
