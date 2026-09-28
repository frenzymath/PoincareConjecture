import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorCoherentJets
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem hasDerivAt_of_dense_test_derivatives
    (test : ι → H) (htest : DenseRange test) (f g : ℝ → H) {a b t : ℝ}
    (ht : t ∈ Ioo a b) (hg : ContinuousOn g (Ioo a b))
    (hd : ∀ s ∈ Ioo a b, ∀ φ,
      HasDerivAt (fun r => inner ℝ (f r) (test φ)) (inner ℝ (g s) (test φ)) s) :
    HasDerivAt f (g t) t := by
  let l := (a + t) / 2
  let r := (t + b) / 2
  have hsub : Icc l r ⊆ Ioo a b := by
    intro s hs
    dsimp only [l, r] at hs
    constructor <;> linarith only [ht.1, ht.2, hs.1, hs.2]
  have hmem : t ∈ Ioo l r := by
    dsimp only [l, r]
    constructor <;> linarith only [ht.1, ht.2]
  have heq (s : ℝ) (hs : s ∈ Icc l r) :
      f s = f l + ∫ q in l..s, g q := by
    have hinterval : uIcc l s ⊆ Ioo a b := by
      rw [uIcc_of_le hs.1]
      exact (Icc_subset_Icc le_rfl hs.2).trans hsub
    have hint : IntervalIntegrable g volume l s := (hg.mono hinterval).intervalIntegrable
    apply htest.eq_of_inner_left ℝ
    intro φ
    let T : H →L[ℝ] ℝ := innerSL ℝ (test φ)
    have hT (v : H) : T v = inner ℝ v (test φ) := real_inner_comm _ _
    have hscalar : (∫ q in l..s, T (g q)) = T (f s) - T (f l) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro q hq
        simpa only [hT] using hd q (hinterval hq) φ
      · exact (T.continuous.comp_continuousOn (hg.mono hinterval)).intervalIntegrable
    rw [T.intervalIntegral_comp_comm hint] at hscalar
    rw [inner_add_left]
    simpa only [hT] using (eq_add_of_sub_eq (hscalar.symm)).trans (add_comm _ _)
  have hint : IntervalIntegrable g volume l t :=
    (hg.mono (by
      rw [uIcc_of_le hmem.1.le]
      exact (Icc_subset_Icc le_rfl hmem.2.le).trans hsub)).intervalIntegrable
  have hi := intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hg t ht)
    (hg.continuousAt (isOpen_Ioo.mem_nhds ht))
  apply (hi.const_add (f l)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hmem.1 hmem.2] with s hs
  exact heq s hs

end PoincareConjecture.M35.Uniqueness.Heat
