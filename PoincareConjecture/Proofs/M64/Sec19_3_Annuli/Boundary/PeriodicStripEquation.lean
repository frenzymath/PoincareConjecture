import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.PeriodicHarmonicMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SupportedRectangleAdmission






set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology

namespace PoincareConjecture.M64





theorem annulus_periodic_integer_translate {Y : Type*} {f : LoopPlane → Y}
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (k : ℤ) (p : LoopPlane) : f (annulusPoint (k • curvePeriod) 0 + p) = f p := by
  have hp : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hshift : annulusPoint (k • curvePeriod) 0 + p =
      annulusPoint (p 0 + k • curvePeriod) (p 1) := by
    ext i
    fin_cases i <;> simp [annulusPoint, add_comm]
  have hper : Function.Periodic (fun x => f (annulusPoint x (p 1))) curvePeriod :=
    fun x => hperiod x (p 1)
  rw [hshift]
  exact (hper.zsmul k (p 0)).trans (congrArg f hp)






theorem annulus_periodic_representative (p : LoopPlane) (hp : p 1 ∈ Icc (0 : ℝ) 1) :
    ∃ (k : ℤ) (q : LoopPlane), q ∈ m64AnnulusDomain ∧ q 0 < curvePeriod ∧
      q 1 = p 1 ∧ annulusPoint (k • curvePeriod) 0 + p = q := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let k := -toIcoDiv hP 0 (p 0)
  let q := annulusPoint (toIcoMod hP 0 (p 0)) (p 1)
  have hx := toIcoMod_mem_Ico' hP (p 0)
  refine ⟨k, q, ⟨hx.1, hx.2.le, hp.1, hp.2⟩, hx.2, rfl, ?_⟩
  ext i
  fin_cases i <;> simp [q, k, annulusPoint, toIcoMod, neg_smul, sub_eq_add_neg, add_comm]






theorem annulus_periodic_zero_on_strip
    {E Y : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    {f : LoopPlane → E} {u : LoopPlane → Y} {V : Set Y}
    (hfperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (huperiod : ∀ x s, u (annulusPoint (x + curvePeriod) s) = u (annulusPoint x s))
    (hW : IsOpen (m64AnnulusOpenStrip ∩ u ⁻¹' V))
    (hf : ContinuousOn f (m64AnnulusOpenStrip ∩ u ⁻¹' V))
    (heq : ∀ p ∈ m64AnnulusInterior, u p ∈ V → f p = 0) :
    ∀ p ∈ m64AnnulusOpenStrip, u p ∈ V → f p = 0 := by
  intro p hp hV
  obtain ⟨k, q, hq, -, hq1, hpoint⟩ := annulus_periodic_representative p ⟨hp.1.le, hp.2.le⟩
  have hqf := annulus_periodic_integer_translate hfperiod k p
  have hqu := annulus_periodic_integer_translate huperiod k p
  rw [hpoint] at hqf hqu
  let W := m64AnnulusOpenStrip ∩ u ⁻¹' V
  have hqW : q ∈ W := ⟨by change 0 < q 1 ∧ q 1 < 1; rw [hq1]; exact hp,
    by change u q ∈ V; rw [hqu]; exact hV⟩
  have hz : EqOn f (fun _ => 0) (W ∩ m64AnnulusInterior) :=
    fun z hz => heq z hz.2 hz.1.2
  have hz' : EqOn f (fun _ => 0) (W ∩ closure m64AnnulusInterior) :=
    hz.of_subset_closure (hf.mono inter_subset_left) continuousOn_const
      (inter_subset_inter Subset.rfl subset_closure) hW.inter_closure
  exact hqf.symm.trans (hz' ⟨hqW, by simpa only [m64AnnulusInterior_closure] using hq⟩)

end PoincareConjecture.M64
