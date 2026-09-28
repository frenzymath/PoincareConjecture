import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcReparametrization
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_exists_arc_parameter
    {gamma eta : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b : ℝ}
    (hinj : InjOn gamma (Icc a b))
    (hregular : ∀ p ∈ Icc a b, deriv gamma p ≠ 0)
    (heta : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ eta t)
    (hetainj : InjOn eta (Icc (0 : ℝ) 1))
    (hetaregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv eta t ≠ 0)
    (himage : eta '' Icc (0 : ℝ) 1 ⊆ gamma '' Icc a b) :
    ∃ phi : ℝ → ℝ,
      ContinuousOn phi (Icc (0 : ℝ) 1) ∧
      MapsTo phi (Icc (0 : ℝ) 1) (Icc a b) ∧
      EqOn eta (gamma ∘ phi) (Icc (0 : ℝ) 1) ∧
      InjOn phi (Icc (0 : ℝ) 1) ∧
      (StrictMonoOn phi (Icc (0 : ℝ) 1) ∨ StrictAntiOn phi (Icc (0 : ℝ) 1)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ ∞ phi t ∧ deriv phi t ≠ 0) ∧
      phi '' Icc (0 : ℝ) 1 = Icc (min (phi 0) (phi 1)) (max (phi 0) (phi 1)) ∧
      phi '' Ioo (0 : ℝ) 1 = Ioo (min (phi 0) (phi 1)) (max (phi 0) (phi 1)) := by
  let phi : ℝ → ℝ := fun t => Function.invFunOn gamma (Icc a b) (eta t)
  have hpre (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∃ p ∈ Icc a b, gamma p = eta t := himage ⟨t, ht, rfl⟩
  have hmap : MapsTo phi (Icc (0 : ℝ) 1) (Icc a b) :=
    fun t ht => Function.invFunOn_mem (hpre t ht)
  have heq : EqOn eta (gamma ∘ phi) (Icc (0 : ℝ) 1) :=
    fun t ht => (Function.invFunOn_eq (hpre t ht)).symm
  let H : Icc a b ≃ₜ gamma '' Icc a b :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn gamma (Icc a b) hinj)
      ((hg.continuous.comp continuous_subtype_val).subtype_mk _)
  let etaImage : Icc (0 : ℝ) 1 → gamma '' Icc a b :=
    fun t => ⟨eta t, himage ⟨t, t.property, rfl⟩⟩
  have hetaCont : ContinuousOn eta (Icc (0 : ℝ) 1) :=
    fun t ht => (heta t ht).continuousAt.continuousWithinAt
  have hetaImage : Continuous etaImage := hetaCont.domRestrict.subtype_mk _
  have hphiEq (t : Icc (0 : ℝ) 1) : phi t = (H.symm (etaImage t)).val := by
    apply hinj (hmap t.property) (H.symm (etaImage t)).property
    have hH := congrArg Subtype.val (H.apply_symm_apply (etaImage t))
    exact (heq t.property).symm.trans hH.symm
  have hcont : ContinuousOn phi (Icc (0 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hfun : (Icc (0 : ℝ) 1).domRestrict phi =
        fun t => (H.symm (etaImage t)).val := funext hphiEq
    rw [hfun]
    exact continuous_subtype_val.comp (H.symm.continuous.comp hetaImage)
  have hphiinj : InjOn phi (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    apply hetainj hs ht
    exact (heq hs).trans ((congrArg gamma hst).trans (heq ht).symm)
  have horder : StrictMonoOn phi (Icc (0 : ℝ) 1) ∨
      StrictAntiOn phi (Icc (0 : ℝ) 1) :=
    hcont.strictMonoOn_of_injOn_Icc' zero_le_one hphiinj
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hinside (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : phi t ∈ Ioo a b := by
    have ht' := Ioo_subset_Icc_self ht
    rcases horder with hmono | hanti
    · exact ⟨(hmap hzero).1.trans_lt (hmono hzero ht' ht.1),
        (hmono ht' hone ht.2).trans_le (hmap hone).2⟩
    · exact ⟨(hmap hone).1.trans_lt (hanti ht' hone ht.2),
        (hanti hzero ht' ht.1).trans_le (hmap hzero).2⟩
  have hsmooth (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ phi t ∧ deriv phi t ≠ 0 := by
    have ht' := Ioo_subset_Icc_self ht
    obtain ⟨psi, hpsi, hpsit, hpsid, hlocal⟩ :=
      m64Intrinsic_exists_local_arc_reparametrization hg hinj (hmap ht')
        (hregular _ (hmap ht')) (heta t ht') (heq ht')
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
          (fun s hs => himage ⟨s, Ioo_subset_Icc_self hs, rfl⟩))
        (hetaregular t ht')
    have hpsiInside : psi t ∈ Ioo a b := by rw [hpsit]; exact hinside t ht
    have hagree : phi =ᶠ[𝓝 t] psi := by
      filter_upwards [isOpen_Ioo.mem_nhds ht, hlocal,
        hpsi.continuousAt.eventually (isOpen_Ioo.mem_nhds hpsiInside)] with s hs he hps
      exact hinj (hmap (Ioo_subset_Icc_self hs)) (Ioo_subset_Icc_self hps)
        ((heq (Ioo_subset_Icc_self hs)).symm.trans he)
    refine ⟨hpsi.congr_of_eventuallyEq hagree, ?_⟩
    rw [hagree.deriv_eq]
    exact hpsid
  have himages :
      phi '' Icc (0 : ℝ) 1 = Icc (min (phi 0) (phi 1)) (max (phi 0) (phi 1)) ∧
      phi '' Ioo (0 : ℝ) 1 = Ioo (min (phi 0) (phi 1)) (max (phi 0) (phi 1)) := by
    rcases horder with hmono | hanti
    · have hle := hmono.monotoneOn hzero hone zero_le_one
      rw [min_eq_left hle, max_eq_right hle]
      exact ⟨hcont.image_Icc_of_monotoneOn zero_le_one hmono.monotoneOn,
        hcont.image_Ioo_of_strictMonoOn zero_le_one hmono⟩
    · have hle := hanti.antitoneOn hzero hone zero_le_one
      rw [min_eq_right hle, max_eq_left hle]
      exact ⟨hcont.image_Icc_of_antitoneOn zero_le_one hanti.antitoneOn,
        hcont.image_Ioo_of_strictAntiOn zero_le_one hanti⟩
  exact ⟨phi, hcont, hmap, heq, hphiinj, horder, hsmooth, himages⟩

end PoincareConjecture
