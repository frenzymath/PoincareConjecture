import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace IsCoveringMap

theorem exists_two_sheet_involution
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p)
    (hcard : ∀ x : X, (p ⁻¹' {x}).ncard = 2) :
    ∃ T : E ≃ₜ E, (∀ e, p (T e) = p e) ∧
      (∀ e, T (T e) = e) ∧ ∀ e, T e ≠ e := by
  classical
  have hother (e : E) : ∃! d : E, p d = p e ∧ d ≠ e := by
    obtain ⟨a, b, hab, hfiber⟩ := ncard_eq_two.mp (hcard (p e))
    have ha : p a = p e := by
      have h : a ∈ p ⁻¹' {p e} := hfiber.symm ▸ (by simp)
      exact h
    have hb : p b = p e := by
      have h : b ∈ p ⁻¹' {p e} := hfiber.symm ▸ (by simp)
      exact h
    have he : e = a ∨ e = b := by
      have h : e ∈ ({a, b} : Set E) := hfiber ▸ (show e ∈ p ⁻¹' {p e} from rfl)
      simpa only [mem_insert_iff, mem_singleton_iff] using h
    have hmem (d : E) (hd : p d = p e) : d = a ∨ d = b := by
      have h : d ∈ ({a, b} : Set E) := hfiber ▸ (show d ∈ p ⁻¹' {p e} from hd)
      simpa only [mem_insert_iff, mem_singleton_iff] using h
    rcases he with he | he
    · refine ⟨b, ⟨hb, fun h => hab ((h.trans he).symm)⟩, ?_⟩
      intro d hd
      rcases hmem d hd.1 with hda | hdb
      · exact (hd.2 (hda.trans he.symm)).elim
      · exact hdb
    · refine ⟨a, ⟨ha, fun h => hab (h.trans he)⟩, ?_⟩
      intro d hd
      rcases hmem d hd.1 with hda | hdb
      · exact hda
      · exact (hd.2 (hdb.trans he.symm)).elim
  choose tau hspec huniq using hother
  have hinv (e : E) : tau (tau e) = e :=
    (huniq (tau e) e ⟨(hspec e).1.symm, (hspec e).2.symm⟩).symm
  have hcont : Continuous tau := by
    apply continuous_iff_continuousAt.mpr
    intro e
    obtain ⟨hdisc, U, heU, _, hpU, H, hH⟩ := hp (p e)
    let B := p ⁻¹' {p e}
    let : DiscreteTopology B := hdisc
    let tauB : B → B := fun b => ⟨tau b, (hspec (b : E)).1.trans b.property⟩
    have hBcont : Continuous tauB := continuous_of_discreteTopology
    let F : p ⁻¹' U → p ⁻¹' U := fun y => H.symm ((H y).1, tauB (H y).2)
    have hFcont : Continuous (fun y : p ⁻¹' U => (F y : E)) :=
      continuous_subtype_val.comp (H.symm.continuous.comp
        ((continuous_fst.prodMk (hBcont.comp continuous_snd)).comp H.continuous))
    have hHF (y : p ⁻¹' U) : H (F y) = ((H y).1, tauB (H y).2) :=
      H.apply_symm_apply _
    have hFp (y : p ⁻¹' U) : p (F y) = p y := by
      calc
        p (F y) = (H (F y)).1.1 := (hH (F y)).symm
        _ = (H y).1.1 := congrArg (fun z => z.1.1) (hHF y)
        _ = p y := hH y
    have hFne (y : p ⁻¹' U) : (F y : E) ≠ y := by
      intro heq
      have hy : F y = y := Subtype.ext heq
      have htag : tauB (H y).2 = (H y).2 := by
        simpa only [hHF y] using congrArg (fun z => (H z).2) hy
      exact (hspec ((H y).2 : E)).2 (congrArg Subtype.val htag)
    have hFtau (y : p ⁻¹' U) : (F y : E) = tau y :=
      huniq (y : E) (F y) ⟨hFp y, hFne y⟩
    have hlocal : Continuous (fun y : p ⁻¹' U => tau (y : E)) := hFcont.congr hFtau
    have hOn : ContinuousOn tau (p ⁻¹' U) :=
      continuousOn_iff_continuous_domRestrict.mpr hlocal
    exact hOn.continuousAt (hpU.mem_nhds heU)
  let T : E ≃ₜ E :=
    { toFun := tau
      invFun := tau
      left_inv := hinv
      right_inv := hinv
      continuous_toFun := hcont
      continuous_invFun := hcont }
  exact ⟨T, fun e => (hspec e).1, hinv, fun e => (hspec e).2⟩

end IsCoveringMap
