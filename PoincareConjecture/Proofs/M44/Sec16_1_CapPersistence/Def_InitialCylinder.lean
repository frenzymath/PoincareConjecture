import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_OpenRegularCylinder
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Algebra.Order.Group.OrderIso

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

theorem exists_initial_based_cylinder
    (F : SurgeryFlowData.{u}) {origin scale B : ℝ}
    (hscale : 0 < scale) (hB : 0 < B)
    (htime : ∀ s ∈ Ico 0 B, origin + s / scale ∈ F.time_domain)
    (U : Set (F.slice origin).carrier) :
    ∃ c : ℝ, 0 < c ∧ c < B ∧
      ∃ e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U,
        ∀ h x, x ∈ U → HEq (e.forward 0 h x) x := by
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale hscale).trans (OrderIso.addLeft origin)
  have hzero : clock 0 = origin := by change origin + 0 / scale = origin; simp
  have horigin : origin ∈ F.time_domain := by simpa using htime 0 ⟨le_rfl, hB⟩
  have hBphysical : origin < clock B := hzero ▸ clock.strictMono hB
  obtain ⟨b, h0b, hbB, hfree⟩ := exists_surgery_free_right_interval F horigin hBphysical
  let c := clock.symm b
  have hc : 0 < c := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [c, hzero, OrderIso.apply_symm_apply] using h0b
  have hcB : c < B := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [c, OrderIso.apply_symm_apply] using hbB
  have hbtime : b ∈ F.time_domain := by
    have h := htime c ⟨hc.le, hcB⟩
    change clock c ∈ F.time_domain at h
    simpa only [c, OrderIso.apply_symm_apply] using h
  have hJ : Ico origin b ⊆ F.time_domain :=
    Ico_subset_Icc_self.trans (F.time_domain_interval.out horigin hbtime)
  have hNo := hfree.mono_right Ioo_subset_Ioc_self
  have hclockTime (s : ℝ) (hs : s ∈ Ico 0 c) :
      origin + s / scale ∈ Ico origin b := by
    change clock s ∈ Ico origin b
    refine ⟨hzero ▸ clock.monotone hs.1, ?_⟩
    simpa only [c, OrderIso.apply_symm_apply] using clock.strictMono hs.2
  let e := F.regularCylinderIco hJ hNo hscale ordConnected_Ico hclockTime U
  refine ⟨c, hc, hcB, e, ?_⟩
  intro h x _
  exact F.regularCylinderIco_initial hJ hNo hscale ordConnected_Ico hclockTime U h x

end PoincareConjecture.M44
