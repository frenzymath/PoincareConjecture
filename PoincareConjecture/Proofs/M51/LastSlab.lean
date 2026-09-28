import PoincareConjecture.Proofs.M51.HalfOpenSlab
import PoincareConjecture.Definitions.M33BranchContinuation
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SurgeryFlowData

theorem lastStartOfFinite (F : SurgeryFlowData.{u}) {H : ℝ}
    (hD : F.time_domain = Ico 0 H) (hfinite : F.surgery_times.Finite) :
    ∃ a : ℝ, a ∈ F.time_domain ∧ (a = 0 ∨ a ∈ F.surgery_times) ∧ a < H ∧
      Ico a H ⊆ F.time_domain ∧ Disjoint F.surgery_times (Ioo a H) := by
  classical
  let s := insert 0 hfinite.toFinset
  have h0s : (0 : ℝ) ∈ s := Finset.mem_insert_self _ _
  let a := s.max' ⟨0, h0s⟩
  have ha : a ∈ s := Finset.max'_mem _ _
  have hchoice : a = 0 ∨ a ∈ F.surgery_times := by
    simpa only [s, Finset.mem_insert, Set.Finite.mem_toFinset] using ha
  have hamem : a ∈ F.time_domain :=
    hchoice.elim (fun h => h ▸ F.zero_mem) (fun h => F.surgery_times_subset h)
  have habounds : a ∈ Ico 0 H := hD ▸ hamem
  refine ⟨a, hamem, hchoice, habounds.2, ?_, ?_⟩
  · intro t ht
    rw [hD]
    exact ⟨habounds.1.trans ht.1, ht.2⟩
  · apply Set.disjoint_left.mpr
    intro t hts ht
    have hmem : t ∈ s := Finset.mem_insert_of_mem (hfinite.mem_toFinset.mpr hts)
    exact (Finset.le_max' _ _ hmem).not_gt ht.1

noncomputable def preterminalSlab (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3) {a H : ℝ}
    (ha : a ∈ F.time_domain) (hstart : a = 0 ∨ a ∈ F.surgery_times)
    (haH : a < H) (hI : Ico a H ⊆ F.time_domain)
    (hS : Disjoint F.surgery_times (Ioo a H))
    (hH : H ∉ F.time_domain) [Nonempty (F.slice a).carrier] :
    RepairedPreterminalSlab F H where
  start := a
  start_mem := ha
  start_lt := haH
  start_initial_or_surgery := hstart
  time_subset := hI
  surgery_free := hS
  flow := M51Slab.flow F haH hI hS
  identify := M51Slab.identify F haH hI hS
  initial_identify := M51Slab.initial_identify F haH hI hS
  metric_pullback := M51Slab.metric_pullback F haH hI hS
  transport_compatibility := M51Slab.transport_compatibility F haH hI hS
  curvature_unbounded := by
    intro L s hs
    obtain ⟨t, ht, x, hx⟩ := F.maximal_intervals a H ha hstart haH hI hS
      (Or.inr hH) L s hs
    have hta : t ∈ Ico a H := ⟨((le_max_left a s).trans_lt ht.1).le, ht.2⟩
    let e := M51Slab.identify F haH hI hS ⟨t, hta⟩
    have hmetric : MetricHomothety (M51Slab.metric F haH hI hS t) (F.metric t) e 1 := by
      intro y v w
      simpa only [one_mul] using M51Slab.metric_pullback F haH hI hS ⟨t, hta⟩ y v w
    have R := H13.metric_homothety _ _ _ (F.metric t) e 1 (by norm_num) hmetric
    have hnorm := R.curvature_norm_eq (M51Slab.connection F haH hI hS t)
      (F.connection t) (e.symm x)
    rw [e.apply_symm_apply, div_one] at hnorm
    exact ⟨t, ht, e.symm x, hx.trans_eq hnorm⟩

theorem lastSlabAlternative (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3) {H : ℝ}
    (hD : F.time_domain = Ico 0 H) (hfinite : F.surgery_times.Finite) :
    ∃ a : ℝ, a ∈ F.time_domain ∧ (a = 0 ∨ a ∈ F.surgery_times) ∧ a < H ∧
      Ico a H ⊆ F.time_domain ∧ Disjoint F.surgery_times (Ioo a H) ∧
      ((∀ t ∈ Ico a H, IsEmpty (F.slice t).carrier) ∨
        ∃ S : RepairedPreterminalSlab F H, S.start = a) := by
  classical
  obtain ⟨a, ha, hstart, haH, hI, hS⟩ := F.lastStartOfFinite hD hfinite
  refine ⟨a, ha, hstart, haH, hI, hS, ?_⟩
  cases isEmpty_or_nonempty (F.slice a).carrier with
  | inl hempty =>
    exact Or.inl (fun t ht => F.extinction_permanent a t ha (hI ht) ht.1 hempty)
  | inr hne =>
    let := hne
    have hH : H ∉ F.time_domain := by rw [hD]; exact fun h => h.2.false
    exact Or.inr ⟨F.preterminalSlab H13 ha hstart haH hI hS hH, rfl⟩

end PoincareConjecture.SurgeryFlowData
