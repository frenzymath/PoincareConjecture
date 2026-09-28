import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M33.RegularHistory
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_BackwardFiniteEvents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem seedM15_cylinder_eq_of_terminal
    {F : SurgeryFlowData.{u}} {C D : GeneralizedSliceCarrier.{u}}
    {origin a : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}
    (e : SurgeryFlowCylinder F C origin 1 I U)
    (f : SurgeryFlowCylinder F D origin 1 J V)
    (ha : a ≤ 0) (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J)
    (x : C.carrier) (hx : x ∈ U) (y : D.carrier) (hy : y ∈ V)
    (hterminal : e.forward 0 (hI ⟨ha, le_rfl⟩) x =
      f.forward 0 (hJ ⟨ha, le_rfl⟩) y) :
    e.forward a (hI ⟨le_rfl, ha⟩) x = f.forward a (hJ ⟨le_rfl, ha⟩) y := by
  classical
  let events : Set ℝ := (fun s : ℝ => origin + s / 1) ⁻¹' F.surgery_times
  let Q : ℝ → Prop := fun s => ∀ hs : s ∈ Icc a 0,
    e.forward s (hI hs) x = f.forward s (hJ hs) y
  have hclock : StrictMono (fun s : ℝ => origin + s / 1) := by
    intro s t hst
    simpa only [div_one, add_comm] using add_lt_add_left hst origin
  have htime : Icc (origin + a / 1) (origin + 0 / 1) ⊆ F.time_domain :=
    F.time_domain_interval.out
      (e.time_subset (mem_image_of_mem _ (hI ⟨le_rfl, ha⟩)))
      (e.time_subset (mem_image_of_mem _ (hI ⟨ha, le_rfl⟩)))
  have hfinite : (events ∩ Ioc a 0).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc htime
    apply (hf.preimage hclock.injective.injOn).subset
    intro s hs
    exact ⟨hs.1, hclock.monotone hs.2.1.le, hclock.monotone hs.2.2⟩
  have hQa : Q a := by
    apply Proofs.M46.backward_cylinder_finite_event_induction ha hfinite Q
      (fun _ => hterminal)
    · intro s hs t ht hst hfree hQt hsQ
      rcases lt_or_eq_of_le hst with hst | rfl
      · have hsmall : Icc (origin + s / 1) (origin + t / 1) ⊆ F.time_domain := by
          intro z hz
          exact htime ⟨(hclock.monotone hs.1).trans hz.1,
            hz.2.trans (hclock.monotone ht.2)⟩
        have hfree' : Disjoint F.surgery_times
            (Ioc (origin + s / 1) (origin + t / 1)) := by
          apply Set.disjoint_left.mpr
          intro z hz hzI
          have hze : z - origin ∈ events := by
            simpa only [events, mem_preimage, div_one, add_sub_cancel] using hz
          exact Set.disjoint_left.mp hfree hze
            (by simp only [div_one] at hzI; constructor <;> linarith [hzI.1, hzI.2])
        let S := F.regular_slabs _ _ (hclock hst) hsmall hfree'
        let ts : Icc (origin + s / 1) (origin + t / 1) :=
          ⟨origin + s / 1, ⟨le_rfl, (hclock hst).le⟩⟩
        let tt : Icc (origin + s / 1) (origin + t / 1) :=
          ⟨origin + t / 1, ⟨(hclock hst).le, le_rfl⟩⟩
        have he := e.slab_compatibility _ _ (hclock hst) hsmall hfree'
          s (hI hsQ) t (hI ht) ts.property tt.property x hx
        have hf := f.slab_compatibility _ _ (hclock hst) hsmall hfree'
          s (hJ hsQ) t (hJ ht) ts.property tt.property y hy
        have heq : S.transport ts tt (e.forward s (hI hsQ) x) =
            S.transport ts tt (f.forward s (hJ hsQ) y) := he.trans ((hQt ht).trans hf.symm)
        exact (S.identify ts).symm.injective ((S.identify tt).injective heq)
      · exact hQt hsQ
    · intro c hc hQc
      have hcI : c ∈ Icc a 0 := ⟨hc.2.1.le, hc.2.2⟩
      have hT : origin + c / 1 ∈ F.surgery_times := hc.1
      let : Nonempty (F.slice (origin + c / 1)).carrier := ⟨e.forward c (hI hcI) x⟩
      let event := F.event (origin + c / 1) hT
      let d := max a (event.tMinus - origin)
      have had : a ≤ d := le_max_left _ _
      have hdc : d < c := by
        apply max_lt hc.2.1
        have h := event.tMinus_lt
        simp only [div_one] at h
        linarith
      have hdpre : origin + d / 1 ∈ Ico event.tMinus (origin + c / 1) := by
        refine ⟨?_, hclock hdc⟩
        have h := le_max_right a (event.tMinus - origin)
        dsimp only [d]
        simp only [div_one]
        linarith
      refine ⟨d, ⟨had, hdc.le⟩, hdc, ?_⟩
      intro hdQ
      have he := e.surgery_compatibility c (hI hcI) hT d (hI hdQ) hdpre x hx
      have hf := f.surgery_compatibility c (hJ hcI) hT d (hJ hdQ) hdpre y hy
      have hepre := e.pre_retained_at_surgery c (hI hcI) hT d (hI hdQ) hdpre x hx
      have hfpre := f.pre_retained_at_surgery c (hJ hcI) hT d (hJ hdQ) hdpre y hy
      have heq := congrArg event.retention.inverse (he.trans ((hQc hcI).trans hf.symm))
      rw [event.retention.left_inverse (interior_subset hepre),
        event.retention.left_inverse (interior_subset hfpre)] at heq
      exact (event.pre_identify ⟨origin + d / 1, hdpre⟩).symm.injective heq
  exact hQa ⟨le_rfl, ha⟩

end PoincareConjecture.M47
