import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.OrdinaryRestart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SurgeryFlowData

theorem exists_last_surgery_before (F : SurgeryFlowData.{u}) {b : ℝ}
    (hb : b ∈ F.surgery_times) :
    ∃ a : ℝ, a ∈ F.time_domain ∧ (a = 0 ∨ a ∈ F.surgery_times) ∧ a < b ∧
      Ico a b ⊆ F.time_domain ∧ Disjoint F.surgery_times (Ioo a b) := by
  have hbF := F.surgery_times_subset hb
  have hbpos : 0 < b := lt_of_le_of_ne (F.time_domain_nonnegative hbF)
    (fun h => F.zero_not_surgery (h ▸ hb))
  have htime : Icc 0 b ⊆ F.time_domain :=
    F.time_domain_interval.out F.zero_mem hbF
  let A : Set ℝ := insert 0 (F.surgery_times ∩ Ico 0 b)
  have hfin : A.Finite :=
    ((F.surgery_times_finite_on_compact isCompact_Icc htime).subset
      (inter_subset_inter_right _ Ico_subset_Icc_self)).insert 0
  have hne : A.Nonempty := ⟨0, mem_insert _ _⟩
  have ha := hne.csSup_mem hfin
  have hab : sSup A < b := (hfin.csSup_lt_iff hne).mpr (by
    intro x hx
    rcases hx with hx | hx
    · simpa only [hx] using hbpos
    · exact hx.2.2)
  have ha0 : 0 ≤ sSup A := le_csSup hfin.bddAbove (mem_insert _ _)
  refine ⟨sSup A, htime ⟨ha0, hab.le⟩, ?_, hab, ?_, ?_⟩
  · rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr ha.1
  · exact fun x hx => htime ⟨ha0.trans hx.1, hx.2.le⟩
  · apply disjoint_left.mpr
    intro s hs hsI
    have hsA : s ∈ A := Or.inr ⟨hs, ha0.trans hsI.1.le, hsI.2⟩
    exact (not_lt_of_ge (le_csSup hfin.bddAbove hsA)) hsI.1

theorem curvature_unbounded_before_surgery (F : SurgeryFlowData.{u}) {b : ℝ}
    (hb : b ∈ F.surgery_times) [Nonempty (F.slice b).carrier]
    (C s : ℝ) (hs : s < b) :
    ∃ t ∈ Ioo s b, ∃ x : (F.slice t).carrier,
      C < (F.connection t).curvatureTensorNorm x := by
  obtain ⟨a, ha, hstart, hab, htime, hfree⟩ := F.exists_last_surgery_before hb
  have : Nonempty (F.slice a).carrier := by
    by_contra hn
    let : IsEmpty (F.slice a).carrier := ⟨fun x => hn ⟨x⟩⟩
    exact (F.extinction_permanent a b ha (F.surgery_times_subset hb) hab.le inferInstance).false
      (Classical.choice (inferInstance : Nonempty (F.slice b).carrier))
  obtain ⟨t, ht, x, hx⟩ := F.maximal_intervals a b ha hstart hab htime hfree
    (Or.inl hb) C s hs
  exact ⟨t, ⟨(le_max_right a s).trans_lt ht.1, ht.2⟩, x, hx⟩

end PoincareConjecture.SurgeryFlowData

namespace PoincareConjecture.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)
  {T : ℝ} (hT : T ∈ F.surgery_times) (hTW : T ∈ W.interval)

theorem event_pre_surgery_free :
    Disjoint F.surgery_times
      (Ioo (@SurgeryFlowData.event F T hT (W.slice_nonempty T hTW)).tMinus T) := by
  let E := @SurgeryFlowData.event F T hT (W.slice_nonempty T hTW)
  have hstart : E.tMinus ∈ W.interval :=
    W.interval_connected.out W.zero_mem hTW ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩
  let : CompactSpace (F.slice E.tMinus).carrier :=
    isCompact_univ_iff.mp (F.slices_compact E.tMinus (W.time_subset hstart))
  apply disjoint_left.mpr
  intro b hb hbI
  have hbW : b ∈ W.interval :=
    W.interval_connected.out hstart hTW ⟨hbI.1.le, hbI.2.le⟩
  let : Nonempty (F.slice b).carrier := W.slice_nonempty b hbW
  obtain ⟨C, hC⟩ := OrdinaryRestart.curvature_bound_on_compact E.pre_flow
    (K := Icc E.tMinus b) isCompact_Icc (fun _ ht => ⟨ht.1, ht.2.trans_lt hbI.2⟩)
  obtain ⟨t, ht, x, hx⟩ := F.curvature_unbounded_before_surgery hb C E.tMinus hbI.1
  have htE : t ∈ Ico E.tMinus T := ⟨ht.1.le, ht.2.trans hbI.2⟩
  let y := (E.pre_identify ⟨t, htE⟩).symm x
  have hnorm := (E.pre_flow.connection t).curvatureTensorNorm_eq_of_local_isometry
    (F.connection t) isOpen_univ (E.pre_identify ⟨t, htE⟩).contMDiff.contMDiffOn
    (fun z _ v w => (E.pre_metric ⟨t, htE⟩ z v w).symm) (mem_univ y)
  rw [(E.pre_identify ⟨t, htE⟩).apply_symm_apply x] at hnorm
  exact (not_lt_of_ge (hnorm ▸ hC t ⟨ht.1.le, ht.2.le⟩ y)) hx

end PoincareConjecture.Surgery.RegularHistory
