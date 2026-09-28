import PoincareConjecture.Proofs.M47.PositiveHistoryBirth










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_component_birth
    (F : SurgeryFlowData.{u}) {T : ℝ} (hT : T ∈ F.time_domain)
    (x : (F.slice T).carrier) :
    ∃ U : TopologicalSpace.Opens (F.slice T).carrier,
      (U : Set (F.slice T).carrier) = connectedComponent x ∧
      IsCompact (U : Set (F.slice T).carrier) ∧
      IsConnected (U : Set (F.slice T).carrier) ∧ x ∈ U ∧
      ∃ (b : ℝ) (hb : b ∈ Icc (-T) 0),
        ∃ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U,
          (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) ∧
          (T + b / 1 = 0 ∨ ∃ hbirth : T + b / 1 ∈ F.surgery_times,
            ∀ [Nonempty (F.slice (T + b / 1)).carrier],
              ∃ i : Fin (F.event (T + b / 1) hbirth).cap_count,
                (e.forward b ⟨le_rfl, hb.2⟩ ''
                  (U : Set (F.slice T).carrier) ∩
                    ((F.event (T + b / 1) hbirth).caps i).carrier).Nonempty) := by
  let : CompactSpace (F.slice T).carrier := isCompact_univ_iff.mp (F.slices_compact T hT)
  let : LocallyConnectedSpace (F.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  let U : TopologicalSpace.Opens (F.slice T).carrier :=
    ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hcompact : IsCompact (U : Set (F.slice T).carrier) := isClosed_connectedComponent.isCompact
  have hconnected : IsConnected (U : Set (F.slice T).carrier) := isConnected_connectedComponent
  have hnonnegative : 0 ≤ T := F.time_domain_nonnegative hT
  have htime : Icc (T + -T) T ⊆ F.time_domain := by
    simpa only [add_neg_cancel] using F.time_domain_interval.out F.zero_mem hT
  obtain ⟨b, hb, e, hbased, hstop⟩ := M47Positive.exists_component_birth_cylinder F
    (neg_nonpos.mpr hnonnegative) htime U U.isOpen hcompact hconnected
  refine ⟨U, rfl, hcompact, hconnected, mem_connectedComponent, b, hb, e, hbased, ?_⟩
  rcases hstop with hzero | hcap
  · exact Or.inl (by simp only [hzero, div_one, add_neg_cancel])
  · exact Or.inr hcap




theorem seed_singleton_component_birth_meets_cap
    {F : SurgeryFlowData.{u}} {T : ℝ} (hT : 0 < T)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc 0 0) U)
    (based : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hbirth : T + 0 / 1 = 0 ∨ ∃ hbirth : T + 0 / 1 ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (T + 0 / 1)).carrier],
        ∃ i : Fin (F.event (T + 0 / 1) hbirth).cap_count,
          (e.forward 0 ⟨le_rfl, le_rfl⟩ '' (U : Set (F.slice T).carrier) ∩
            ((F.event (T + 0 / 1) hbirth).caps i).carrier).Nonempty) :
    ∃ hbirth : T ∈ F.surgery_times,
      ∀ [Nonempty (F.slice T).carrier],
        ∃ i : Fin (F.event T hbirth).cap_count,
          ((U : Set (F.slice T).carrier) ∩ ((F.event T hbirth).caps i).carrier).Nonempty := by
  have hnotzero : T + 0 / 1 ≠ 0 := by simpa only [zero_div, add_zero] using hT.ne'
  have hcap := hbirth.resolve_left hnotzero
  have transfer (s : ℝ) (hs : s = T)
      (f : (F.slice T).carrier → (F.slice s).carrier)
      (hf : ∀ y ∈ U, HEq (f y) y)
      (hc : ∃ h : s ∈ F.surgery_times,
        ∀ [Nonempty (F.slice s).carrier], ∃ i : Fin (F.event s h).cap_count,
          (f '' (U : Set (F.slice T).carrier) ∩ ((F.event s h).caps i).carrier).Nonempty) :
      ∃ h : T ∈ F.surgery_times,
        ∀ [Nonempty (F.slice T).carrier], ∃ i : Fin (F.event T h).cap_count,
          ((U : Set (F.slice T).carrier) ∩ ((F.event T h).caps i).carrier).Nonempty := by
    subst s
    obtain ⟨h, hc⟩ := hc
    refine ⟨h, ?_⟩
    intro hn
    obtain ⟨i, z, ⟨y, hy, hzy⟩, hzcap⟩ := hc
    refine ⟨i, y, hy, ?_⟩
    have hyz : y = z := (eq_of_heq (hf y hy)).symm.trans hzy
    exact hyz.symm ▸ hzcap
  exact transfer _ (by simp only [zero_div, add_zero])
    (e.forward 0 ⟨le_rfl, le_rfl⟩) (based _) hcap

end PoincareConjecture.Proofs.M47
