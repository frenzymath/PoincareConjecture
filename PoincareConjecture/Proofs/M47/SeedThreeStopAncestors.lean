import PoincareConjecture.Proofs.M47.SeedSearchAncestors
import PoincareConjecture.Proofs.M47.SeedSearchBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47



theorem seed_search_before_birth_nonpositive
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {J : Set ℝ}
    (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {origin c : ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hc : c ≤ 0) (horigin : origin ∈ J)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (q : (F.slice origin).carrier) (hcomponent : U ⊆ connectedComponent q)
    (hbirth : ¬ SurgeryPositiveComponentAt F origin q ∨
      ∃ hT : origin ∈ F.surgery_times,
        ∀ [Nonempty (F.slice origin).carrier],
          ∃ i : Fin (F.event origin hT).cap_count,
            (connectedComponent q ∩ ((F.event origin hT).caps i).carrier).Nonempty)
    (s : ℝ) (hs : s ∈ Icc c 0) (hs0 : s < 0)
    (x : (F.slice origin).carrier) (hx : x ∈ U) :
    ¬ SurgeryPositiveComponentAt F (origin + s / 1) (e.forward s hs x) := by
  let Birth : (t : ℝ) → (F.slice t).carrier → Prop := fun t y =>
    ¬ SurgeryPositiveComponentAt F t y ∨
      ∃ hT : t ∈ F.surgery_times, ∀ [Nonempty (F.slice t).carrier],
        ∃ i : Fin (F.event t hT).cap_count,
          (connectedComponent y ∩ ((F.event t hT).caps i).carrier).Nonempty
  have hbirthx : Birth origin x := by
    rcases hbirth with hnot | ⟨hT, hcap⟩
    · exact Or.inl (not_positive_of_mem_component hnot (hcomponent hx))
    · right
      refine ⟨hT, ?_⟩
      intro hn
      obtain ⟨i, hi⟩ := hcap
      exact ⟨i, by simpa only [connectedComponent_eq (hcomponent hx)] using hi⟩
  have hzero : 0 ∈ Icc c 0 := ⟨hc, le_rfl⟩
  have hpoint : (⟨origin + 0 / 1, e.forward 0 hzero x⟩ :
      (t : ℝ) × (F.slice t).carrier) = ⟨origin, x⟩ := by
    apply Sigma.ext (by simp)
    exact hbase hzero x hx
  have hterminal : Birth (origin + 0 / 1) (e.forward 0 hzero x) :=
    (congrArg (fun z : (t : ℝ) × (F.slice t).carrier => Birth z.1 z.2) hpoint).mpr hbirthx
  rcases hterminal with hnot | ⟨hT, hcap⟩
  · exact seed_search_nonpositive_of_endpoint e hx hs hzero hs0.le hnot
  · let : Nonempty (F.slice (origin + 0 / 1)).carrier := ⟨e.forward 0 hzero x⟩
    obtain ⟨i, hi⟩ := hcap
    exact seed_search_nonpositive_of_cap_endpoint P.m04 hpolicy e hx hs hzero hs0
      (by simpa only [zero_div, add_zero] using horigin) hT hi



theorem seed_search_bounds_of_birth
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hpinch : SurgeryFlowPinched F)
    (hpolicy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    {origin c H B : ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hc : c ≤ 0) (hbottom : 0 ≤ origin + c)
    (horigin : origin ∈ surgeryObservationInterval O ∩ prefixFinalInterval p)
    (hH : 0 < H) (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H)
    (hB : M46.seedAnalyticConstant S ≤ B)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (q : (F.slice origin).carrier) (hcomponent : U ⊆ connectedComponent q)
    (hbirth : ¬ SurgeryPositiveComponentAt F origin q ∨
      ∃ hT : origin ∈ F.surgery_times,
        ∀ [Nonempty (F.slice origin).carrier],
          ∃ i : Fin (F.event origin hT).cap_count,
            (connectedComponent q ∩ ((F.event origin hT).caps i).carrier).Nonempty)
    (hinitial : ∀ x ∈ U, (F.connection origin).scalarCurvature x ≤ 2 * H)
    (hshort : 64 * B * H * (-c) ≤ 1) :
    ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U,
      (F.connection (origin + s / 1)).scalarCurvature (e.forward s hs x) ≤ 4 * H ∧
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤
        13 * max (4 * H) (Real.exp 4) := by
  apply seed_search_scalar_and_curvature P S p compatible old hpinch e hc hH hlevel hB
    hbase hinitial ?_ ?_ hshort
  · intro s hs
    rcases horigin with ⟨horigin, hprefix⟩
    change 0 ≤ origin ∧ origin < O.H at horigin
    change 0 ≤ origin ∧ origin < surgeryEpochStart p.i at hprefix
    change (0 ≤ origin + s / 1 ∧ origin + s / 1 < O.H) ∧
      (0 ≤ origin + s / 1 ∧ origin + s / 1 < surgeryEpochStart p.i)
    simp only [div_one]
    constructor
    · constructor
      · linarith [hs.1]
      · linarith [hs.2, horigin.2]
    · constructor
      · linarith [hs.1]
      · linarith [hs.2, hprefix.2]
  · intro s hs x hx
    exact seed_search_before_birth_nonpositive P hpolicy e hc horigin.1 hbase q hcomponent
      hbirth s (Ioo_subset_Icc_self hs) hs.2 x hx

end PoincareConjecture.Proofs.M47
