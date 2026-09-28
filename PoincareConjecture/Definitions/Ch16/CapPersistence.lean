import PoincareConjecture.Definitions.Ch16.ControlledSurgery

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure SurgeryCapInitialComparison (F : SurgeryFlowData.{u})
    (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier]
    (i : Fin (F.event t hT).cap_count) (A : ℝ) where
  A_pos : 0 < A
  chart : StandardCapSpace → (F.slice t).carrier
  inverse : (F.slice t).carrier → StandardCapSpace
  chart_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ chart
    (F.standard_initial.metric.ball 0 A)
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse (Set.range chart)
  left_inverse : Set.LeftInvOn inverse chart (F.standard_initial.metric.ball 0 A)
  right_inverse : Set.LeftInvOn chart inverse (Set.range chart)
  tip_eq : chart 0 = ((F.event t hT).caps i).tip
  local_metric_link : ∃ eta : ℝ, 0 < eta ∧
    ∃ Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output
      ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip
      (((F.event t hT).necks i).neck.scale) eta,
      ((F.event t hT).necks i).neck.epsilon ≤
        F.local_constants.comparison_delta eta ∧
      F.standard_initial.metric.ball 0 A ⊆
        F.standard_initial.metric.ball 0 (eta⁻¹ + 1) ∧
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        chart x = (F.event t hT).local_embed i (Q.map x)





def SurgeryCapFamilyComparison (F : SurgeryFlowData.{u})
    (S : MaximalStandardCapFlow F.standard_initial) (A eta : ℝ)
    {t : ℝ} {I : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (chart : StandardCapSpace → (F.slice t).carrier) : Prop :=
  ∃ bound : ℝ, bound < eta ^ 2 ∧
    S.base.lifetime = 1 ∧
    (∀ (s : ℝ) (_hs : s ∈ I), s ∈ Set.Ico 0 S.base.lifetime) ∧
    chart '' F.standard_initial.metric.ball 0 A = U ∧
    ∀ (s : ℝ) (hs : s ∈ I) (x : StandardCapSpace),
      x ∈ F.standard_initial.metric.ball 0 A →
      singularMetricJetErrorSquared (S.metric s) (S.connection s)
        (fun y v => e.pullbackInner s hs (chart y)
          (mfderiv (𝓡 3) (𝓡 3) chart y (v 0))
          (mfderiv (𝓡 3) (𝓡 3) chart y (v 1)))
        ⌊eta⁻¹⌋₊ x ≤ bound

noncomputable def surgeryCapEnd (t H h theta : ℝ) : ℝ := min H (t + theta * h ^ 2)

noncomputable def surgeryCapDuration (t H h theta : ℝ) : ℝ :=
  (surgeryCapEnd t H h theta - t) / h ^ 2

def SurgeryBallDisappearsAt (F : SurgeryFlowData.{u})
    {origin scale : ℝ} {I : Set ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (tPlus : ℝ) : Prop :=
  IsEmpty (F.slice tPlus).carrier ∨
    ∃ (hPlus : tPlus ∈ F.surgery_times) (_hn : Nonempty (F.slice tPlus).carrier),
      (∀ h x, x ∈ U → HEq (e.forward 0 h x) x) ∧
      ∃ s0 : ℝ, s0 ∈ I ∧
        ∀ (s : ℝ) (hs : s ∈ I), s0 ≤ s →
          ∀ (x : (F.slice origin).carrier) (_hx : x ∈ U)
            (ht : origin + s / scale ∈ Set.Ico (F.event tPlus hPlus).tMinus tPlus),
            ((F.event tPlus hPlus).pre_identify
              ⟨origin + s / scale, ht⟩).symm
              (e.forward s hs x) ∉
                interior (F.event tPlus hPlus).retained_pre

def SurgeryCapPersistenceAlternative (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (A eta theta : ℝ) : Prop :=
  (∃ e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
      (Set.Ico 0 (surgeryCapDuration t O.H (F.parameters.h t) theta))
      ((F.metric t).ball ((F.event t hT).caps i).tip
        (A * F.parameters.h t)),
    ∃ initial : SurgeryCapInitialComparison F t hT i A,
      SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart ∧
      ∀ h x, x ∈ (F.metric t).ball ((F.event t hT).caps i).tip
        (A * F.parameters.h t) → HEq (e.forward 0 h x) x) ∨
  ∃ tPlus : ℝ, t < tPlus ∧
    tPlus ∈ F.surgery_times ∧
    tPlus < surgeryCapEnd t O.H (F.parameters.h t) theta ∧
    ∃ e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
      (Set.Ico 0 ((tPlus - t) / (F.parameters.h t) ^ 2))
      ((F.metric t).ball ((F.event t hT).caps i).tip
        (A * F.parameters.h t)),
      ∃ initial : SurgeryCapInitialComparison F t hT i A,
        SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart ∧
        (∀ h x, x ∈ (F.metric t).ball ((F.event t hT).caps i).tip
          (A * F.parameters.h t) → HEq (e.forward 0 h x) x) ∧
      SurgeryBallDisappearsAt F e tPlus

end PoincareConjecture
