import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_PhysicalBirthChart











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem exists_cap_birth_chart_with_map
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {A kappa : ℝ} (hA : 0 < A) (hAkappa : A < kappa⁻¹)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip (((F.event t hT).necks i).neck.scale) kappa)
    (hdelta : ((F.event t hT).necks i).neck.epsilon ≤
      F.local_constants.comparison_delta kappa)
    (hball : Q.map '' F.standard_initial.metric.ball 0 A =
      ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
        (((F.event t hT).necks i).neck.scale * A)) :
    ∃ initial : SurgeryCapInitialComparison F t hT i A,
      initial.chart '' F.standard_initial.metric.ball 0 A =
        (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) ∧
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        initial.chart x = (F.event t hT).local_embed i (Q.map x) := by
  classical
  obtain ⟨q, hsource, hmap, htarget, _hconnected⟩ :=
    M44.exists_physical_birth_chart F t hT i hA hAkappa Q hball
  let B := F.standard_initial.metric.ball 0 A
  have hzero : (0 : StandardCapSpace) ∈ B := by
    change F.standard_initial.metric.edist 0 0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hA
  have hzeroSource : (0 : StandardCapSpace) ∈ q.source := hsource.symm ▸ hzero
  let chart : StandardCapSpace → (F.slice t).carrier :=
    fun x => if x ∈ B then q x else q 0
  have hchart (x : StandardCapSpace) (hx : x ∈ B) : chart x = q x := if_pos hx
  have hback (y : (F.slice t).carrier) (hy : y ∈ q.target) : q.symm y ∈ B := by
    change q.symm y ∈ F.standard_initial.metric.ball 0 A
    rw [← hsource]
    exact q.symm.map_source hy
  have hrange : range chart = q.target := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x ∈ B
      · rw [hchart x hx]
        exact q.map_source (hsource.symm ▸ hx)
      · change (if x ∈ B then q x else q 0) ∈ q.target
        rw [if_neg hx]
        exact q.map_source hzeroSource
    · intro hy
      exact ⟨q.symm y, (hchart _ (hback y hy)).trans (q.right_inv hy)⟩
  have hleft : LeftInvOn q.symm chart B := by
    intro x hx
    rw [hchart x hx]
    exact q.left_inv (hsource.symm ▸ hx)
  have hright : LeftInvOn chart q.symm (range chart) := by
    intro y hy
    have hyq : y ∈ q.target := hrange ▸ hy
    rw [hchart _ (hback y hyq)]
    exact q.right_inv hyq
  have himage : chart '' B = q.target := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hchart x hx]
      exact q.map_source (hsource.symm ▸ hx)
    · intro hy
      exact ⟨q.symm y, hback y hy,
        (hchart _ (hback y hy)).trans (q.right_inv hy)⟩
  let initial : SurgeryCapInitialComparison F t hT i A := {
    A_pos := hA
    chart := chart
    inverse := q.symm
    chart_smooth := (hsource ▸ q.contMDiffOn).congr hchart
    inverse_smooth := hrange.symm ▸ q.symm.contMDiffOn
    left_inverse := hleft
    right_inverse := hright
    tip_eq := by
      rw [hchart 0 hzero, hmap, Q.map_tip]
      exact (F.event t hT).local_tip i
    local_metric_link := by
      refine ⟨kappa, Q.eta_pos, Q, hdelta, ?_, ?_⟩
      · intro x hx
        exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hAkappa]))
      · intro x hx
        exact (hchart x hx).trans (hmap x) }
  refine ⟨initial, ?_, ?_⟩
  · change chart '' B = _
    rw [himage, htarget, mul_comm]
  · intro x hx
    exact (hchart x hx).trans (hmap x)

end PoincareConjecture.M47
