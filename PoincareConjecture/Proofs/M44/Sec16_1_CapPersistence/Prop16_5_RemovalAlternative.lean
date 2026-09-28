import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalRestriction
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_PhysicalInitialChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall
import PoincareConjecture.Proofs.M36.ComparisonCovariantJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace




theorem singularMetricJetErrorSquared_eq_of_eventuallyEq
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    {B C : CovariantTensorEvaluation 3 E 2} {x : E}
    (hBC : ∀ᶠ y in 𝓝 x, B y = C y) (m : ℕ) :
    singularMetricJetErrorSquared g D B m x = singularMetricJetErrorSquared g D C m x := by
  have hdiff : ∀ᶠ y in 𝓝 x,
      (fun v => B y v - g.inner y (v 0) (v 1)) =
        (fun v => C y v - g.inner y (v 0) (v 1)) := by
    filter_upwards [hBC] with y hy
    rw [hy]
  unfold singularMetricJetErrorSquared
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold RiemannianMetric.tensorNorm
  rw [(M36.comparison_iteratedCovariantTensorDerivative_eventuallyEq D hdiff j).self_of_nhds]





theorem initial_comparison_of_enlarged_birth_chart
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {A R zeta : ℝ} (hA : 0 < A) (hAR : A ≤ R) (hRzeta : R < zeta⁻¹)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip (((F.event t hT).necks i).neck.scale) zeta)
    (hlink : ((F.event t hT).necks i).neck.epsilon ≤
      F.local_constants.comparison_delta zeta)
    (hball : Q.map '' F.standard_initial.metric.ball 0 A =
      ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
        (((F.event t hT).necks i).neck.scale * A))
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice t).carrier ∞)
    (hfsource : f.source = F.standard_initial.metric.ball 0 R)
    (hfmap : ∀ x, f x = (F.event t hT).local_embed i (Q.map x)) :
    ∃ initial : SurgeryCapInitialComparison F t hT i A,
      EqOn initial.chart f (F.standard_initial.metric.ball 0 A) ∧
      initial.chart '' F.standard_initial.metric.ball 0 A =
        (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
  classical
  let B := F.standard_initial.metric.ball 0 A
  have hsub : B ⊆ f.source := by
    rw [hfsource]
    exact fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hAR)
  have hzero : (0 : E) ∈ B := by
    change (0 : E) ∈ F.standard_initial.metric.ball 0 A
    rw [M36.standard_ball_eq_euclidean F.standard_initial hA]
    exact Metric.mem_ball_self ((M36.radialEuclideanRadius_pos_iff F.standard_initial A).mpr hA)
  let chart : E → (F.slice t).carrier := fun x => if x ∈ B then f x else f 0
  have hchart (x : E) (hx : x ∈ B) : chart x = f x := if_pos hx
  have hrange : range chart = f '' B := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x ∈ B
      · exact ⟨x, hx, (hchart x hx).symm⟩
      · exact ⟨0, hzero, (if_neg hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hchart x hx⟩
  have htarget : range chart ⊆ f.target := by
    rw [hrange]
    rintro _ ⟨x, hx, rfl⟩
    exact f.map_source (hsub hx)
  have hAfit : A < zeta⁻¹ := hAR.trans_lt hRzeta
  have himage : f '' B =
      (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
    have hcompact := Q.isCompact_closure_image_ball hA hAfit
    rw [hball] at hcompact
    calc
      _ = (fun x => (F.event t hT).local_embed i (Q.map x)) '' B :=
        image_congr (fun x _ => hfmap x)
      _ = (F.event t hT).local_embed i '' (Q.map '' B) := (image_image _ _ _).symm
      _ = (F.event t hT).local_embed i ''
          ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
            (((F.event t hT).necks i).neck.scale * A) := congrArg _ hball
      _ = (F.metric t).ball ((F.event t hT).caps i).tip
          (((F.event t hT).necks i).neck.scale * A) :=
        local_result_ball_image F t hT i (mul_pos Q.scale_pos hA) hcompact
      _ = _ := by rw [(F.event t hT).neck_scale i, mul_comm]
  refine ⟨{
    A_pos := hA
    chart := chart
    inverse := f.symm
    chart_smooth := (f.contMDiffOn.mono hsub).congr hchart
    inverse_smooth := f.symm.contMDiffOn.mono htarget
    left_inverse := ?_
    right_inverse := ?_
    tip_eq := ?_
    local_metric_link := ?_ }, hchart, ?_⟩
  · intro x hx
    rw [hchart x hx]
    exact f.left_inv (hsub hx)
  · intro y hy
    rw [hrange] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (congrArg chart (f.left_inv (hsub hx))).trans (hchart x hx)
  · rw [hchart 0 hzero, hfmap, Q.map_tip, (F.event t hT).local_tip i]
  · refine ⟨zeta, Q.eta_pos, Q, hlink, ?_, ?_⟩
    · intro x hx
      exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith : A ≤ zeta⁻¹ + 1))
    · intro x hx
      exact (hchart x hx).trans (hfmap x)
  · exact (image_congr hchart).trans himage





theorem cap_persistence_alternative_of_enlarged_cylinder
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier]
    (i : Fin (F.event t hT).cap_count) {A R eta theta c zeta : ℝ}
    (hA : 0 < A) (hAR : A ≤ R) (hRzeta : R < zeta⁻¹) (htheta : theta < 1)
    (hc : 0 < c) (hcB : c ≤ surgeryCapDuration t O.H (F.parameters.h t) theta)
    (outer : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) (Ico 0 c)
      ((F.metric t).ball ((F.event t hT).caps i).tip (F.parameters.h t * R)))
    (hinitial : ∀ hs x,
      x ∈ (F.metric t).ball ((F.event t hT).caps i).tip (F.parameters.h t * R) →
        HEq (outer.forward 0 hs x) x)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip (((F.event t hT).necks i).neck.scale) zeta)
    (hlink : ((F.event t hT).necks i).neck.epsilon ≤
      F.local_constants.comparison_delta zeta)
    (hballs : ∀ r : ℝ, 0 < r → r ≤ zeta⁻¹ →
      Q.map '' F.standard_initial.metric.ball 0 r =
        ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
          (((F.event t hT).necks i).neck.scale * r))
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice t).carrier ∞)
    (hfsource : f.source = F.standard_initial.metric.ball 0 R)
    (hfmap : ∀ x, f x = (F.event t hT).local_embed i (Q.map x))
    (hlife : O.standard_flow.base.lifetime = 1)
    (hjets : ∃ bound : ℝ, bound < eta ^ 2 ∧
      ∀ s (hs : s ∈ Ico (0 : ℝ) c), ∀ x ∈ F.standard_initial.metric.ball 0 A,
        singularMetricJetErrorSquared (O.standard_flow.metric s) (O.standard_flow.connection s)
          (fun y v => outer.pullbackInner s hs (f y)
            (mfderiv (𝓡 3) (𝓡 3) f y (v 0))
            (mfderiv (𝓡 3) (𝓡 3) f y (v 1))) ⌊eta⁻¹⌋₊ x ≤ bound)
    (hstop : c = surgeryCapDuration t O.H (F.parameters.h t) theta ∨
      t + c / ((F.parameters.h t)⁻¹ ^ 2) ∈ F.surgery_times ∧
      SurgeryBallDisappearsAt F outer (t + c / ((F.parameters.h t)⁻¹ ^ 2))) :
    SurgeryCapPersistenceAlternative F O t hT i A eta theta := by
  have hh := F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hsmall : (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) ⊆
      (F.metric t).ball ((F.event t hT).caps i).tip (F.parameters.h t * R) := by
    intro x hx
    apply hx.trans_le (ENNReal.ofReal_le_ofReal _)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hAR hh.le
  let small := restrictCylinderSource outer hsmall
  have hinitialSmall : ∀ hs x,
      x ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) →
        HEq (small.forward 0 hs x) x := fun hs x hx => hinitial hs x (hsmall hx)
  obtain ⟨initial, hchart, himage⟩ := initial_comparison_of_enlarged_birth_chart
    F t hT i hA hAR hRzeta Q hlink (hballs A hA (hAR.trans hRzeta.le)) f hfsource hfmap
  have hopen : IsOpen (F.standard_initial.metric.ball 0 A) := by
    rw [M36.standard_ball_eq_euclidean F.standard_initial hA]
    exact Metric.isOpen_ball
  obtain ⟨bound, hbound, hjet⟩ := hjets
  have hcomparison : SurgeryCapFamilyComparison F O.standard_flow A eta small initial.chart := by
    refine ⟨bound, hbound, hlife, ?_, himage, ?_⟩
    · intro s hs
      rw [hlife]
      exact surgeryCap_model_time_mem hh htheta ⟨hs.1, hs.2.trans_le hcB⟩
    · intro s hs x hx
      have heq : initial.chart =ᶠ[𝓝 x] f := eventually_of_mem (hopen.mem_nhds hx) hchart
      have hfield : ∀ᶠ y in 𝓝 x,
          (fun (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          small.pullbackInner s hs (initial.chart y)
          (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 0))
          (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 1))) =
          (fun (v : Fin 2 → TangentSpace (𝓡 3) y) => outer.pullbackInner s hs (f y)
            (mfderiv (𝓡 3) (𝓡 3) f y (v 0))
            (mfderiv (𝓡 3) (𝓡 3) f y (v 1))) := by
        filter_upwards [heq.eventuallyEq_nhds] with y hy
        funext v
        rw [hy.mfderiv_eq, hy.self_of_nhds]
        rfl
      rw [singularMetricJetErrorSquared_eq_of_eventuallyEq _ _ hfield]
      exact hjet s hs x hx
  by_cases hceq : c = surgeryCapDuration t O.H (F.parameters.h t) theta
  · subst c
    exact Or.inl ⟨small, initial, hcomparison, hinitialSmall⟩
  · have hclt : c < surgeryCapDuration t O.H (F.parameters.h t) theta :=
      lt_of_le_of_ne hcB hceq
    obtain ⟨hPlus, hremove⟩ := hstop.resolve_left hceq
    let tPlus := t + c / ((F.parameters.h t)⁻¹ ^ 2)
    have htPlus : t < tPlus := lt_add_of_pos_right t (div_pos hc outer.scale_pos)
    have hbefore : tPlus < surgeryCapEnd t O.H (F.parameters.h t) theta :=
      (surgeryCap_physical_time_mem hh ⟨hc.le, hclt⟩).2
    have hduration : (tPlus - t) / (F.parameters.h t) ^ 2 = c := by
      dsimp only [tPlus]
      rw [surgeryCap_physical_time]
      field_simp [hh.ne']
      ring
    refine Or.inr ⟨tPlus, htPlus, hPlus, hbefore, ?_⟩
    rw [hduration]
    exact ⟨small, initial, hcomparison, hinitialSmall, disappears_restrict_source hremove hsmall⟩

end PoincareConjecture.M44
