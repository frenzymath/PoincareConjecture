import PoincareConjecture.Proofs.M47.ComponentEstimateScalarCeiling
import PoincareConjecture.Proofs.M47.ComponentEstimateMetric
import PoincareConjecture.Proofs.M47.ComponentEstimateDiameter
import PoincareConjecture.Proofs.M47.ComponentEstimateCapExclusion
import PoincareConjecture.Proofs.M47.ComponentEstimateBackward
import PoincareConjecture.Proofs.M47.ComponentHistory











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

private theorem terminal_scalar_eq
    {F : SurgeryFlowData.{u}} {origin : ℝ}
    {U : Set (F.slice origin).carrier} {I : Set ℝ}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 I U) (hzero : 0 ∈ I)
    (he : ∀ y ∈ U, HEq (e.forward 0 hzero y) y)
    {y : (F.slice origin).carrier} (hy : y ∈ U) :
    (F.connection (origin + 0 / 1)).scalarCurvature (e.forward 0 hzero y) =
      (F.connection origin).scalarCurvature y := by
  have hp : (⟨origin + 0 / 1, e.forward 0 hzero y⟩ :
      (t : ℝ) × (F.slice t).carrier) = ⟨origin, y⟩ := by
    apply Sigma.ext (by simp)
    exact he y hy
  have hvalue := congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
    (F.connection p.1).scalarCurvature p.2) hp
  exact hvalue

private theorem terminal_diameter_eq
    {F : SurgeryFlowData.{u}} {origin : ℝ}
    {U : Set (F.slice origin).carrier} {I : Set ℝ}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 I U) (hzero : 0 ∈ I)
    (he : ∀ y ∈ U, HEq (e.forward 0 hzero y) y) :
    intrinsicDiameter (F.metric (origin + 0 / 1)) (e.forward 0 hzero '' U) =
      intrinsicDiameter (F.metric origin) U := by
  have hfunctions :
      (⟨origin + 0 / 1, fun y : U => e.forward 0 hzero y.val⟩ :
        (t : ℝ) × (U → (F.slice t).carrier)) =
          ⟨origin, (Subtype.val : U → (F.slice origin).carrier)⟩ := by
    apply Sigma.ext (by simp)
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    exact he y.val y.property
  have hdiam := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
    intrinsicDiameter (F.metric p.1) (range p.2)) hfunctions
  simpa only [← image_eq_range, Subtype.range_val_subtype, ofPred_mem_eq] using hdiam




theorem exists_component_backward_duration
    (P : M47Predecessors.{u}) (PA : M47ComponentAnalyticPredecessors.{u})
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∃ delta : StandardInitialMetric → MetricSurgeryConstants → ℝ,
        (∀ g₀ K, 0 < delta g₀ K) ∧
        ∀ (F : SurgeryFlowData.{u}) (origin Q : ℝ) (x : (F.slice origin).carrier),
          (F.connection origin).scalarCurvature x = Q → 6 ≤ Q → Real.exp 4 ≤ Q →
          Icc (origin - d / Q) origin ⊆ F.time_domain →
          (∀ t ∈ Icc (origin - d / Q) origin, SurgeryPinchedAt (F.connection t) t) →
          (∀ t ∈ Ico (origin - d / Q) origin, ∀ y : (F.slice t).carrier,
            Q ≤ (F.connection t).scalarCurvature y →
              SurgeryCanonicalControl F t y F.parameters.epsilon C) →
          (∀ T ∈ Icc (origin - d / Q) origin, T ∈ F.surgery_times →
            F.parameters.delta T ≤ delta F.standard_initial F.local_constants) →
          ∀ N : SingularCComponent (F.metric origin) (F.connection origin) (2 * C),
            x ∈ N.carrier →
          ∀ U : TopologicalSpace.Opens (F.slice origin).carrier,
            (U : Set (F.slice origin).carrier) = N.carrier →
            ∃ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc (-d / Q) 0) U,
              (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) ∧
              ∀ s : ℝ, ∀ hs : s ∈ Ioc (-d / Q) 0, ∀ y : U,
                (F.connection (origin + s / 1)).scalarCurvature
                  (e.forward s ⟨hs.1.le, hs.2⟩ y.val) < 4 * (C + 1) * Q := by
  classical
  obtain ⟨d, hd, hd1, hmetricDuration, hscalar⟩ :=
    exists_component_strict_scalar_duration P PA.toM47ScalarPersistencePredecessors C hC
  let L := 4 * (C + 1)
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let Db := 4 * C * Real.sqrt L
  have hDb : 0 < Db := by dsimp only [Db]; positivity
  choose delta hdelta hcap using fun g₀ K =>
    exists_component_cap_exclusion_cutoff.{u} g₀ K Db hDb
  refine ⟨d, hd, hd1, delta, hdelta, ?_⟩
  intro F origin Q x hxQ hQ6 hQexp htime hpinch hcanonical hcutoff N hx U hU
  have hQ : 0 < Q := by linarith
  have ha : -d / Q < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) hQ
  have hxU : x ∈ U := by change x ∈ (U : Set _); rw [hU]; exact hx
  have hcompact : IsCompact (U : Set (F.slice origin).carrier) := hU.symm ▸ N.compact
  have hconnected : IsConnected (U : Set (F.slice origin).carrier) := by
    rw [hU, N.component_eq]
    exact isConnected_connectedComponent
  have htime0 : origin ∈ F.time_domain := htime ⟨by linarith [div_pos hd hQ], le_rfl⟩
  obtain ⟨initial, hinitial⟩ := exists_component_singleton_cylinder F origin htime0 U
  have hfrontier : ∀ c (hc : c ∈ Ioc (-d / Q) 0)
      (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U),
      (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) →
      ∀ (hT : origin + c / 1 ∈ F.surgery_times)
        [Nonempty (F.slice (origin + c / 1)).carrier],
        e.forward c ⟨le_rfl, hc.2⟩ '' (U : Set _) ⊆
          interior (F.event (origin + c / 1) hT).retained_post := by
    intro c hc e he hT _
    have hcLower : -(d / Q) < c := by simpa only [neg_div] using hc.1
    let H := L * Q
    have hH : 0 < H := mul_pos hLpos hQ
    have hclock : origin + c / 1 ∈ Icc (origin - d / Q) origin := by
      simp only [div_one]
      constructor <;> linarith [hcLower, hc.2]
    have himage := component_cylinder_image_eq e U.isOpen hcompact hconnected
      c ⟨le_rfl, hc.2⟩ hxU
    have hbounds :
        (∀ y ∈ U, (F.connection (origin + c / 1)).scalarCurvature
          (e.forward c ⟨le_rfl, hc.2⟩ y) ≤ H) ∧
        intrinsicDiameter (F.metric (origin + c / 1))
          (e.forward c ⟨le_rfl, hc.2⟩ '' (U : Set _)) <
            ENNReal.ofReal (4 * C / Real.sqrt Q) := by
      rcases lt_or_eq_of_le hc.2 with hc0 | rfl
      · have hsbound := hscalar F origin Q x hxQ hQ6 hQexp N hx U hU c hc.1.le hc0
          e he hpinch hcanonical
        have hcurvature : ∀ s : ℝ, ∀ hs : s ∈ Ioc c 0, ∀ y ∈ U,
            (F.connection (origin + s / 1)).curvatureTensorNorm
              (e.forward s ⟨hs.1.le, hs.2⟩ y) ≤ 13 * H := by
          intro s hs y hy
          have hwindow : origin + s / 1 ∈ Icc (origin - d / Q) origin := by
            simp only [div_one]
            constructor <;> linarith [hcLower, hs.1, hs.2]
          exact component_pinched_curvature_bound P (hpinch _ hwindow) hQexp hL
            (mem_univ _) (hsbound s hs ⟨y, hy⟩).le
        have hshort : 6 * (13 * H) * (-c) ≤ 1 / 2 := by
          have hcQ : Q * (-c) ≤ d := by
            have h := (div_le_iff₀ hQ).1 hc.1.le
            nlinarith
          have hmul := mul_le_mul_of_nonneg_left hcQ (by positivity : 0 ≤ 78 * L)
          dsimp only [H]
          change 156 * L * d ≤ 1 at hmetricDuration
          nlinarith
        have hquadratic := component_cylinder_quadratic_le_two P PA hc0
          (by positivity : 0 ≤ 13 * H) U ⟨x, hxU⟩ e he hshort hcurvature
        refine ⟨?_, component_cylinder_image_diameter_lt N hx hxQ U hU e c
          ⟨le_rfl, hc.2⟩ (hquadratic c ⟨le_rfl, hc.2⟩)⟩
        intro y hy
        exact component_cylinder_scalar_le_at_left P e hc0 hy
          (fun s hs => (hsbound s hs ⟨y, hy⟩).le)
      · have hterminalDiameter := terminal_diameter_eq e ⟨le_rfl, le_rfl⟩ (he _)
        refine ⟨?_, ?_⟩
        · intro y hy
          rw [terminal_scalar_eq e ⟨le_rfl, le_rfl⟩ (he _) hy]
          have hyN : y ∈ N.carrier := by rw [← hU]; exact hy
          have hupper := twoComponent_scalar_bound N hx hxQ hyN
          dsimp only [H, L]
          nlinarith
        · rw [hterminalDiameter]
          have hdiam := component_diameter_lt N hx
          rw [← hU, hxQ] at hdiam
          have hradius : (2 * C) * Q ^ (-1 / 2 : ℝ) = 2 * C / Real.sqrt Q := by
            rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hQ.le,
              ← Real.sqrt_eq_rpow, div_eq_mul_inv]
          rw [hradius] at hdiam
          apply hdiam.trans_le
          apply ENNReal.ofReal_le_ofReal
          apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg Q)
          linarith
    have hupper : ∀ z ∈ connectedComponent (e.forward c ⟨le_rfl, hc.2⟩ x),
        (F.connection (origin + c / 1)).scalarCurvature z ≤ H := by
      rw [← himage]
      rintro z ⟨y, hy, rfl⟩
      exact hbounds.1 y hy
    have hradius : Db / Real.sqrt H = 4 * C / Real.sqrt Q := by
      dsimp only [Db, H]
      rw [Real.sqrt_mul hLpos.le]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hLpos), ne_of_gt (Real.sqrt_pos.mpr hQ)]
    have hdiam : intrinsicDiameter (F.metric (origin + c / 1))
        (connectedComponent (e.forward c ⟨le_rfl, hc.2⟩ x)) <
          ENNReal.ofReal (Db / Real.sqrt H) := by
      rw [← himage, hradius]
      exact hbounds.2
    have hfree := hcap F.standard_initial F.local_constants F.parameters F.slice F.metric
      (origin + c / 1) (F.event _ hT) (F.connection _) (hcutoff _ hclock hT)
      H hH (e.forward c ⟨le_rfl, hc.2⟩ x) hupper hdiam
    rw [himage]
    exact capFree_post_component_subset_interior (F.event _ hT) hfree
  obtain ⟨e, he⟩ := exists_component_backward_cylinder_of_retained_frontiers ha.le
    (by simpa only [div_neg, neg_div, sub_eq_add_neg] using htime)
    (U : Set _) U.isOpen ⟨x, hxU⟩ initial hinitial hfrontier
  exact ⟨e, he, hscalar F origin Q x hxQ hQ6 hQexp N hx U hU (-d / Q) le_rfl ha
    e he hpinch hcanonical⟩

end PoincareConjecture.M47
