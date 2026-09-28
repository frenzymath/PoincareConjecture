import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticComparison
import PoincareConjecture.Definitions.M44CapPersistence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_actualCap_near_scalar_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta A : ℝ}
    (htheta : theta < 1) (hA : 0 < A) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S P.standard_cap.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      0 < F.parameters.h t →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
      let R := (S.connection s).scalarCurvature x
      let V := (F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward s hs (initial.chart x))
      0 < V ∧ R ≤ (101 / 100 : ℝ) * V ∧ V ≤ (101 / 100 : ℝ) * R := by
  obtain ⟨unique⟩ := P.standard_cap_uniqueness
  obtain ⟨c, hc, hrate⟩ := unique.scalar_lower_bound
  obtain ⟨eta0, heta0, hbound⟩ :=
    PoincareConjecture.M47.exists_actualCap_analytic_comparison_tolerance P.standard_cap
      htheta hA (show 0 < c / 1000 by positivity)
  refine ⟨eta0, heta0, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaSmall comparison hh s hs hst x hx
  have h := hbound F hinitial S hS t hT hn i J U e initial eta heta hetaSmall comparison
    hh s hs hst x hx
  let R := (S.connection s).scalarCurvature x
  let V := (F.parameters.h t) ^ 2 *
    (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
      (e.forward s hs (initial.chart x))
  have herror : |V - R| ≤ c / 1000 := by
    simpa only [Prod.fst_sub, Real.norm_eq_abs] using (norm_fst_le _).trans h
  have hfloor : c ≤ R := by
    have ht := comparison.choose_spec.2.2.1 s hs
    cases hinitial
    cases hS
    have htime : s < 1 := by
      rw [← P.standard_cap.lifetime_one]
      exact ht.2
    have hden : 0 < 1 - s := sub_pos.mpr htime
    have hmodel : c ≤ c / (1 - s) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [mul_nonneg hc.le ht.1]
    exact hmodel.trans (hrate s ht x)
  change 0 < V ∧ R ≤ (101 / 100 : ℝ) * V ∧ V ≤ (101 / 100 : ℝ) * R
  obtain ⟨hlo, hhi⟩ := abs_le.mp herror
  refine ⟨by linarith only [hlo, hfloor, hc], ?_, ?_⟩ <;>
    linarith only [hlo, hhi, hfloor, hc]

end PoincareConjecture.Proofs.M47
