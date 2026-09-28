import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirth
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_CapScalarRate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_inserted_cap_birth_scalar_floor_cutoff
    {g0 : StandardInitialMetric} (P : RepairedCapPersistenceData.{u} g0)
    (K : MetricSurgeryConstants) :
    ∃ c delta : ℝ, 0 < c ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 → F.local_constants = K →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        F.parameters.delta t ≤ delta → ∀ i : Fin (F.event t hT).cap_count,
          ∀ y ∈ ((F.event t hT).caps i).carrier,
            c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature y := by
  obtain ⟨c, hc, hrate⟩ := (Classical.choice P.standard_cap_uniqueness).scalar_lower_bound
  let A := g0.cylindrical_end.radius + 6
  have hA : 0 < A := by dsimp only [A]; linarith [g0.cylindrical_end.radius_pos]
  obtain ⟨eta, heta, _hetaHalf, hscalar⟩ :=
    Proofs.M46.exists_actualCap_scalarRate_tolerance P hc
      (by norm_num : (1 / 2 : ℝ) < 1) hA hrate
  obtain ⟨delta, hdelta, hbirth⟩ := exists_cap_birth_family_comparison_cutoff g0 K hA heta
  refine ⟨c, delta, hc, hdelta, ?_⟩
  intro F hinitial hK t hT hn hsmall i y hy
  let S : MaximalStandardCapFlow F.standard_initial := hinitial.symm ▸ P.standard_cap.flow
  have hS : HEq S P.standard_cap.flow := by subst g0; rfl
  have hlifetime : S.base.lifetime = 1 := by
    subst g0
    exact P.standard_cap.lifetime_one
  obtain ⟨e, initial, comparison, based⟩ := hbirth F hinitial hK S hlifetime t hT hsmall i
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hyball : y ∈ (F.metric t).ball ((F.event t hT).caps i).tip
      (A * F.parameters.h t) := by
    have houter := ((F.event t hT).caps i).outer_ball hy
    change (F.metric t).edist ((F.event t hT).caps i).tip y ≤
      ENNReal.ofReal (F.parameters.h t * (F.standard_initial.cylindrical_end.radius + 5)) at houter
    change (F.metric t).edist ((F.event t hT).caps i).tip y < ENNReal.ofReal (A * F.parameters.h t)
    apply houter.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hA hh)).mpr
    have hradius : F.standard_initial.cylindrical_end.radius = g0.cylindrical_end.radius :=
      congrArg (fun g : StandardInitialMetric => g.cylindrical_end.radius) hinitial
    dsimp only [A]
    rw [hradius]
    nlinarith only [hh]
  obtain ⟨z, hz, hzy⟩ := comparison.choose_spec.2.2.2.1.symm ▸ hyball
  let hzero : (0 : ℝ) ∈ Icc 0 0 := ⟨le_rfl, le_rfl⟩
  have h := hscalar F hinitial S hS t hT hn i (Icc 0 0)
    ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t))
    e initial comparison hh 0 hzero (by norm_num) z hz
  have hpoint : (⟨t + 0 / ((F.parameters.h t)⁻¹ ^ 2),
      e.forward 0 hzero (initial.chart z)⟩ : Σ s, (F.slice s).carrier) = ⟨t, y⟩ :=
    Sigma.ext (by simp) ((based hzero _ (hzy.symm ▸ hyball)).trans (heq_of_eq hzy))
  have hread := congrArg
    (fun p : Σ s, (F.slice s).carrier => (F.connection p.1).scalarCurvature p.2) hpoint
  change (F.connection (t + 0 / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
    (e.forward 0 hzero (initial.chart z)) = (F.connection t).scalarCurvature y at hread
  rw [hread] at h
  simpa only [sub_zero, mul_one] using h

end PoincareConjecture.M47
