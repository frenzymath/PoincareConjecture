import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthChart
import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M47.SeedCylinderClock
import PoincareConjecture.Proofs.M47.CanonicalCapComparisonTolerance
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialExactCutoff
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJets
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_PhysicalBirthMetric
import PoincareConjecture.Proofs.M04.ShiCarrier
import PoincareConjecture.Proofs.M13.OrdinaryFlow











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

private theorem exists_scaled_singleton_cylinder
    (F : SurgeryFlowData.{u}) {t q : ℝ} (ht : t ∈ F.time_domain) (hq : 0 < q)
    (U : Set (F.slice t).carrier) :
    ∃ e : SurgeryFlowCylinder F (F.slice t) t q (Icc 0 0) U,
      ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x := by
  obtain ⟨e0, based⟩ := exists_component_singleton_cylinder F t ht U
  have hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 0) : t + s / q = t + s / 1 := by
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    simp only [hs0, zero_div]
  let e := Proofs.M47.seedCylinderReclock e0 hq ordConnected_Icc id
    (mapsTo_id _) (strictMono_id.strictMonoOn _) hclock
  refine ⟨e, ?_⟩
  intro hs x hx
  exact (Proofs.M47.seedCylinderReclock_forward_heq e0 hq ordConnected_Icc id
    (mapsTo_id _) (strictMono_id.strictMonoOn _) hclock 0 hs x).trans (based _ x hx)




theorem exists_cap_birth_family_comparison_cutoff
    (g0 : StandardInitialMetric) (K : MetricSurgeryConstants)
    {A eta : ℝ} (hA : 0 < A) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 → F.local_constants = K →
      ∀ (S : MaximalStandardCapFlow F.standard_initial), S.base.lifetime = 1 →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        F.parameters.delta t ≤ delta → ∀ i : Fin (F.event t hT).cap_count,
          ∃ e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
              (Icc 0 0)
              ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
            ∃ initial : SurgeryCapInitialComparison F t hT i A,
              SurgeryCapFamilyComparison F S A eta e initial.chart ∧
              ∀ hs x,
                x ∈ (F.metric t).ball ((F.event t hT).caps i).tip
                  (A * F.parameters.h t) → HEq (e.forward 0 hs x) x := by
  let kappa := min (eta / 2) (A + 1)⁻¹
  have hkappa : 0 < kappa := lt_min (by positivity) (by positivity)
  have hkappaEta : kappa < eta := (min_le_left _ _).trans_lt (by linarith only [heta])
  have hAinv : A < kappa⁻¹ := by
    have h := one_div_le_one_div_of_le hkappa (min_le_right (eta / 2) (A + 1)⁻¹)
    simp only [one_div, inv_inv] at h
    linarith only [h]
  have horder : ⌊eta⁻¹⌋₊ ≤ ⌊kappa⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ heta hkappa).mpr hkappaEta.le)
  obtain ⟨delta, hdelta, comparison⟩ :=
    exists_initial_cap_exact_comparison_cutoff.{u} g0 K hkappa
  refine ⟨delta, hdelta, ?_⟩
  intro F hinitial hK S hlifetime t hT hn hsmall i
  obtain ⟨Q, hlink, hballs⟩ := comparison F hinitial hK t hT hsmall i
  obtain ⟨initial, himage, hmap⟩ := exists_cap_birth_chart_with_map F t hT i hA hAinv Q hlink
    (hballs A hA hAinv.le)
  let U := (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)
  let V := F.standard_initial.metric.ball 0 A
  have hU : IsOpen U := M04.initial_ball_isOpen _ _ _
  have hV : IsOpen V := M04.initial_ball_isOpen _ _ _
  have hsub : V ⊆ F.standard_initial.metric.ball 0 kappa⁻¹ :=
    fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hAinv.le)
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  obtain ⟨e, based⟩ := exists_scaled_singleton_cylinder F (F.surgery_times_subset hT)
    (sq_pos_of_pos (inv_pos.mpr hh)) U
  obtain ⟨bound, hbound, hjets⟩ := Q.jets
  have hboundEta : bound < eta ^ 2 :=
    hbound.trans (pow_lt_pow_left₀ hkappaEta hkappa.le (by decide))
  refine ⟨e, initial, ?_, based⟩
  refine ⟨bound, hboundEta, hlifetime, ?_, himage, ?_⟩
  · intro s hs
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst s
    exact ⟨le_rfl, S.base.lifetime_pos⟩
  · intro s hs x hx
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst s
    have hread (y : StandardCapSpace) (hy : y ∈ V)
        (v : Fin 2 → TangentSpace (𝓡 3) y) :
        e.pullbackInner 0 hs (initial.chart y)
            (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 0))
            (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 1)) =
          (((F.event t hT).necks i).neck.scale)⁻¹ ^ 2 *
            surgeryCapPullback ((F.event t hT).local_result i).metric Q.map y v := by
      have hyU : initial.chart y ∈ U := by
        change initial.chart y ∈ (F.metric t).ball _ _
        rw [← himage]
        exact mem_image_of_mem initial.chart hy
      rw [Proofs.M46.surgeryCylinder_pullbackInner_zero hU e hs (based hs) hyU]
      let gQ := M13.scaleSmoothMetric (F.metric t) ((F.parameters.h t)⁻¹ ^ 2)
        (sq_pos_of_pos (inv_pos.mpr hh))
      have hpull := M44.physical_birth_pullback_eq F t hT i Q gQ
        (fun _ _ _ => rfl) hV hsub hmap hy
      exact congrArg (fun T : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ =>
        T (v 0) (v 1)) hpull
    have hmetric : (⟨S.metric 0, S.connection 0⟩ :
        Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g) =
        ⟨F.standard_initial.metric, F.standard_initial.connection⟩ :=
      Sigma.ext S.base.initial_metric S.base.initial_connection
    let B : CovariantTensorEvaluation 3 StandardCapSpace 2 := fun y v =>
      e.pullbackInner 0 hs (initial.chart y)
        (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 0))
        (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 1))
    have hmodel := congrArg
      (fun p : Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g =>
        singularMetricJetErrorSquared p.1 p.2 B ⌊eta⁻¹⌋₊ x) hmetric
    change singularMetricJetErrorSquared (S.metric 0) (S.connection 0) B ⌊eta⁻¹⌋₊ x ≤ bound
    rw [hmodel]
    have hgerm : ∀ᶠ y in 𝓝 x, B y = (fun v =>
        (((F.event t hT).necks i).neck.scale)⁻¹ ^ 2 *
          surgeryCapPullback ((F.event t hT).local_result i).metric Q.map y v) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      funext v
      exact hread y hy v
    rw [M44.singularMetricJetErrorSquared_congr_germ _ _ hgerm ⌊eta⁻¹⌋₊]
    exact (Proofs.M47.singularMetricJetErrorSquared_mono_order _ _ _ horder x).trans
      (hjets x (hsub hx))

end PoincareConjecture.M47
