import PoincareConjecture.Proofs.M47.CanonicalNeckCapBirthScalar
import PoincareConjecture.Proofs.M47.CanonicalNeckCapTipDistance
import PoincareConjecture.Proofs.M47.CanonicalNeckTipArithmetic
import PoincareConjecture.Proofs.M47.CanonicalNeckCalibratedDistance
import PoincareConjecture.Proofs.M47.CanonicalNeckTipDistance
import PoincareConjecture.Proofs.M47.CanonicalNeckOrdinaryBridge









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem strongNeck_bottom_tip_distance_calibrated
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {T epsilon : ℝ}
    (N : SurgeryStrongNeck F T epsilon) (hsmall : epsilon ≤ 1 / 200)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hU : (U : Set (F.slice T).carrier) = N.neck.carrier)
    (E : SurgeryFlowCylinder F (F.slice T) T 1
      (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U)
    (hbased : ∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x)
    (hagree : ∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
      (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
      ∀ x ∈ U,
        HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) :
    let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
    let ha : a ∈ Icc a 0 :=
      ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
    let t := T + a / 1
    ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
    ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
      E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
      ((F.metric t).edist ((F.event t hT).caps i).tip
        (E.forward a ha N.neck.center)).toReal ≤
          (F.standard_initial.cylindrical_end.radius + 5) * F.parameters.h t +
            (5 / 2 : ℝ) * epsilon⁻¹ * N.neck.scale := by
  dsimp only
  intro hT hn i contact hcontact
  let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
  have ha : a ∈ Icc a 0 :=
    ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
  let t := T + a / 1
  let g := F.metric t
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have he : 0 < epsilon := N.neck.epsilon_pos.trans_eq N.epsilon_eq
  have hscalePos : 0 < N.neck.scale := N.neck.scale_pos
  have hAcap : 0 < F.standard_initial.cylindrical_end.radius + 5 := by
    linarith [F.standard_initial.cylindrical_end.radius_pos]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have houter := ((F.event t hT).caps i).outer_ball hcontact
  have hneck := strongNeck_closed_center_distance_calibrated P N hsmall U hU E
    hbased hagree a ha contact
  have hsymm : g.edist (E.forward a ha contact.val) (E.forward a ha N.neck.center) =
      g.edist (E.forward a ha N.neck.center) (E.forward a ha contact.val) :=
    Manifold.riemannianEDist_comm
  have hdist : g.edist ((F.event t hT).caps i).tip (E.forward a ha N.neck.center) ≤
      ENNReal.ofReal ((F.standard_initial.cylindrical_end.radius + 5) * F.parameters.h t +
        (5 / 2 : ℝ) * epsilon⁻¹ * N.neck.scale) := by
    calc
      _ ≤ g.edist ((F.event t hT).caps i).tip (E.forward a ha contact.val) +
          g.edist (E.forward a ha contact.val) (E.forward a ha N.neck.center) :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal (F.parameters.h t *
          (F.standard_initial.cylindrical_end.radius + 5)) +
          ENNReal.ofReal ((5 / 2 : ℝ) * epsilon⁻¹ * N.neck.scale) := by
        rw [hsymm]
        exact add_le_add houter hneck
      _ = _ := by
        have hleft : 0 ≤ F.parameters.h t *
            (F.standard_initial.cylindrical_end.radius + 5) :=
          mul_nonneg hh.le hAcap.le
        have hright : 0 ≤ (5 / 2 : ℝ) * epsilon⁻¹ * N.neck.scale := by
          positivity
        rw [← ENNReal.ofReal_add hleft hright]
        congr 1
        ring
  have htotal : 0 ≤ (F.standard_initial.cylindrical_end.radius + 5) *
      F.parameters.h t +
        (5 / 2 : ℝ) * epsilon⁻¹ * N.neck.scale := by
    positivity
  exact ENNReal.toReal_le_of_le_ofReal htotal hdist



theorem exists_exposed_neck_standard_cap_locus_tolerance
    (P : M47Predecessors.{u}) {g0 : StandardInitialMetric}
    (cap : RepairedCapPersistenceData.{u} g0)
    {epsilon beta C theta A : ℝ}
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hbeta : 0 < beta) (hbetaSmall : beta < 1 / 2)
    (htheta : theta < 1) (hA : 0 < A)
    (hsetup : epsilon * Real.sqrt cap.standard_cap.initial_estimate.scalar_constant *
      (g0.cylindrical_end.radius + 5) ≤ 1)
    (hcanonical : ∀ s ∈ Ico 0 cap.standard_cap.flow.base.lifetime,
      ∀ z : StandardCapSpace, StandardCanonicalAlternative cap.standard_cap.atlas
        cap.standard_cap.flow s z (beta * epsilon / 3) C) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 1000 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (model : MaximalStandardCapFlow F.standard_initial),
        HEq model cap.standard_cap.flow →
      ∀ T : ℝ, ∀ (N : SurgeryStrongNeck F T epsilon),
      ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
        (U : Set (F.slice T).carrier) = N.neck.carrier →
      ∀ E : SurgeryFlowCylinder F (F.slice T) T 1
          (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
        (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
          ∀ x ∈ U,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) →
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        let ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let t := T + a / 1
        let d := (T - t) / (F.parameters.h t) ^ 2
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
          E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
          0 < d → d ≤ theta →
        ∀ closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
            (Icc 0 d) ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
        ∀ (initial : SurgeryCapInitialComparison F t hT i A) (eta : ℝ),
          0 < eta → eta ≤ eta0 →
          SurgeryCapFamilyComparison F model A eta closed initial.chart →
          (∀ hs y, y ∈ (F.metric t).ball ((F.event t hT).caps i).tip
            (A * F.parameters.h t) → HEq (closed.forward 0 hs y) y) →
          (∀ x ∈ U, E.forward a ha x ∈ (F.metric t).ball
            ((F.event t hT).caps i).tip (A * F.parameters.h t)) →
          (∀ htop x, x ∈ U → HEq (closed.forward d htop (E.forward a ha x)) x) →
          ∃ z ∈ F.standard_initial.metric.ball 0 A,
            initial.chart z = E.forward a ha N.neck.center ∧
            ((cap.standard_cap.flow.metric d).edist 0 z).toReal *
              Real.sqrt ((cap.standard_cap.flow.connection d).scalarCurvature z) <
                (57 / 10 : ℝ) * epsilon⁻¹ ∧
            Nonempty (StandardCapNeighborhood cap.standard_cap.atlas cap.standard_cap.flow
              d (beta * epsilon / 3) C z) := by
  obtain ⟨etaS, hetaS, scalarRatio⟩ := exists_actualCap_near_scalar_tolerance cap htheta hA
  let eta0 := min etaS (1 / 1000)
  refine ⟨eta0, lt_min hetaS (by norm_num), min_le_right _ _, ?_⟩
  intro F hinitial model hmodel T N U hU E hbased hagree
  dsimp only
  intro hT hn i contact hcontact hd hdtheta closed initial eta heta hetaSmall
    comparison based capture terminal
  cases hinitial
  cases hmodel
  let Q := N.neck.scale⁻¹ ^ 2
  let a := -Q⁻¹
  have hQ : 0 < Q := N.cylinder.scale_pos
  have ha : a ∈ Icc a 0 := ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr hQ).le⟩
  let t := T + a / 1
  let h := F.parameters.h t
  let d := (T - t) / h ^ 2
  let D := cap.standard_cap.initial_estimate.scalar_constant
  have hD : 0 < D := cap.standard_cap.initial_estimate.scalar_constant_pos
  have hh : 0 < h :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hzero : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have htop : d ∈ Icc 0 d := ⟨hd.le, le_rfl⟩
  have hetaS' : eta ≤ etaS := hetaSmall.trans (min_le_left _ _)
  have hetaNear : eta ≤ 1 / 1000 := hetaSmall.trans (min_le_right _ _)
  have hratio := scalarRatio F rfl cap.standard_cap.flow HEq.rfl t hT hn i
    (Icc 0 d) _ closed initial eta heta hetaS' comparison hh
  have hcenter : N.neck.center ∈ (U : Set (F.slice T).carrier) := by
    rw [hU]
    exact N.neck.central_sphere_subset N.neck.center_on_central_sphere
  have hcapture := capture N.neck.center hcenter
  have himage := comparison.choose_spec.2.2.2.1
  obtain ⟨z, hz, hzy⟩ := himage.symm ▸ hcapture
  have hbirthUpper := cap_birth_scalar_le_initial cap.standard_cap closed initial comparison
    hzero (based hzero) (fun w hw => (hratio 0 hzero (hd.le.trans hdtheta) w hw).2.2)
      hcapture
  have hscale := strongNeck_scale_mul_height_sq_le P N hsmall U hU E hbased hagree
    hD hbirthUpper
  have hbirth := strongNeck_bottom_tip_distance_calibrated P N hsmall U hU E hbased
    hagree hT i contact hcontact
  have hinverse := cap_birth_tip_distance_near_one hA closed initial comparison
    hzero (based hzero) hh heta hetaNear hz
  rw [hzy] at hinverse
  have htime := comparison.choose_spec.2.2.1 d htop
  have hmodelDistance := (standard_flow_tip_distance_le_initial cap.standard_cap htime z).trans
    hinverse
  have hclock : t + d / (h⁻¹ ^ 2) = T := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  have hpoint : (⟨t + d / (h⁻¹ ^ 2), closed.forward d htop (initial.chart z)⟩ :
      Σ s, (F.slice s).carrier) = ⟨T, N.neck.center⟩ :=
    Sigma.ext hclock (by rw [hzy]; exact terminal htop N.neck.center hcenter)
  have hscalar := congrArg
    (fun p : Σ s, (F.slice s).carrier => (F.connection p.1).scalarCurvature p.2) hpoint
  have hQeq : Q = (F.connection T).scalarCurvature N.neck.center := by
    rw [← N.connection_eq]
    exact neck_scale_inverse_square N.neck
  have hmodelScalar := (hratio d htop hdtheta z hz).2.1
  change (F.connection (t + d / (h⁻¹ ^ 2))).scalarCurvature
    (closed.forward d htop (initial.chart z)) =
      (F.connection T).scalarCurvature N.neck.center at hscalar
  rw [hscalar, ← hQeq] at hmodelScalar
  have hnormal : Q * N.neck.scale ^ 2 = 1 := by
    dsimp only [Q]
    field_simp [N.neck.scale_pos.ne']
  have hAcap : 0 < F.standard_initial.cylindrical_end.radius + 5 := by
    linarith [F.standard_initial.cylindrical_end.radius_pos]
  have htip := cap_tip_distance_margin he hbeta hbetaSmall hD hAcap hQ hh
    N.neck.scale_pos hnormal hscale hsetup ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hbirth hmodelDistance (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hmodelScalar)
  have hlocus := cap_tip_distance_bound he hD hAcap hQ hh N.neck.scale_pos
    hnormal hscale hsetup ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hbirth hmodelDistance (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hmodelScalar)
  have hgamma : beta * epsilon / 3 ≤ 1 / 1200 := by
    have h := mul_le_mul hbetaSmall.le hsmall he.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [h]
  exact ⟨z, hz, hzy, hlocus, standardCanonical_cap_of_tip_distance cap.standard_cap hgamma
    (hcanonical d htime z) htip⟩



theorem exists_exposed_neck_standard_cap_tolerance
    (P : M47Predecessors.{u}) {g0 : StandardInitialMetric}
    (cap : RepairedCapPersistenceData.{u} g0)
    {epsilon beta C theta A : ℝ}
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hbeta : 0 < beta) (hbetaSmall : beta < 1 / 2)
    (htheta : theta < 1) (hA : 0 < A)
    (hsetup : epsilon * Real.sqrt cap.standard_cap.initial_estimate.scalar_constant *
      (g0.cylindrical_end.radius + 5) ≤ 1)
    (hcanonical : ∀ s ∈ Ico 0 cap.standard_cap.flow.base.lifetime,
      ∀ z : StandardCapSpace, StandardCanonicalAlternative cap.standard_cap.atlas
        cap.standard_cap.flow s z (beta * epsilon / 3) C) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 1000 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (model : MaximalStandardCapFlow F.standard_initial),
        HEq model cap.standard_cap.flow →
      ∀ T : ℝ, ∀ (N : SurgeryStrongNeck F T epsilon),
      ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
        (U : Set (F.slice T).carrier) = N.neck.carrier →
      ∀ E : SurgeryFlowCylinder F (F.slice T) T 1
          (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
        (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
          ∀ x ∈ U,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) →
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        let ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let t := T + a / 1
        let d := (T - t) / (F.parameters.h t) ^ 2
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
          E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
          0 < d → d ≤ theta →
        ∀ closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
            (Icc 0 d) ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
        ∀ (initial : SurgeryCapInitialComparison F t hT i A) (eta : ℝ),
          0 < eta → eta ≤ eta0 →
          SurgeryCapFamilyComparison F model A eta closed initial.chart →
          (∀ hs y, y ∈ (F.metric t).ball ((F.event t hT).caps i).tip
            (A * F.parameters.h t) → HEq (closed.forward 0 hs y) y) →
          (∀ x ∈ U, E.forward a ha x ∈ (F.metric t).ball
            ((F.event t hT).caps i).tip (A * F.parameters.h t)) →
          (∀ htop x, x ∈ U → HEq (closed.forward d htop (E.forward a ha x)) x) →
          ∃ z ∈ F.standard_initial.metric.ball 0 A,
            initial.chart z = E.forward a ha N.neck.center ∧
            Nonempty (StandardCapNeighborhood cap.standard_cap.atlas cap.standard_cap.flow
              d (beta * epsilon / 3) C z) := by
  obtain ⟨eta0, heta0, hetaNear, produce⟩ :=
    exists_exposed_neck_standard_cap_locus_tolerance P cap he hsmall hbeta hbetaSmall
      htheta hA hsetup hcanonical
  refine ⟨eta0, heta0, hetaNear, ?_⟩
  intro F hinitial model hmodel T N U hU E hbased hagree
  dsimp only
  intro hT hn i contact hcontact hd hdtheta closed initial eta heta hetaSmall
    comparison based capture terminal
  obtain ⟨z, hz, hzy, _hlocus, cap⟩ := produce F hinitial model hmodel T N U hU E
    hbased hagree hT i contact hcontact hd hdtheta closed initial eta heta hetaSmall
      comparison based capture terminal
  exact ⟨z, hz, hzy, cap⟩

end PoincareConjecture.Proofs.M47
