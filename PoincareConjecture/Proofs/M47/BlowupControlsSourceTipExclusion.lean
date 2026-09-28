import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapLocus
import PoincareConjecture.Proofs.M47.CanonicalStandardTipLocus
import PoincareConjecture.Proofs.M47.CanonicalStandardRecutCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem exists_source_bad_point_tip_exclusion_tolerance
    (S : RepairedControlledSchedulesData.{u}) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta : theta < 1) :
    ∃ A0 : ℝ, 0 < A0 ∧ ∀ A : ℝ, A0 ≤ A →
      ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = S.standard_initial),
        F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
      ∀ (model : MaximalStandardCapFlow F.standard_initial),
        HEq model S.cap_persistence.standard_cap.flow →
      ∀ (base t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count)
        (closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
          (Icc 0 ((base - t) / (F.parameters.h t) ^ 2))
          ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F model A eta closed initial.chart →
      (base - t) / (F.parameters.h t) ^ 2 ∈ Icc 0 theta →
      ∀ (y0 : (F.slice t).carrier) (y : (F.slice base).carrier),
        y0 ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) →
        (∀ htop, HEq (closed.forward ((base - t) / (F.parameters.h t) ^ 2) htop y0) y) →
        ¬ SurgeryCanonicalControl F base y F.parameters.epsilon F.parameters.C →
        ∃ z ∈ F.standard_initial.metric.ball 0 A, initial.chart z = y0 ∧
          (57 / 10 : ℝ) * S.setup.epsilon⁻¹ <
            ((S.cap_persistence.standard_cap.flow.metric
              ((base - t) / (F.parameters.h t) ^ 2)).edist 0 z).toReal *
              Real.sqrt ((S.cap_persistence.standard_cap.flow.connection
                ((base - t) / (F.parameters.h t) ^ 2)).scalarCurvature z) := by
  classical
  let L := (57 / 10 : ℝ) * S.setup.epsilon⁻¹
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (inv_nonneg.mpr S.setup.epsilon_pos.le)
  obtain ⟨R, hR, hK, hKsub⟩ :=
    exists_compact_standard_tip_locus S.cap_persistence htheta0 htheta hL
  let K : Set (ℝ × StandardCapSpace) := {p | p.1 ∈ Icc 0 theta ∧
    ((S.cap_persistence.standard_cap.flow.metric p.1).edist 0 p.2).toReal *
      Real.sqrt ((S.cap_persistence.standard_cap.flow.connection p.1).scalarCurvature p.2) ≤ L}
  have hcaps : ∀ p ∈ K,
      ∃ N : CapCertificate (S.cap_persistence.standard_cap.flow.metric p.1),
        N.epsilon = S.setup.epsilon ∧ N.cap_constant ≤ S.setup.C ∧
        N.connection = S.cap_persistence.standard_cap.flow.connection p.1 ∧ p.2 ∈ N.core := by
    intro p hp
    apply standard_tip_locus_setup_cap S ?_ hp.2
    rw [S.cap_persistence.standard_cap.lifetime_one]
    exact ⟨hp.1.1, hp.1.2.trans_lt htheta⟩
  obtain ⟨A0, hA0, _hRA0, tolerances⟩ :=
    exists_source_cap_certificate_at_base_of_locus S.cap_persistence htheta0.le htheta
      S.setup.C_pos hR hK hKsub hcaps
  refine ⟨A0, hA0, fun A hA => ?_⟩
  obtain ⟨eta0, heta0, transfer⟩ := tolerances A hA
  refine ⟨eta0, heta0, ?_⟩
  intro F hinitial heps hC model hmodel base t hT hn i closed initial eta heta hetaLe
    comparison hd y0 y hy0 htop hfail
  by_contra hfar
  push Not at hfar
  obtain ⟨N, hNe, hNC, hND, hNy⟩ := transfer F hinitial model hmodel base t hT hn i
    closed initial eta heta hetaLe comparison hd.1 y0 y hy0 htop
    (fun z hz hzy => ⟨hd, hfar z hz hzy⟩)
  exact hfail (SurgeryCanonicalControl.cap N (hNe.trans heps.symm)
    (by rwa [hC]) hND hNy)

end PoincareConjecture.M47
