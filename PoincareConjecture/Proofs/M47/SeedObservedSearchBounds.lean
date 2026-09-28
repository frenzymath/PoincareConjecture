import PoincareConjecture.Proofs.M47.SeedThreeStopAncestors
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SmallCurvature
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

open M46



theorem seed_observed_search_bounds
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext cutoff : ℝ} {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {origin c H B : ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hc : c ≤ 0) (hbottom : 0 ≤ origin + c)
    (horigin : origin ∈ surgeryObservationInterval O)
    (hH : 0 < H) (hlevel : rNext⁻¹ ^ 2 ≤ H)
    (hB : seedAnalyticConstant S ≤ B) (hsmall : (Real.sqrt H)⁻¹ ≤ 1 / 200)
    (hbase : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
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
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤ 52 * H := by
  let ell := (Real.sqrt H)⁻¹
  have hell : 0 < ell := inv_pos.mpr (Real.sqrt_pos.mpr hH)
  have hellH : ell⁻¹ ^ 2 = H := by
    dsimp only [ell]
    rw [inv_inv, Real.sq_sqrt hH.le]
  have hBpos : 0 < B := (seedAnalyticConstant_pos S).trans_le hB
  have hC : F.parameters.C = S.setup.C := by rw [inputs.old.C_eq, hp.setup_eq]
  let P44 : M44CapPersistencePredecessors.{u} := ⟨P.m04, P.m13.ordinary_flow⟩
  have hline (x : (F.slice origin).carrier) (hx : x ∈ U) :
      ∀ s ∈ Icc c 0, cylinderScalar e x s ≤ 4 * H := by
    have hzero : (0 : ℝ) ∈ Icc c 0 := ⟨hc, le_rfl⟩
    have hstart : cylinderScalar e x 0 ≤ 2 * ell⁻¹ ^ 2 := by
      rw [cylinderScalar_of_mem e x 0 hzero, hellH]
      have hpoint : (⟨origin + 0 / 1, e.forward 0 hzero x⟩ :
          (t : ℝ) × (F.slice t).carrier) = ⟨origin, x⟩ :=
        Sigma.ext (by simp) (hbase hzero x hx)
      have heq := congrArg (fun z : (t : ℝ) × (F.slice t).carrier =>
        (F.connection z.1).scalarCurvature z.2) hpoint
      exact heq ▸ hinitial x hx
    have hrate : ∀ s ∈ Ioo c 0, origin + s / 1 ∉ F.surgery_times →
        ell⁻¹ ^ 2 ≤ cylinderScalar e x s →
          |cylinderScalarRate e x s| ≤ B * cylinderScalar e x s ^ 2 := by
      intro s hs _hregular hhigh
      have hsO : origin + s / 1 ∈ surgeryObservationInterval O := by
        change 0 ≤ origin + s / 1 ∧ origin + s / 1 < O.H
        simp only [div_one]
        constructor <;> linarith only [hbottom, hs.1, hs.2, horigin.2]
      have hR : H ≤ (F.connection (origin + s / 1)).scalarCurvature
          (e.forward s (Ioo_subset_Icc_self hs) x) := by
        simpa only [hellH, cylinderScalar_of_mem e x s (Ioo_subset_Icc_self hs)] using hhigh
      have hcanonical := inputs.canonical (origin + s / 1) hsO (O.interval_subset hsO)
        (e.forward s (Ioo_subset_Icc_self hs) x) (hlevel.trans hR)
      rw [hC] at hcanonical
      have hancestor := seed_search_before_birth_nonpositive P inputs.terminal_policy e hc
        horigin hbase q hcomponent hbirth s (Ioo_subset_Icc_self hs) hs.2 x hx
      have hanalytic := canonical_analytic_on_nonpositive S F (origin + s / 1)
        (e.forward s (Ioo_subset_Icc_self hs) x) hcanonical hancestor
      classical
      simpa only [cylinderScalar, cylinderScalarRate, dif_pos (Ioo_subset_Icc_self hs)] using
        hanalytic.2.2.trans (mul_le_mul_of_nonneg_right hB (sq_nonneg _))
    have h := cylinderScalar_le_four_inv_sq P44 inputs.pinched e hx hc hBpos hell
      hstart hrate (by simpa only [hellH] using hshort)
    simpa only [hellH] using h
  intro s hs x hx
  have hscalar : (F.connection (origin + s / 1)).scalarCurvature
      (e.forward s hs x) ≤ 4 * H := by
    simpa only [cylinderScalar_of_mem e x s hs] using hline x hx s hs
  refine ⟨hscalar, ?_⟩
  have h := low_scalar_curvature_le_fifty_two P.toM46
    (inputs.pinched _ (e.time_subset (mem_image_of_mem _ hs))) hell hsmall
    (e.forward s hs x) (by simpa only [hellH] using hscalar)
  simpa only [hellH] using h

end PoincareConjecture.Proofs.M47
