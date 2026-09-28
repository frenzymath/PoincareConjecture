import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Transitions
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic













set_option autoImplicit false

open Set Filter Function
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem shiEndpoint_frame_transition
    {cold cnew : OpenPartialHomeomorph M E}
    (ho : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cold cold.source)
    (hoi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cold.symm cold.target)
    (hn : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cnew cnew.source)
    (hni : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cnew.symm cnew.target)
    {x : E} (hx : x ∈ cold.target) (hy : cold.symm x ∈ cnew.source)
    {Pold Pnew : E →L[ℝ] E}
    (hmatch : ∀ v, shiChartField cnew (Pnew v) (cold.symm x) =
      shiChartField cold (Pold v) (cold.symm x)) :
    Pnew = (fderiv ℝ (cnew ∘ cold.symm) x).comp Pold := by
  apply ContinuousLinearMap.ext
  intro v
  have htr := shiChartTransition_field ho hoi hn hni hx hy (Pold v)
  have he := congrArg (mvfderiv (𝓡 n) cnew (cold.symm x))
    ((hmatch v).trans htr.symm)
  simpa only [shiChartField_duality hn hni hy, ContinuousLinearMap.comp_apply] using he

set_option synthInstance.maxHeartbeats 100000 in

set_option backward.isDefEq.respectTransparency false in
private theorem endpoint_quadratic_jets
    (x : E) (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) :
    let Q : E → E := fun z => x + A z + (1 / 2 : ℝ) • B z z
    ContDiff ℝ ∞ Q ∧ Q 0 = x ∧ fderiv ℝ Q 0 = A ∧
      fderiv ℝ (fderiv ℝ Q) 0 = B := by
  let Q : E → E := fun z => x + A z + (1 / 2 : ℝ) • B z z
  have hQ : ContDiff ℝ ∞ Q := by
    simpa +instances only [Q, Pi.add_apply, Pi.smul_apply] using!
      ((contDiff_const.add A.contDiff).add
        ((B.contDiff.clm_apply contDiff_id).const_smul (1 / 2 : ℝ)))
  have hd (z : E) : HasFDerivAt Q (A + B z) z := by
    have h := (B.hasFDerivAt_of_bilinear
      (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1 / 2 : ℝ)
    have he : (1 / 2 : ℝ) •
        (B.precompR E z (ContinuousLinearMap.id ℝ E) +
          B.precompL E (ContinuousLinearMap.id ℝ E) z) = B z := by
      ext v : 1
      change (1 / 2 : ℝ) • (B z v + B v z) = B z v
      rw [hB v z]
      module
    simp only [id_eq] at h
    rw [he] at h
    simpa +instances only [Q, Pi.add_apply, Pi.smul_apply, zero_add] using!
      ((hasFDerivAt_const x z).add A.hasFDerivAt).add h
  have hdf : fderiv ℝ Q = fun z => A + B z := funext fun z => (hd z).fderiv
  refine ⟨hQ, ?_, ?_, ?_⟩
  · simp [Q]
  · simpa only [map_zero, add_zero] using (hd 0).fderiv
  · rw [hdf]
    exact ((B.hasFDerivAt (x := (0 : E))).const_add A).fderiv

set_option synthInstance.maxHeartbeats 100000 in

set_option backward.isDefEq.respectTransparency false in
private theorem endpoint_raw_jets
    (x : E) (A : E →L[ℝ] E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ : ∀ u v, Γ u v = Γ v u) :
    let Q : E → E := fun z => x + A z - (1 / 2 : ℝ) • Γ (A z) (A z)
    ContDiff ℝ ∞ Q ∧ Q 0 = x ∧ fderiv ℝ Q 0 = A ∧
      fderiv ℝ (fderiv ℝ Q) 0 = -Γ.bilinearComp A A := by
  let B : E →L[ℝ] E →L[ℝ] E := -Γ.bilinearComp A A
  have hB (u v : E) : B u v = B v u := by
    change -Γ (A u) (A v) = -Γ (A v) (A u)
    rw [hΓ]
  simpa +instances only [B, neg_apply, ContinuousLinearMap.bilinearComp_apply,
    smul_neg, sub_eq_add_neg] using! endpoint_quadratic_jets x A B hB

set_option synthInstance.maxHeartbeats 100000 in

set_option backward.isDefEq.respectTransparency false in
private theorem endpoint_second_comp
    {F H : E → E} {U : Set E} (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (hF : ContDiff ℝ ∞ F)
    {x : E} (hx : F x ∈ U) (u v : E) :
    fderiv ℝ (fderiv ℝ (H ∘ F)) x u v =
      fderiv ℝ (fderiv ℝ H) (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) +
        fderiv ℝ H (F x) (fderiv ℝ (fderiv ℝ F) x u v) := by
  have hHat : ContDiffAt ℝ ∞ H (F x) := hH.contDiffAt (hU.mem_nhds hx)
  have hDH : HasFDerivAt (fun z => fderiv ℝ H (F z))
      ((fderiv ℝ (fderiv ℝ H) (F x)).comp (fderiv ℝ F x)) x :=
    ((hHat.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp x
      (hF.differentiable (by simp) x).hasFDerivAt
  have hDF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hComp := hDH.clm_comp hDF
  have he : fderiv ℝ (H ∘ F) =ᶠ[𝓝 x]
      (fun z => (fderiv ℝ H (F z)).comp (fderiv ℝ F z)) := by
    filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with z hz
    exact fderiv_comp z ((hH.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      (hF.differentiable (by simp) z)
  have hd := (hComp.congr_of_eventuallyEq he).fderiv
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, add_comm] using!
    congrArg (fun B : E →L[ℝ] E →L[ℝ] E => B u v) hd

set_option maxHeartbeats 1800000 in

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
theorem shiEndpoint_transition_jets [T2Space M] (D : LeviCivitaData g)
    {cold cnew : OpenPartialHomeomorph M E}
    (ho : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cold cold.source)
    (hoi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cold.symm cold.target)
    (hn : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cnew cnew.source)
    (hni : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cnew.symm cnew.target)
    {x : E} (hx : x ∈ cold.target) (hy : cold.symm x ∈ cnew.source)
    (s : ℝ) (Pold Pnew : E →L[ℝ] E)
    (hP : Pnew = (fderiv ℝ (cnew ∘ cold.symm) x).comp Pold) :
    let tau : E → E := cnew ∘ cold.symm
    let y : E := tau x
    let L : E →L[ℝ] E := s • Pnew
    let B : E →L[ℝ] E →L[ℝ] E :=
      -(shiChartChristoffel D cnew y).bilinearComp L L
    let old : E → E := fun z => x + s • Pold z - (1 / 2 : ℝ) •
      shiChartChristoffel D cold x (s • Pold z) (s • Pold z)
    let endpoint : E → E := tau ∘ old
    let raw : E → E := fun z => y + s • Pnew z - (1 / 2 : ℝ) •
      shiChartChristoffel D cnew y (s • Pnew z) (s • Pnew z)
    ContDiffAt ℝ ∞ endpoint 0 ∧ endpoint 0 = y ∧
      fderiv ℝ endpoint 0 = L ∧ fderiv ℝ (fderiv ℝ endpoint) 0 = B ∧
      endpoint 0 = raw 0 ∧ fderiv ℝ endpoint 0 = fderiv ℝ raw 0 ∧
      fderiv ℝ (fderiv ℝ endpoint) 0 = fderiv ℝ (fderiv ℝ raw) 0 := by
  let tau : E → E := cnew ∘ cold.symm
  let y : E := tau x
  let L : E →L[ℝ] E := s • Pnew
  let B : E →L[ℝ] E →L[ℝ] E :=
    -(shiChartChristoffel D cnew y).bilinearComp L L
  let old : E → E := fun z => x + s • Pold z - (1 / 2 : ℝ) •
    shiChartChristoffel D cold x (s • Pold z) (s • Pold z)
  let endpoint : E → E := tau ∘ old
  let raw : E → E := fun z => y + s • Pnew z - (1 / 2 : ℝ) •
    shiChartChristoffel D cnew y (s • Pnew z) (s • Pnew z)
  change ContDiffAt ℝ ∞ endpoint 0 ∧ endpoint 0 = y ∧
    fderiv ℝ endpoint 0 = L ∧ fderiv ℝ (fderiv ℝ endpoint) 0 = B ∧
    endpoint 0 = raw 0 ∧ fderiv ℝ endpoint 0 = fderiv ℝ raw 0 ∧
    fderiv ℝ (fderiv ℝ endpoint) 0 = fderiv ℝ (fderiv ℝ raw) 0
  have hoJets : ContDiff ℝ ∞ old ∧ old 0 = x ∧ fderiv ℝ old 0 = s • Pold ∧
      fderiv ℝ (fderiv ℝ old) 0 =
        -(shiChartChristoffel D cold x).bilinearComp (s • Pold) (s • Pold) := by
    simpa only [old, smul_apply] using
      endpoint_raw_jets x (s • Pold) (shiChartChristoffel D cold x)
        (shiChartChristoffel_symm D ho hoi hx)
  have hnJets : ContDiff ℝ ∞ raw ∧ raw 0 = y ∧ fderiv ℝ raw 0 = L ∧
      fderiv ℝ (fderiv ℝ raw) 0 = B := by
    simpa only [raw, B, L, smul_apply] using
      endpoint_raw_jets y L (shiChartChristoffel D cnew y)
        (shiChartChristoffel_symm D hn hni (cnew.map_source hy))
  let W : Set E := cold.target ∩ cold.symm ⁻¹' cnew.source
  have hW : IsOpen W := cold.isOpen_inter_preimage_symm cnew.open_source
  have hTau : ContDiffOn ℝ ∞ tau W := shiChartTransition_smooth hoi hn
  have hOld0 : old 0 ∈ W := by rw [hoJets.2.1]; exact ⟨hx, hy⟩
  have hTau0 := hTau.contDiffAt (hW.mem_nhds hOld0)
  have hEndpoint : ContDiffAt ℝ ∞ endpoint 0 := hTau0.comp 0 hoJets.1.contDiffAt
  have hAP : (fderiv ℝ tau x).comp (s • Pold) = L := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [L, hP, tau, ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  have hAPv (v : E) : fderiv ℝ tau x ((s • Pold) v) = L v :=
    congrArg (fun A : E →L[ℝ] E => A v) hAP
  have hValue : endpoint 0 = y := by
    change tau (old 0) = tau x
    rw [hoJets.2.1]
  have hFirst : fderiv ℝ endpoint 0 = L := by
    change fderiv ℝ (tau ∘ old) 0 = L
    rw [fderiv_comp 0 (hTau0.differentiableAt (by simp))
      (hoJets.1.differentiable (by simp) 0), hoJets.2.1, hoJets.2.2.1]
    exact hAP
  have hSecond : fderiv ℝ (fderiv ℝ endpoint) 0 = B := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    have hchain := endpoint_second_comp hW hTau hoJets.1 hOld0 u v
    rw [hoJets.2.1, hoJets.2.2.1, hoJets.2.2.2] at hchain
    simp only [neg_apply, ContinuousLinearMap.bilinearComp_apply, map_neg] at hchain
    have htr := shiChartTransition_secondJet D ho hoi hn hni hx hy
      ((s • Pold) u) ((s • Pold) v)
    change fderiv ℝ (fderiv ℝ tau) x ((s • Pold) u) ((s • Pold) v) +
      shiChartChristoffel D cnew y (fderiv ℝ tau x ((s • Pold) u))
        (fderiv ℝ tau x ((s • Pold) v)) =
      fderiv ℝ tau x (shiChartChristoffel D cold x ((s • Pold) u) ((s • Pold) v)) at htr
    rw [hAPv u, hAPv v] at htr
    calc
      fderiv ℝ (fderiv ℝ endpoint) 0 u v =
          fderiv ℝ (fderiv ℝ tau) x ((s • Pold) u) ((s • Pold) v) +
            -fderiv ℝ tau x
              (shiChartChristoffel D cold x ((s • Pold) u) ((s • Pold) v)) := hchain
      _ = -shiChartChristoffel D cnew y (L u) (L v) := by
        rw [eq_sub_of_add_eq htr]
        abel
      _ = B u v := rfl
  exact ⟨hEndpoint, hValue, hFirst, hSecond, hValue.trans hnJets.2.1.symm,
    hFirst.trans hnJets.2.2.1.symm, hSecond.trans hnJets.2.2.2.symm⟩

end PoincareConjecture.RicciFlowAnalysis
