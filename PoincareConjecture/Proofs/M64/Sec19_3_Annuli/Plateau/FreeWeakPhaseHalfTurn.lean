import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnNormalization
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnVerticalGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnSeamGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnObserved
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ScalarPhaseGreen













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "T" => m64AnnulusHalfTurn
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)





theorem exists_halfTurn
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hperiod0 : Function.Periodic c0 curvePeriod)
    (hperiod1 : Function.Periodic c1 curvePeriod)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (hD : angularPoint (k * D) = angularPoint 0) :
    ∃ B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      B.annulus.map = A.annulus.map ∘ T ∧
      (∀ i, ∀ᵐ p ∂mu, B.annulus.column i p = A.annulus.column i (T p)) ∧
      B.label0 = m64FreePhaseHalfTurnLabel A.label0 ∧
      B.label1 = m64FreePhaseHalfTurnLabel A.label1 := by
  have hl := A.labels_continuous hH0 hH1
  obtain ⟨O, hO, hcol⟩ := A.annulus.exists_halfTurn (hc0.comp hl.1) (hc1.comp hl.2)
  let l0 := m64FreePhaseHalfTurnLabel A.label0
  let l1 := m64FreePhaseHalfTurnLabel A.label1
  let j0 := m64FreePhaseHalfTurnFloor A.label0
  let j1 := m64FreePhaseHalfTurnFloor A.label1
  let C : ℝ := (j0 : ℝ) * D
  let offset : ℝ := A.offset + ((j1 - j0 : ℤ) : ℝ) * D
  have hb0 (x : ℝ) : c0 (l0 x) = c0 (A.label0 (m64BoundaryHalfTurn x)) :=
    m64FreePhaseHalfTurnLabel_boundary hperiod0 A.label0_period x
  have hb1 (x : ℝ) : c1 (l1 x) = c1 (A.label1 (m64BoundaryHalfTurn x)) :=
    m64FreePhaseHalfTurnLabel_boundary hperiod1 A.label1_period x
  let B0 : M64ObservedWeakAnnulus (n := n) e (c0 ∘ l0) (c1 ∘ l1) := {
    map := O.map
    observed_memLp := O.observed_memLp
    column := O.column
    tangent := O.tangent
    weak_partial := O.weak_partial
    boundary := fun phi hp => by
      convert O.boundary phi hp using 1
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Function.comp_apply, hb0, hb1]
    seam := O.seam }
  let u := m64FreePhaseHalfTurn A.phase D
  let W := fun (i : Fin 2) (p : LoopPlane) => A.phaseColumn i (T p)
  have hu : MemLp u 2 mu := m64FreePhaseHalfTurn_memLp (Lp.memLp A.phase) D
  have huC : MemLp (fun p => u p - C) 2 mu :=
    hu.sub (m64Annulus_continuous_memLp_two continuous_const)
  have hW (i : Fin 2) : MemLp (W i) 2 mu :=
    m64AnnulusHalfTurn_memLp (Lp.memLp (A.phaseColumn i))
  let phase := huC.toLp (fun p => u p - C)
  let column := fun i => (hW i).toLp (W i)
  have hphase : (phase : LoopPlane → ℝ) =ᵐ[mu] fun p => u p - C := huC.coeFn_toLp
  have hcolumn (i : Fin 2) : (column i : LoopPlane → ℝ) =ᵐ[mu] W i :=
    (hW i).coeFn_toLp
  let b0 : ℝ → ℝ := fun x => H0 (A.label0 (x + curvePeriod / 2))
  let b1 : ℝ → ℝ := fun x => H1 (A.label1 (x + curvePeriod / 2)) + A.offset
  have b0c : Continuous b0 := H0.continuous.comp (hl.1.comp (continuous_id.add_const _))
  have b1c : Continuous b1 :=
    (H1.continuous.comp (hl.2.comp (continuous_id.add_const _))).add_const _
  have hboundary : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * W 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * b1 x - phi (annulusPoint x 0) * b0 x := by
    intro phi hp
    exact m64FreePhaseHalfTurn_vertical_green (Lp.memLp A.phase)
      (Lp.memLp (A.phaseColumn 1)) (H0.continuous.comp hl.1)
      ((H1.continuous.comp hl.2).add_const _)
      (fun x => by simp only [Function.comp_apply, A.label0_period, hH0])
      (fun x => by simp only [Function.comp_apply, A.label1_period, hH1]; ring)
      A.phase_boundary hp
  have hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * W 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) :=
    m64FreePhaseHalfTurn_seam_green (Lp.memLp A.phase)
      (Lp.memLp (A.phaseColumn 0)) A.phase_seam
  have hshift0 (x : ℝ) : H0 (l0 x) = b0 x - C :=
    m64FreePhaseHalfTurnLabel_phase hH0 x
  have hshift1 (x : ℝ) : H1 (l1 x) + offset = b1 x - C := by
    rw [show H1 (l1 x) = H1 (A.label1 (x + curvePeriod / 2)) - (j1 : ℝ) * D from
      m64FreePhaseHalfTurnLabel_phase hH1 x]
    dsimp only [offset, b1, C]
    rw [Int.cast_sub]
    ring
  have hboundary' : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * column 1 p) + (∫ p in S, fderiv ℝ phi p e1 * phase p) =
        ∫ x in I, phi (annulusPoint x 1) * (H1 (l1 x) + offset) -
          phi (annulusPoint x 0) * H0 (l0 x) := by
    intro phi hp
    have hc : (∫ p in S, phi p * column 1 p) = ∫ p in S, phi p * W 1 p :=
      integral_congr_ae ((hcolumn 1).mono fun p h => congrArg (phi p * ·) h)
    have hv : (∫ p in S, fderiv ℝ phi p e1 * phase p) =
        ∫ p in S, fderiv ℝ phi p e1 * (u p - C) :=
      integral_congr_ae (hphase.mono fun p h => congrArg (fderiv ℝ phi p e1 * ·) h)
    simp_rw [hshift0, hshift1]
    rw [hc, hv]
    exact m64Annulus_vertical_green_sub_const hu b0c b1c hboundary C hp
  have hseam' : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * column 0 p) + (∫ p in S, fderiv ℝ phi p e0 * phase p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) := by
    intro phi hp hs
    have hc : (∫ p in S, phi p * column 0 p) = ∫ p in S, phi p * W 0 p :=
      integral_congr_ae ((hcolumn 0).mono fun p h => congrArg (phi p * ·) h)
    have hv : (∫ p in S, fderiv ℝ phi p e0 * phase p) =
        ∫ p in S, fderiv ℝ phi p e0 * (u p - C) :=
      integral_congr_ae (hphase.mono fun p h => congrArg (fderiv ℝ phi p e0 * ·) h)
    rw [hc, hv]
    exact m64Annulus_seam_green_sub_const hu hseam C hp hs
  have hpD := m64AngularPoint_phase_periodic hD
  have hpC : angularPoint (k * C) = angularPoint 0 := by
    simpa only [C, mul_zero] using hpD.int_mul_eq j0
  have hoffset : angularPoint (k * offset) = angularPoint 0 := by
    exact (hpD.int_mul (j1 - j0) A.offset).trans A.offset_circle
  have hobs := m64FreePhaseHalfTurn_observation hD A.phase_observation
  let B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D := {
    label0 := l0
    label1 := l1
    label0_monotone := m64FreePhaseHalfTurnLabel_monotone A.label0_monotone
    label1_monotone := m64FreePhaseHalfTurnLabel_monotone A.label1_monotone
    label0_period := m64FreePhaseHalfTurnLabel_period A.label0_period
    label1_period := m64FreePhaseHalfTurnLabel_period A.label1_period
    label0_normalized := Ico_subset_Icc_self m64FreePhaseHalfTurnLabel_normalized
    label1_normalized := Ico_subset_Icc_self m64FreePhaseHalfTurnLabel_normalized
    annulus := B0
    phase := phase
    phaseColumn := column
    phase_weak := m64Annulus_scalar_weak_of_green hboundary' hseam'
    phase_observation := by
      filter_upwards [hobs, hphase] with p ho hp
      change R (e (O.map p)) = angularPoint (k * phase p)
      rw [hO, hp, m64AngularPoint_sub_phase_period hpC]
      exact ho
    offset := offset
    offset_circle := hoffset
    phase_boundary := hboundary'
    phase_seam := hseam' }
  exact ⟨B, hO, hcol, rfl, rfl⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
