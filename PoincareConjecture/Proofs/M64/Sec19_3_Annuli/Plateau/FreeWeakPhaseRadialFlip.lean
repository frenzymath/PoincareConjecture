import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusRadialFlip
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ScalarPhaseGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseSeamObservation






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k degree : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "T" => m64AnnulusRadialFlip
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)





theorem exists_radial_flip
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + degree)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + degree) :
    ∃ B : M64FreeWeakPhaseAnnulus (n := n) e R c1 c0 H1 H0 k degree,
      B.annulus.map = A.annulus.map ∘ T ∧
      B.label0 = A.label1 ∧ B.label1 = A.label0 ∧ B.offset = -A.offset ∧
      (∀ i, (B.annulus.column i : LoopPlane → E) =ᵐ[mu]
        fun p => (if i = 0 then (1 : ℝ) else -1) • A.annulus.column i (T p)) ∧
      ∀ (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ),
        B.annulus.weightedEnergy Q r = A.annulus.weightedEnergy Q r := by
  obtain ⟨O, hO, hcol, henergy⟩ := A.annulus.exists_radial_flip
  have hl := A.labels_continuous hH0 hH1
  have hmp := m64AnnulusRadialFlip_restrict_measurePreserving
  let u := fun p => A.phase (T p)
  let V := fun (i : Fin 2) p => (if i = 0 then (1 : ℝ) else -1) * A.phaseColumn i (T p)
  have hu : MemLp u 2 mu := (Lp.memLp A.phase).comp_measurePreserving hmp
  have huC : MemLp (fun p => u p - A.offset) 2 mu :=
    hu.sub (m64Annulus_continuous_memLp_two continuous_const)
  have hV (i : Fin 2) : MemLp (V i) 2 mu :=
    ((Lp.memLp (A.phaseColumn i)).comp_measurePreserving hmp).const_mul _
  let phase := huC.toLp (fun p => u p - A.offset)
  let column := fun i => (hV i).toLp (V i)
  have hphase : (phase : LoopPlane → ℝ) =ᵐ[mu] fun p => u p - A.offset := huC.coeFn_toLp
  have hcolumn (i : Fin 2) : (column i : LoopPlane → ℝ) =ᵐ[mu] V i :=
    (hV i).coeFn_toLp
  have hboundary : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * H0 (A.label0 x) -
          phi (annulusPoint x 0) * (H1 (A.label1 x) + A.offset) := by
    intro phi hp
    have hpc := hp.comp (m64AnnulusRadialFlip_contDiff.of_le (by simp))
    have ht := m64AnnulusRadialFlip_green (fun p => A.phase p)
      (fun p => A.phaseColumn 1 p) hp 1
    simp only [smul_eq_mul] at ht
    rw [A.phase_boundary (phi ∘ T) hpc] at ht
    calc
      _ = -(∫ x in I, (phi ∘ T) (annulusPoint x 1) *
          (H1 (A.label1 x) + A.offset) -
          (phi ∘ T) (annulusPoint x 0) * H0 (A.label0 x)) := by
        simpa only [V, u, show (1 : Fin 2) ≠ 0 from by decide, ite_false,
          neg_one_mul] using ht
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [Function.comp_apply, m64AnnulusRadialFlip_point, sub_self, sub_zero,
          neg_sub]
  have hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        degree * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) := by
    simpa only [V, u, ite_true, one_mul] using
      m64WeakPhase_radialFlip_seam A.phase (fun i => A.phaseColumn i) degree A.phase_seam
  have hboundary' : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * column 1 p) + (∫ p in S, fderiv ℝ phi p e1 * phase p) =
        ∫ x in I, phi (annulusPoint x 1) * (H0 (A.label0 x) + -A.offset) -
          phi (annulusPoint x 0) * H1 (A.label1 x) := by
    intro phi hp
    have hc : (∫ p in S, phi p * column 1 p) = ∫ p in S, phi p * V 1 p :=
      integral_congr_ae ((hcolumn 1).mono fun p h => congrArg (phi p * ·) h)
    have hv : (∫ p in S, fderiv ℝ phi p e1 * phase p) =
        ∫ p in S, fderiv ℝ phi p e1 * (u p - A.offset) :=
      integral_congr_ae (hphase.mono fun p h => congrArg (fderiv ℝ phi p e1 * ·) h)
    rw [hc, hv]
    simpa only [Function.comp_apply, add_sub_cancel_right, sub_eq_add_neg,
      add_neg_cancel_right] using
      m64Annulus_vertical_green_sub_const hu ((H1.continuous.comp hl.2).add_const _)
        (H0.continuous.comp hl.1) hboundary A.offset hp
  have hseam' : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * column 0 p) + (∫ p in S, fderiv ℝ phi p e0 * phase p) =
        degree * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) := by
    intro phi hp hs
    have hc : (∫ p in S, phi p * column 0 p) = ∫ p in S, phi p * V 0 p :=
      integral_congr_ae ((hcolumn 0).mono fun p h => congrArg (phi p * ·) h)
    have hv : (∫ p in S, fderiv ℝ phi p e0 * phase p) =
        ∫ p in S, fderiv ℝ phi p e0 * (u p - A.offset) :=
      integral_congr_ae (hphase.mono fun p h => congrArg (fderiv ℝ phi p e0 * ·) h)
    rw [hc, hv]
    exact m64Annulus_seam_green_sub_const hu hseam A.offset hp hs
  let B : M64FreeWeakPhaseAnnulus (n := n) e R c1 c0 H1 H0 k degree := {
    label0 := A.label1
    label1 := A.label0
    label0_monotone := A.label1_monotone
    label1_monotone := A.label0_monotone
    label0_period := A.label1_period
    label1_period := A.label0_period
    label0_normalized := A.label1_normalized
    label1_normalized := A.label0_normalized
    annulus := O
    phase := phase
    phaseColumn := column
    phase_weak := m64Annulus_scalar_weak_of_green hboundary' hseam'
    phase_observation := by
      filter_upwards [hphase, hmp.quasiMeasurePreserving.ae A.phase_observation] with p hp ho
      rw [hO, hp, m64AngularPoint_sub_phase_period A.offset_circle]
      exact ho
    offset := -A.offset
    offset_circle := by
      simpa only [zero_sub, mul_zero] using
        m64AngularPoint_sub_phase_period A.offset_circle 0
    phase_boundary := hboundary'
    phase_seam := hseam' }
  exact ⟨B, hO, rfl, rfl, rfl, hcol, henergy⟩




theorem exists_radial_flip_minimum
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + degree)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + degree)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (modulus : ℝ)
    (hmin : ∀ s : ℝ, 0 < s →
      ∀ W : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree,
        A.annulus.weightedEnergy Q modulus ≤ W.annulus.weightedEnergy Q s) :
    ∃ B : M64FreeWeakPhaseAnnulus (n := n) e R c1 c0 H1 H0 k degree,
      B.annulus.map = A.annulus.map ∘ T ∧ B.label0 = A.label1 ∧ B.label1 = A.label0 ∧
      (∀ r : ℝ, B.annulus.weightedEnergy Q r = A.annulus.weightedEnergy Q r) ∧
      ∀ s : ℝ, 0 < s →
        ∀ W : M64FreeWeakPhaseAnnulus (n := n) e R c1 c0 H1 H0 k degree,
          B.annulus.weightedEnergy Q modulus ≤ W.annulus.weightedEnergy Q s := by
  obtain ⟨B, hmap, h0, h1, -, -, heq⟩ := A.exists_radial_flip hH0 hH1
  refine ⟨B, hmap, h0, h1, heq Q, ?_⟩
  intro s hs W
  obtain ⟨Z, -, -, -, -, -, hZ⟩ := W.exists_radial_flip hH1 hH0
  rw [heq Q modulus, ← hZ Q s]
  exact hmin s hs Z

end PoincareConjecture.M64FreeWeakPhaseAnnulus
