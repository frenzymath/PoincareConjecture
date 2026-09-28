import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceObservedPullback
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Poincare.Analysis.Sobolev.Weak Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem exists_horizontalSource
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau) (h0 : tau 0 = 0)
    (hperiod : ∀ x, tau (x + curvePeriod) = tau x + curvePeriod) :
    ∃ B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      B.annulus.map = A.annulus.map ∘ m64HorizontalSource tau ∧
      (∀ i, ∀ᵐ p ∂mu, B.annulus.column i p =
        (if i = 0 then deriv tau (p 0) else 1) •
          A.annulus.column i (m64HorizontalSource tau p)) ∧
      B.label0 = A.label0 ∘ tau ∧ B.label1 = A.label1 ∘ tau ∧
      (B.phase : LoopPlane → ℝ) =ᵐ[mu] A.phase ∘ m64HorizontalSource tau := by
  let T := m64HorizontalSource tau
  have hP : tau curvePeriod = curvePeriod := by simpa only [zero_add, h0] using hperiod 0
  obtain ⟨Q, hQmap, hQcol⟩ := A.annulus.exists_horizontalSource ht hi hpos hmono h0 hP
  let u : LoopPlane → ℝ := A.phase ∘ T
  let W := fun (i : Fin 2) (p : LoopPlane) =>
    (if i = 0 then deriv tau (p 0) else 1) * A.phaseColumn i (T p)
  have hu : MemLp u 2 mu := m64HorizontalSource_memLp_two
    (ht.of_le (by simp)) (hi.of_le (by simp)) hpos hmono h0 hP (Lp.memLp A.phase)
  have hW (i : Fin 2) : MemLp (W i) 2 mu :=
    m64HorizontalSource_column_memLp_two (ht.of_le (by simp)) (hi.of_le (by simp))
      hpos hmono h0 hP (Lp.memLp (A.phaseColumn i)) i
  let phase := hu.toLp u
  let column := fun i => (hW i).toLp (W i)
  have hphase : (phase : LoopPlane → ℝ) =ᵐ[mu] u := hu.coeFn_toLp
  have hcolumn (i : Fin 2) : (column i : LoopPlane → ℝ) =ᵐ[mu] W i := (hW i).coeFn_toLp
  have hq := m64HorizontalSource_quasiMeasurePreserving (hi.of_le (by simp)) hmono h0 hP
  have hint (i : Fin 2) (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p * column i p) = ∫ p in S, phi p * W i p :=
    integral_congr_ae ((hcolumn i).mono fun p hp => congrArg (phi p * ·) hp)
  have hvalue (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p * phase p) = ∫ p in S, phi p * A.phase (T p) :=
    integral_congr_ae (hphase.mono fun p hp => congrArg (phi p * ·) hp)
  let B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D := {
    label0 := A.label0 ∘ tau
    label1 := A.label1 ∘ tau
    label0_monotone := A.label0_monotone.comp hmono.monotone
    label1_monotone := A.label1_monotone.comp hmono.monotone
    label0_period := fun x => by simp only [Function.comp_apply, hperiod, A.label0_period]
    label1_period := fun x => by simp only [Function.comp_apply, hperiod, A.label1_period]
    label0_normalized := by simpa only [Function.comp_apply, h0] using A.label0_normalized
    label1_normalized := by simpa only [Function.comp_apply, h0] using A.label1_normalized
    annulus := Q
    phase := phase
    phaseColumn := column
    phase_weak := fun i =>
      m64WeakPartialDeriv_ae_congr hphase.symm (hcolumn i).symm
        (m64HorizontalSource_weakPartial ht hi hpos hmono h0 hP (A.phase_weak i))
    phase_observation := by
      filter_upwards [hq.ae_eq A.phase_observation, hphase] with p hp hu
      rw [hQmap]
      exact hp.trans (congrArg (fun z => angularPoint (k * z)) hu.symm)
    offset := A.offset
    offset_circle := A.offset_circle
    phase_boundary := fun phi hp => by
      rw [hint, hvalue]
      have hbd : ∀ psi : LoopPlane → ℝ, ContDiff ℝ 1 psi →
          (∫ p in S, psi p • A.phaseColumn 1 p) +
            (∫ p in S, fderiv ℝ psi p e1 • A.phase p) =
          ∫ x in Icc (0 : ℝ) curvePeriod,
            psi (annulusPoint x 1) • (H1 (A.label1 x) + A.offset) -
              psi (annulusPoint x 0) • H0 (A.label0 x) := by
        intro psi hpsi
        exact A.phase_boundary psi hpsi
      simpa only [W, show (1 : Fin 2) ≠ 0 from by decide, ite_false, one_mul,
        smul_eq_mul, Function.comp_apply] using
        m64HorizontalSource_preserves_boundary ht hi hpos hmono h0 hP
          A.phase (A.phaseColumn 1) (fun x => H0 (A.label0 x))
          (fun x => H1 (A.label1 x) + A.offset) hbd phi hp
    phase_seam := fun phi hp hs => by
      rw [hint, hvalue]
      have hseam : ∀ psi : LoopPlane → ℝ, ContDiff ℝ 1 psi →
          (∀ s ∈ Icc (0 : ℝ) 1,
            psi (annulusPoint curvePeriod s) = psi (annulusPoint 0 s)) →
          (∫ p in S, psi p • A.phaseColumn 0 p) +
            (∫ p in S, fderiv ℝ psi p e0 • A.phase p) =
          (∫ s in Icc (0 : ℝ) 1, psi (annulusPoint curvePeriod s)) • D := by
        intro psi hpsi hperiod
        simpa only [smul_eq_mul, mul_comm] using A.phase_seam psi hpsi hperiod
      simpa only [W, ite_true, smul_eq_mul, mul_comm] using
        m64HorizontalSource_preserves_seam ht hi hpos hmono h0 hP
          A.phase (A.phaseColumn 0) D hseam phi hp hs }
  exact ⟨B, hQmap, hQcol, rfl, rfl, hphase⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
