import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularObserved
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

theorem exists_triangularSource
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S)
    (hzero : ∀ s, T (annulusPoint 0 s) = annulusPoint 0 s)
    (hperiod : ∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s)
    (hshift : ∀ x s, T (annulusPoint (x + curvePeriod) s) =
      T (annulusPoint x s) + annulusPoint curvePeriod 0) :
    ∃ B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      B.annulus.map = A.annulus.map ∘ T ∧
      (∀ i, ∀ᵐ p ∂mu, B.annulus.column i p =
        if i = 0 then fderiv ℝ T p e0 0 • A.annulus.column 0 (T p)
        else fderiv ℝ T p e1 0 • A.annulus.column 0 (T p) + A.annulus.column 1 (T p)) ∧
      B.label0 = (fun x => A.label0 (T (annulusPoint x 0) 0)) ∧
      B.label1 = (fun x => A.label1 (T (annulusPoint x 1) 0)) ∧
      (B.phase : LoopPlane → ℝ) =ᵐ[mu] A.phase ∘ T := by
  have hl := A.labels_continuous hH0 hH1
  obtain ⟨Q, hQmap, hQcol⟩ := A.annulus.exists_triangularSource (hc0.comp hl.1)
    (hc1.comp hl.2) T hT hi hsecond hpos hpre hzero hperiod
  let u : LoopPlane → ℝ := A.phase ∘ T
  let W := fun (i : Fin 2) (p : LoopPlane) =>
    if i = 0 then fderiv ℝ T p e0 0 * A.phaseColumn 0 (T p)
    else fderiv ℝ T p e1 0 * A.phaseColumn 0 (T p) + A.phaseColumn 1 (T p)
  have hu : MemLp u 2 mu := m64TriangularSource_memLp_two T
    (hT.of_le (by simp)) (hi.of_le (by simp)) hsecond hpos hpre (Lp.memLp A.phase)
  have hW (i : Fin 2) : MemLp (W i) 2 mu := by
    fin_cases i
    · exact m64TriangularSource_weighted_column_memLp T (hT.of_le (by simp))
        (hi.of_le (by simp)) hsecond hpos hpre (Lp.memLp (A.phaseColumn 0)) 0
    · exact (m64TriangularSource_weighted_column_memLp T (hT.of_le (by simp))
        (hi.of_le (by simp)) hsecond hpos hpre (Lp.memLp (A.phaseColumn 0)) 1).add
        (m64TriangularSource_memLp_two T (hT.of_le (by simp)) (hi.of_le (by simp))
          hsecond hpos hpre (Lp.memLp (A.phaseColumn 1)))
  let phase := hu.toLp u
  let column := fun i => (hW i).toLp (W i)
  have hphase : (phase : LoopPlane → ℝ) =ᵐ[mu] u := hu.coeFn_toLp
  have hcolumn (i : Fin 2) : (column i : LoopPlane → ℝ) =ᵐ[mu] W i := (hW i).coeFn_toLp
  have hq := m64Source_quasiMeasurePreserving T (hi.differentiable (by simp)) hpre
  have hint (i : Fin 2) (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p * column i p) = ∫ p in S, phi p * W i p :=
    integral_congr_ae ((hcolumn i).mono fun p hp => congrArg (phi p * ·) hp)
  have hvalue (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p * phase p) = ∫ p in S, phi p * A.phase (T p) :=
    integral_congr_ae (hphase.mono fun p hp => congrArg (phi p * ·) hp)
  have hw (i : Fin 2) : HasWeakPartialDeriv i (W i) u S := by
    have h := m64TriangularSource_weakPartials T hT hi hsecond hpos hpre
      (Lp.memLp A.phase) (Lp.memLp (A.phaseColumn 0)) (Lp.memLp (A.phaseColumn 1))
      (A.phase_weak 0) (A.phase_weak 1)
    fin_cases i
    · exact h.1
    · exact h.2
  have hm (s : ℝ) : StrictMono (fun x => T (annulusPoint x s) 0) :=
    strictMono_of_hasDerivAt_pos
      (fun x => m64Source_horizontalSlice_hasDerivAt (hT.differentiable (by simp)) x s)
      (fun x => hpos (annulusPoint x s))
  have hshift0 (x s : ℝ) : T (annulusPoint (x + curvePeriod) s) 0 =
      T (annulusPoint x s) 0 + curvePeriod := by
    rw [hshift]
    rfl
  have hseam : ∀ psi : LoopPlane → ℝ, ContDiff ℝ 1 psi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        psi (annulusPoint curvePeriod s) = psi (annulusPoint 0 s)) →
      (∫ p in S, psi p • A.phaseColumn 0 p) +
        (∫ p in S, fderiv ℝ psi p e0 • A.phase p) =
      (∫ s in Icc (0 : ℝ) 1, psi (annulusPoint curvePeriod s)) • D := by
    intro psi hpsi hperiod
    simpa only [smul_eq_mul, mul_comm] using A.phase_seam psi hpsi hperiod
  let B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D := {
    label0 := fun x => A.label0 (T (annulusPoint x 0) 0)
    label1 := fun x => A.label1 (T (annulusPoint x 1) 0)
    label0_monotone := A.label0_monotone.comp (hm 0).monotone
    label1_monotone := A.label1_monotone.comp (hm 1).monotone
    label0_period := fun x => by rw [hshift0, A.label0_period]
    label1_period := fun x => by rw [hshift0, A.label1_period]
    label0_normalized := by rw [hzero]; exact A.label0_normalized
    label1_normalized := by rw [hzero]; exact A.label1_normalized
    annulus := Q
    phase := phase
    phaseColumn := column
    phase_weak := fun i => m64WeakPartialDeriv_ae_congr hphase.symm (hcolumn i).symm (hw i)
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
      simpa only [W, show (1 : Fin 2) ≠ 0 from by decide, ite_false,
        smul_eq_mul, Function.comp_apply] using
        m64TriangularSource_preserves_boundary T hT hi hsecond hpos hpre hzero hperiod
          (Lp.memLp A.phase) (Lp.memLp (A.phaseColumn 0)) (Lp.memLp (A.phaseColumn 1))
          (H0.continuous.comp hl.1) ((H1.continuous.comp hl.2).add_const A.offset) D
          hbd hseam phi hp
    phase_seam := fun phi hp hs => by
      rw [hint, hvalue]
      simpa only [W, ite_true, smul_eq_mul, mul_comm] using
        m64TriangularSource_preserves_seam T hT hi hsecond hpos hpre hzero hperiod
          A.phase (A.phaseColumn 0) D hseam phi hp hs }
  exact ⟨B, hQmap, hQcol, rfl, rfl, hphase⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
