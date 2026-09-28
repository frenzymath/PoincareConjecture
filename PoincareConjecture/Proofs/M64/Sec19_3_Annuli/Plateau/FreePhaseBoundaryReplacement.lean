import PoincareConjecture.Proofs.M64.Mathlib.WeakReplacementFluxDefect
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





theorem exists_phase_boundary_replacement
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    {sigma0 sigma1 : ℝ → ℝ} (hm0 : Monotone sigma0) (hm1 : Monotone sigma1)
    (hp0 : ∀ x, sigma0 (x + curvePeriod) = sigma0 x + curvePeriod)
    (hp1 : ∀ x, sigma1 (x + curvePeriod) = sigma1 x + curvePeriod)
    (hn0 : sigma0 0 ∈ I) (hn1 : sigma1 0 ∈ I)
    (B : M64ObservedWeakAnnulus (n := n) e (c0 ∘ sigma0) (c1 ∘ sigma1))
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict K))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p * V i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
      (∫ p in K, phi p * A.phaseColumn i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p) +
      if i = 1 then
        (∫ x in I, phi (annulusPoint x 1) * (H1 (sigma1 x) + A.offset) -
          phi (annulusPoint x 0) * H0 (sigma0 x)) -
        (∫ x in I, phi (annulusPoint x 1) * (H1 (A.label1 x) + A.offset) -
          phi (annulusPoint x 0) * H0 (A.label0 x)) else 0)
    (hobs : (fun p => R (e (B.map p))) =ᵐ[mu]
      fun p => angularPoint (k * K.piecewise u A.phase p)) :
    ∃ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      C.label0 = sigma0 ∧ C.label1 = sigma1 ∧ C.annulus.map = B.map ∧
      (∀ i, C.annulus.column i = B.column i) ∧
      (C.phase : LoopPlane → ℝ) =ᵐ[mu] K.piecewise u A.phase ∧
      (∀ i, (C.phaseColumn i : LoopPlane → ℝ) =ᵐ[mu]
        K.piecewise (V i) (A.phaseColumn i)) ∧ C.offset = A.offset := by
  let U := K.piecewise u A.phase
  let W := fun i => K.piecewise (V i) (A.phaseColumn i)
  have hU : MemLp U 2 mu := m64MemLp_piecewise_of_subset hK hKS hu (Lp.memLp A.phase)
  have hW (i : Fin 2) : MemLp (W i) 2 mu :=
    m64MemLp_piecewise_of_subset hK hKS (hV i) (Lp.memLp (A.phaseColumn i))
  let phase := hU.toLp U
  let column := fun i => (hW i).toLp (W i)
  have hphase : (phase : LoopPlane → ℝ) =ᵐ[mu] U := hU.coeFn_toLp
  have hcolumn (i : Fin 2) : (column i : LoopPlane → ℝ) =ᵐ[mu] W i :=
    (hW i).coeFn_toLp
  have hflux (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in S, phi p * column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * phase p) =
      (∫ p in S, phi p * A.phaseColumn i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p) +
      if i = 1 then
        (∫ x in I, phi (annulusPoint x 1) * (H1 (sigma1 x) + A.offset) -
          phi (annulusPoint x 0) * H0 (sigma0 x)) -
        (∫ x in I, phi (annulusPoint x 1) * (H1 (A.label1 x) + A.offset) -
          phi (annulusPoint x 0) * H0 (A.label0 x)) else 0 := by
    have hd := (hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))
    have hh := m64WeakReplacement_flux_defect hK hKS A.phase u (A.phaseColumn i) (V i)
      phi (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) _
      (Lp.memLp A.phase) hu (Lp.memLp (A.phaseColumn i)) (hV i)
      (m64Annulus_continuous_memLp_two hphi.continuous)
      (m64Annulus_continuous_memLp_two hd) (by simpa only [smul_eq_mul] using hgreen phi hphi i)
    have h0 : (∫ p in S, phi p * column i p) = ∫ p in S, phi p * W i p :=
      integral_congr_ae ((hcolumn i).mono fun p hp => congrArg (phi p * ·) hp)
    have h1 : (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * phase p) =
        ∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * U p :=
      integral_congr_ae (hphase.mono fun p hp =>
        congrArg (fderiv ℝ phi p (EuclideanSpace.single i 1) * ·) hp)
    rw [h0, h1]
    exact hh
  have hboundary (phi : LoopPlane → ℝ) (hp : ContDiff ℝ 1 phi) :
      (∫ p in S, phi p * column 1 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single 1 1) * phase p) =
      ∫ x in I, phi (annulusPoint x 1) * (H1 (sigma1 x) + A.offset) -
        phi (annulusPoint x 0) * H0 (sigma0 x) := by
    have hh := hflux phi hp 1
    simp only [ite_true] at hh
    rw [A.phase_boundary phi hp] at hh
    linarith
  have hseam (phi : LoopPlane → ℝ) (hp : ContDiff ℝ 1 phi)
      (hs : ∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
      (∫ p in S, phi p * column 0 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single 0 1) * phase p) =
      D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) := by
    have hh := hflux phi hp 0
    simpa using hh.trans (by simpa using A.phase_seam phi hp hs)
  let C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D := {
    label0 := sigma0
    label1 := sigma1
    label0_monotone := hm0
    label1_monotone := hm1
    label0_period := hp0
    label1_period := hp1
    label0_normalized := hn0
    label1_normalized := hn1
    annulus := B
    phase := phase
    phaseColumn := column
    phase_weak := m64Annulus_scalar_weak_of_green hboundary hseam
    phase_observation := by
      filter_upwards [hphase, hobs] with p hp ho
      rw [hp]
      exact ho
    offset := A.offset
    offset_circle := A.offset_circle
    phase_boundary := hboundary
    phase_seam := hseam }
  exact ⟨C, rfl, rfl, rfl, fun _ => rfl, hphase, hcolumn, rfl⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
