import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem exists_phase_disk_replacement
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (B : M64ObservedWeakAnnulus (n := n) e (c0 ∘ A.label0) (c1 ∘ A.label1))
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict K))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p * V i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
      (∫ p in K, phi p * A.phaseColumn i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p))
    (hobs : (fun p => R (e (B.map p))) =ᵐ[mu]
      fun p => angularPoint (k * K.piecewise u A.phase p)) :
    ∃ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      C.label0 = A.label0 ∧ C.label1 = A.label1 ∧ C.annulus.map = B.map ∧
      ∀ i, C.annulus.column i = B.column i := by
  let U := K.piecewise u A.phase
  let W := fun i => K.piecewise (V i) (A.phaseColumn i)
  have hU : MemLp U 2 mu := m64MemLp_piecewise_of_subset hK hKS hu (Lp.memLp A.phase)
  have hW (i : Fin 2) : MemLp (W i) 2 mu :=
    m64MemLp_piecewise_of_subset hK hKS (hV i) (Lp.memLp (A.phaseColumn i))
  let phase := hU.toLp U
  let column := fun i => (hW i).toLp (W i)
  have hphase : phase =ᵐ[mu] U := hU.coeFn_toLp
  have hcolumn (i : Fin 2) : column i =ᵐ[mu] W i := (hW i).coeFn_toLp
  have hflux (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in S, phi p * column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * phase p) =
      (∫ p in S, phi p * A.phaseColumn i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p) := by
    have hd := (hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))
    have h := m64WeakReplacement_flux hK hKS A.phase u (A.phaseColumn i) (V i)
      phi (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1))
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
    exact h
  let C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D := {
    A with
    annulus := B
    phase := phase
    phaseColumn := column
    phase_weak := fun i phi hphi hc hs => by
      have h := hflux phi (hphi.of_le (by simp)) i
      have hold := A.phase_weak i phi hphi hc hs
      simp only [mul_comm] at h hold ⊢
      linarith
    phase_observation := by
      filter_upwards [hphase, hobs] with p hp ho
      rw [hp]
      exact ho
    phase_boundary := fun phi hp => (hflux phi hp 1).trans (A.phase_boundary phi hp)
    phase_seam := fun phi hp hs => (hflux phi hp 0).trans (A.phase_seam phi hp hs) }
  exact ⟨C, rfl, rfl, rfl, fun _ => rfl⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
