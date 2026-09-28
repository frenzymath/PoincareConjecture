import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCompactGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Poincare.Analysis.Sobolev.Weak Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem exists_compact_phase_correction
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (B : M64ObservedWeakAnnulus (n := n) e (c0 ∘ A.label0) (c1 ∘ A.label1))
    {K : Set LoopPlane} (hK : IsCompact K) (hKS : K ⊆ S)
    {delta : LoopPlane → ℝ} {W : Fin 2 → LoopPlane → ℝ}
    (hdelta : MemLp delta 2 volume) (hW : ∀ i, MemLp (W i) 2 volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (W i) delta univ)
    (hsupport : ∀ p, p ∉ K → delta p = 0)
    (hobs : (fun p => R (e (B.map p))) =ᵐ[mu]
      fun p => angularPoint (k * (A.phase p + delta p))) :
    ∃ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      C.label0 = A.label0 ∧ C.label1 = A.label1 ∧ C.annulus.map = B.map ∧
      ∀ i, C.annulus.column i = B.column i := by
  let u : Lp ℝ 2 mu := (hdelta.restrict S).toLp delta
  let v : Fin 2 → Lp ℝ 2 mu := fun i => (hW i |>.restrict S).toLp (W i)
  let f : Lp ℝ 2 mu := A.phase + u
  let g : Fin 2 → Lp ℝ 2 mu := fun i => A.phaseColumn i + v i
  have hu : u =ᵐ[mu] delta := (hdelta.restrict S).coeFn_toLp
  have hv (i : Fin 2) : v i =ᵐ[mu] W i := (hW i |>.restrict S).coeFn_toLp
  have hf : f =ᵐ[mu] fun p => A.phase p + delta p := by
    filter_upwards [Lp.coeFn_add A.phase u, hu] with p hp hup
    change (A.phase + u) p = _
    rw [hp, Pi.add_apply, hup]
  have hg (i : Fin 2) : g i =ᵐ[mu] fun p => A.phaseColumn i p + W i p := by
    filter_upwards [Lp.coeFn_add (A.phaseColumn i) (v i), hv i] with p hp hvp
    change (A.phaseColumn i + v i) p = _
    rw [hp, Pi.add_apply, hvp]
  have hw (i : Fin 2) : HasWeakPartialDeriv i (g i) f S :=
    m64WeakPartialDeriv_ae_congr hf.symm (hg i).symm
      (m64WeakPartial_add (Lp.memLp A.phase) (hdelta.restrict S)
        (Lp.memLp (A.phaseColumn i)) (hW i |>.restrict S)
        (A.phase_weak i) ((hweak i).restrict isOpen_interior (subset_univ _)))
  have hflux (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in S, phi p * g i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * f p) =
      (∫ p in S, phi p * A.phaseColumn i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p) := by
    have hp := m64Annulus_continuous_memLp_two hphi.continuous
    have hd := m64Annulus_continuous_memLp_two
      ((hphi.continuous_fderiv (by simp)).clm_apply
        (continuous_const (y := EuclideanSpace.single i 1)))
    have hcols : (∫ p in S, phi p * g i p) =
        ∫ p in S, phi p * (A.phaseColumn i p + W i p) :=
      integral_congr_ae ((hg i).mono fun p hp => congrArg (phi p * ·) hp)
    have hvalues : (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * f p) =
        ∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * (A.phase p + delta p) :=
      integral_congr_ae (hf.mono fun p hp =>
        congrArg (fderiv ℝ phi p (EuclideanSpace.single i 1) * ·) hp)
    rw [hcols, hvalues]
    simp_rw [mul_add]
    have hadd0 := integral_add (hp.integrable_mul (Lp.memLp (A.phaseColumn i)))
      (hp.integrable_mul (hW i |>.restrict S))
    have hadd1 := integral_add (hd.integrable_mul (Lp.memLp A.phase))
      (hd.integrable_mul (hdelta.restrict S))
    simp only [Pi.mul_apply] at hadd0 hadd1
    rw [hadd0, hadd1]
    have hz := m64WeakPhase_compact_green hK hKS hdelta (hW i) (hweak i)
      hsupport phi hphi
    linarith
  let C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D := {
    A with
    annulus := B
    phase := f
    phaseColumn := g
    phase_weak := hw
    phase_observation := by
      filter_upwards [hobs, hf] with p hp hfp
      rw [hfp]
      exact hp
    phase_boundary := fun phi hp => (hflux phi hp 1).trans (A.phase_boundary phi hp)
    phase_seam := fun phi hp hs => (hflux phi hp 0).trans (A.phase_seam phi hp hs) }
  exact ⟨C, rfl, rfl, rfl, fun _ => rfl⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
