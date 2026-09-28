import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakSobolevExtraction

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

theorem m64WeakPartialDeriv_ae_congr
    {S : Set LoopPlane} {i : Fin 2} {f g f' g' : LoopPlane → ℝ}
    (hf : f =ᵐ[volume.restrict S] f') (hg : g =ᵐ[volume.restrict S] g')
    (h : HasWeakPartialDeriv i g f S) : HasWeakPartialDeriv i g' f' S := by
  intro phi hphi hc hs
  calc
    (∫ p in S, f' p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p in S, f p * fderiv ℝ phi p (EuclideanSpace.single i 1) :=
      integral_congr_ae (hf.symm.mono fun p hp =>
        congrArg (fun r : ℝ => r * fderiv ℝ phi p (EuclideanSpace.single i 1)) hp)
    _ = -(∫ p in S, g p * phi p) := h phi hphi hc hs
    _ = -(∫ p in S, g' p * phi p) := by
      congr 1
      exact integral_congr_ae (hg.mono fun p hp => congrArg (fun r : ℝ => r * phi p) hp)

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

private theorem coordinate_test_apply
    (phi : LoopPlane → ℝ) (hp : MemLp phi 2 mu) (b : Fin m) (u : Lp E 2 mu) :
    testIntegral phi hp (LpFiniteCoordinatesNative.coordinateLp mu b u) =
      ∫ p in S, phi p * u p b := by
  rw [testIntegral_apply]
  apply integral_congr_ae
  filter_upwards [LpFiniteCoordinatesNative.coordinateLp_coe mu b u] with p hp
  simp only [hp, smul_eq_mul]

theorem m64Annulus_weak_partial_closed
    {u v : ℕ → Lp E 2 mu} {U V : Lp E 2 mu}
    (hu : WeakConverges u U) (hv : WeakConverges v V) (i : Fin 2) (b : Fin m)
    (hw : ∀ j, HasWeakPartialDeriv i (fun p => v j p b) (fun p => u j p b) S) :
    HasWeakPartialDeriv i (fun p => V p b) (fun p => U p b) S := by
  intro phi hphi hc hs
  let dphi : LoopPlane → ℝ := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hp : MemLp phi 2 mu :=
    (hphi.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdp : MemLp dphi 2 mu :=
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  let P := LpFiniteCoordinatesNative.coordinateLp mu b
  have hup : WeakConverges (fun j => P (u j)) (P U) := fun L => hu (L.comp P)
  have hvp : WeakConverges (fun j => P (v j)) (P V) := fun L => hv (L.comp P)
  have hlim := weak_limit_linear_identity hvp hup
    (testIntegral (F := ℝ) dphi hdp) (testIntegral phi hp) (fun j => by
      rw [coordinate_test_apply, coordinate_test_apply]
      simpa only [dphi, mul_comm] using hw j phi hphi hc hs)
  rw [coordinate_test_apply, coordinate_test_apply] at hlim
  simpa only [dphi, mul_comm] using hlim

theorem m64WeakLimit_affine_identity
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u v : ℕ → H} {U V : H} (hu : WeakConverges u U) (hv : WeakConverges v V)
    (A B : H →L[ℝ] F) (c : F) (hseq : ∀ j, A (v j) + B (u j) = c) :
    A V + B U = c := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have ht := (hv (L.comp A)).add (hu (L.comp B))
  have hconstant : Tendsto (fun j => L (A (v j)) + L (B (u j))) atTop (𝓝 (L c)) := by
    have heq : (fun j => L (A (v j)) + L (B (u j))) = fun _ : ℕ => L c := by
      funext j
      rw [← map_add, hseq]
    rw [heq]
    exact tendsto_const_nhds
  simpa only [ContinuousLinearMap.comp_apply, map_add] using tendsto_nhds_unique ht hconstant

theorem m64Annulus_weak_green_closed
    {u v : ℕ → Lp E 2 mu} {U V : Lp E 2 mu}
    (hu : WeakConverges u U) (hv : WeakConverges v V) (i : Fin 2)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (c : E)
    (hseq : ∀ j, (∫ p in S, phi p • v j p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • u j p) = c) :
    (∫ p in S, phi p • V p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • U p) = c := by
  let dphi : LoopPlane → ℝ := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hp : MemLp phi 2 mu := by
    apply (memLp_two_iff_integrable_sq hphi.continuous.aestronglyMeasurable).mpr
    exact (hphi.continuous.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hdc : Continuous dphi := (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdp : MemLp dphi 2 mu := by
    apply (memLp_two_iff_integrable_sq hdc.aestronglyMeasurable).mpr
    exact (hdc.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  simpa only [testIntegral_apply] using m64WeakLimit_affine_identity hu hv
    (testIntegral phi hp) (testIntegral dphi hdp) c
    (fun j => by simpa only [testIntegral_apply] using hseq j)

end PoincareConjecture
