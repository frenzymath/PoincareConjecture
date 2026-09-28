import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleGreenIdentity
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem m64Annulus_weak_fixed_boundary_identity
    (f : ℕ → LoopPlane → F) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hU : ∀ j, MemLp (f j) 2 (volume.restrict (interior m64AnnulusDomain)))
    (hV : ∀ j, MemLp (fun p => fderiv ℝ (f j) p
      (EuclideanSpace.single (1 : Fin 2) 1)) 2
        (volume.restrict (interior m64AnnulusDomain)))
    {u V : Lp F 2 (volume.restrict (interior m64AnnulusDomain))}
    (hu : WeakConverges (fun j => (hU j).toLp (f j)) u)
    (hv : WeakConverges (fun j => (hV j).toLp (fun p => fderiv ℝ (f j) p
      (EuclideanSpace.single (1 : Fin 2) 1))) V)
    (c0 c1 : ℝ → F)
    (h0 : ∀ j x, f j (annulusPoint x 0) = c0 x)
    (h1 : ∀ j x, f j (annulusPoint x 1) = c1 x)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in interior m64AnnulusDomain, phi p • V p) +
      (∫ p in interior m64AnnulusDomain,
        fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • u p) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • c1 x - phi (annulusPoint x 0) • c0 x := by
  let dphi : LoopPlane → ℝ := fun p =>
    fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1)
  have hdc : Continuous dphi :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hp : MemLp phi 2 (volume.restrict (interior m64AnnulusDomain)) := by
    apply (memLp_two_iff_integrable_sq hphi.continuous.aestronglyMeasurable).mpr
    exact (hphi.continuous.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hdp : MemLp dphi 2 (volume.restrict (interior m64AnnulusDomain)) := by
    apply (memLp_two_iff_integrable_sq hdc.aestronglyMeasurable).mpr
    exact (hdc.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  let A := testIntegral (F := F) phi hp
  let B := testIntegral (F := F) dphi hdp
  let c : F := ∫ x in Icc (0 : ℝ) curvePeriod,
    phi (annulusPoint x 1) • c1 x - phi (annulusPoint x 0) • c0 x
  have hseq (j : ℕ) : A ((hV j).toLp (fun p => fderiv ℝ (f j) p
      (EuclideanSpace.single (1 : Fin 2) 1))) + B ((hU j).toLp (f j)) = c := by
    dsimp only [A, B]
    rw [testIntegral_toLp, testIntegral_toLp]
    simpa only [h0, h1] using m64Annulus_vertical_green_identity (hf j) hphi
  have hlim : A V + B u = c := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    have ht := (hv (L.comp A)).add (hu (L.comp B))
    have hc : Tendsto (fun j => L (A ((hV j).toLp (fun p => fderiv ℝ (f j) p
        (EuclideanSpace.single (1 : Fin 2) 1)))) + L (B ((hU j).toLp (f j))))
        atTop (𝓝 (L c)) := by
      have heq : (fun j => L (A ((hV j).toLp (fun p => fderiv ℝ (f j) p
          (EuclideanSpace.single (1 : Fin 2) 1)))) + L (B ((hU j).toLp (f j)))) =
          fun _ : ℕ => L c := by
        funext j
        rw [← map_add, hseq]
      rw [heq]
      exact tendsto_const_nhds
    simpa only [ContinuousLinearMap.comp_apply, map_add] using tendsto_nhds_unique ht hc
  simpa only [A, B, testIntegral_apply] using hlim

end PoincareConjecture
