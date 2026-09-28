import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakDerivativeClosure
import Mathlib.Geometry.Manifold.PartitionOfUnity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped ContDiff Manifold

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak



theorem m64WeakPartial_of_local
    {O : Set LoopPlane} (hO : IsOpen O) {u v : LoopPlane → ℝ} {i : Fin 2}
    (hu : MemLp u 2 (volume.restrict O)) (hv : MemLp v 2 (volume.restrict O))
    (hlocal : ∀ a ∈ O, ∃ U : Set LoopPlane,
      IsOpen U ∧ a ∈ U ∧ U ⊆ O ∧ HasWeakPartialDeriv i v u U) :
    HasWeakPartialDeriv i v u O := by
  classical
  choose U hU hmem hUO hw using fun a : O => hlocal a a.property
  intro phi hphi hc hs
  have hcover : tsupport phi ⊆ ⋃ a : O, U a := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hs hp⟩, hmem ⟨p, hs hp⟩⟩
  obtain ⟨rho, hrho⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓡 2) (isClosed_tsupport phi) U hU hcover
  have hfinite := rho.locallyFinite.finite_nonempty_inter_compact hc
  let J := hfinite.toFinset
  let psi := fun (j : O) p => rho j p * phi p
  have hpsi (j : O) : ContDiff ℝ ∞ (psi j) :=
    (contMDiff_iff_contDiff.mp (rho j).contMDiff).mul hphi
  have hcpsi (j : O) : HasCompactSupport (psi j) := hc.mul_left
  have hspsi (j : O) : tsupport (psi j) ⊆ U j :=
    (tsupport_mul_subset_left (f := (rho j : LoopPlane → ℝ)) (g := phi)).trans (hrho j)
  have hsum : phi = fun p => ∑ j ∈ J, psi j p := by
    funext p
    by_cases hp : phi p = 0
    · simp only [psi, hp, mul_zero, Finset.sum_const_zero]
    · have hpS := subset_tsupport phi hp
      have hsupport : Function.support (fun j : O => rho j p) ⊆ J := by
        intro j hj
        exact hfinite.mem_toFinset.mpr ⟨p, hj, hpS⟩
      have hsumrho : ∑ j ∈ J, rho j p = 1 := by
        rw [← finsum_eq_sum_of_support_subset _ hsupport]
        exact rho.sum_eq_one hpS
      simp only [psi, ← Finset.sum_mul, hsumrho, one_mul]
  let d := fun (f : LoopPlane → ℝ) p => fderiv ℝ f p (EuclideanSpace.single i 1)
  have hd (j : O) : Continuous (d (psi j)) :=
    ((hpsi j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc (j : O) : HasCompactSupport (d (psi j)) :=
    (hcpsi j).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hdLp (j : O) : MemLp (d (psi j)) 2 (volume.restrict O) :=
    ((hd j).memLp_of_hasCompactSupport (hdc j)).restrict O
  have hpLp (j : O) : MemLp (psi j) 2 (volume.restrict O) :=
    ((hpsi j).continuous.memLp_of_hasCompactSupport (hcpsi j)).restrict O
  have hInt0 (j : O) : IntegrableOn (fun p => u p * d (psi j) p) O :=
    hu.integrable_mul (hdLp j)
  have hInt1 (j : O) : IntegrableOn (fun p => v p * psi j p) O :=
    hv.integrable_mul (hpLp j)
  have heq (j : O) : (∫ p in O, u p * d (psi j) p) = -(∫ p in O, v p * psi j p) := by
    have h0 : (∫ p in O, u p * d (psi j) p) =
        ∫ p in U j, u p * d (psi j) p := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hO.measurableSet (hUO j)
      intro p hp
      have hn : p ∉ tsupport (psi j) := fun h => hp.2 (hspsi j h)
      simp only [d, fderiv_of_notMem_tsupport ℝ hn, zero_apply, mul_zero]
    have h1 : (∫ p in O, v p * psi j p) = ∫ p in U j, v p * psi j p := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hO.measurableSet (hUO j)
      intro p hp
      have hn : p ∉ tsupport (psi j) := fun h => hp.2 (hspsi j h)
      rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
    rw [h0, h1]
    exact hw j (psi j) (hpsi j) (hcpsi j) (hspsi j)
  have hdsum (p : LoopPlane) : d phi p = ∑ j ∈ J, d (psi j) p := by
    conv_lhs => rw [hsum]
    dsimp only [d]
    rw [fderiv_fun_sum (fun j _ => (hpsi j).differentiable (by simp) p)]
    simp only [sum_apply]
  change (∫ p in O, u p * d phi p) = -(∫ p in O, v p * phi p)
  calc
    _ = ∑ j ∈ J, ∫ p in O, u p * d (psi j) p := by
      simp_rw [hdsum, Finset.mul_sum]
      exact integral_finsetSum _ (fun j _ => hInt0 j)
    _ = -(∑ j ∈ J, ∫ p in O, v p * psi j p) := by
      simp only [heq, Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      rw [hsum]
      simp_rw [Finset.mul_sum]
      exact (integral_finsetSum _ (fun j _ => hInt1 j)).symm

end PoincareConjecture
