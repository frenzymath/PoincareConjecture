import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityGeometry
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Interior

theorem exists_linear_local_inverse {T E : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {j : T → E} {a : T} (hj : ContDiffAt ℝ ∞ j a)
    (hinj : Function.Injective (fderiv ℝ j a)) :
    ∃ (L : E →L[ℝ] T) (k : T → T), k 0 = a ∧ ContDiffAt ℝ ∞ k 0 ∧
      ∀ᶠ y in 𝓝 a, k (L (j y - j a)) = y := by
  let : CompleteSpace T := FiniteDimensional.complete ℝ T
  let A := fderiv ℝ j a
  let L := gramLeftInverse A
  let F (y : T) := L (j y - j a)
  have hF : ContDiffAt ℝ ∞ F a :=
    L.contDiff.contDiffAt.comp a (hj.sub contDiffAt_const)
  have hD : HasFDerivAt F (ContinuousLinearEquiv.refl ℝ T : T →L[ℝ] T) a := by
    have hd := L.hasFDerivAt.comp a
      ((hj.differentiableAt (by simp)).hasFDerivAt.sub_const (j a))
    convert! hd using 1
    ext v
    exact (gramLeftInverse_apply_image A hinj v).symm
  have hzero : F a = 0 := by simp [F]
  let k := hF.localInverse hD (by simp)
  refine ⟨L, k, ?_, ?_, ?_⟩
  · simpa only [hzero] using hF.localInverse_apply_image hD (by simp)
  · simpa only [hzero] using hF.to_localInverse hD (by simp)
  · exact (hF.hasStrictFDerivAt' hD (by simp)).eventually_left_inverse

end PoincareConjecture.M65Interior

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}

theorem m65Embedding_exists_linear_chart (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (p : M) :
    ∃ (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (P : EuclideanSpace ℝ (Fin 3) → M),
      P 0 = p ∧ ContMDiffAt (𝓡 3) (𝓡 3) ∞ P 0 ∧
        ∀ᶠ q in 𝓝 p, P (L (e q - e p)) = q := by
  let c := extChartAt (𝓡 3) p
  let a := c p
  have ha : a ∈ c.target := c.map_source (mem_extChartAt_source p)
  have hpa : c.symm a = p := c.left_inv (mem_extChartAt_source p)
  have hpsi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm a :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds ha)
  have hj : ContDiffAt ℝ ∞ (e ∘ c.symm) a :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp a hpsi)
  have hA : Function.Injective (fderiv ℝ (e ∘ c.symm) a) := by
    have hleft := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm ha
    have hright := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ha
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hleft hright
    have hbij := (ContinuousLinearMap.IsInvertible.of_inverse hright hleft).bijective
    rw [← mfderiv_eq_fderiv, mfderiv_comp a (he.contMDiffAt.mdifferentiableAt (by simp))
      (hpsi.mdifferentiableAt (by simp))]
    exact (hinj _).comp hbij.injective
  obtain ⟨L, k, hk, hksmooth, hkinv⟩ := M65Interior.exists_linear_local_inverse hj hA
  refine ⟨L, c.symm ∘ k, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, hk, hpa]
  · have hpik : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (k 0) := hk ▸ hpsi
    exact hpik.comp 0 hksmooth.contMDiffAt
  · have hc : Tendsto c (𝓝 p) (𝓝 a) :=
      (contMDiffAt_extChartAt (n := ∞)).continuousAt
    filter_upwards [hc.eventually hkinv,
      (isOpen_extChartAt_source (I := 𝓡 3) p).mem_nhds (mem_extChartAt_source p)]
      with q hq hsource
    have hqinv : c.symm (c q) = q := c.left_inv hsource
    simp only [Function.comp_apply, hqinv, hpa] at hq
    change c.symm (k (L (e q - e p))) = q
    rw [hq, hqinv]

end PoincareConjecture
