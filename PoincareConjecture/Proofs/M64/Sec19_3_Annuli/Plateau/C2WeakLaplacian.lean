import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTransverseC1










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff SchwartzMap

namespace PoincareConjecture




theorem m64C2_classical_laplacian_weak {N : ℕ} {U : Set LoopPlane}
    (hU : IsOpen U)
    (X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) U)
    (hX : ContDiffOn ℝ 2 X.value U)
    (hD : ∀ i, MemLp (X.derivative i) 2 (volume.restrict U)) {C : ℝ}
    (hgrowth : ∀ z ∈ U,
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2) :
    let f := fun k z => (∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) k
    (∀ k, IntegrableOn (f k) U) ∧
      (∀ k, ∀ᵐ z ∂volume.restrict U,
        |f k z| ≤ C * ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ∧
      ∀ k (test : 𝓢(LoopPlane, ℝ)), HasCompactSupport test → tsupport test ⊆ U →
        (∫ z in U, ∑ i : Fin 2, X.derivative i z k *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            -(∫ z in U, f k z * test z) := by
  classical
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let f := fun k z => (∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) k
  have hX1 : ContDiffOn ℝ 1 (id ∘ X.value) U := hX.of_le (by norm_num)
  have hcol (i : Fin 2) : (fun z => fderiv ℝ X.value z (b i))
      =ᵐ[volume.restrict U] X.derivative i :=
    M65Euler.classical_derivative_eq_weak hU X X.value hX1 (ae_of_all _ fun _ => rfl) i
  have hsumI : IntegrableOn (fun z => ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) U :=
    integrable_finsetSum _ (fun i _ => (hD i).norm.integrable_sq)
  have hDX : ContDiffOn ℝ 1 (fderiv ℝ X.value) U :=
    hX.fderiv_of_isOpen hU (by norm_num)
  have hfc (k : Fin N) : ContinuousOn (f k) U := by
    have h2 := hDX.fderiv_of_isOpen (m := 0) hU (by norm_num)
    change ContinuousOn ((EuclideanSpace.proj (𝕜 := ℝ) k) ∘
      fun z => ∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) U
    apply (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn
    apply continuousOn_finsetSum
    intro i _
    exact (h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hfg (k : Fin N) : ∀ᵐ z ∂volume.restrict U,
      |f k z| ≤ C * ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2 := by
    filter_upwards [ae_all_iff.mpr hcol, ae_restrict_mem hU.measurableSet] with z hd hz
    have hp := PiLp.norm_apply_le
      (∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) k
    rw [Real.norm_eq_abs] at hp
    exact hp.trans (by simpa only [b, hd] using hgrowth z hz)
  refine ⟨(fun k => (hsumI.const_mul C).mono'
    ((hfc k).aestronglyMeasurable hU.measurableSet)
      (by simpa only [Real.norm_eq_abs] using hfg k)), hfg, ?_⟩
  intro k test hc hs
  let row := fun i z => (fderiv ℝ X.value z (b i)) k
  have hrow (i : Fin 2) : ContDiffOn ℝ 1 (row i) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn
      (hDX.clm_apply contDiffOn_const)
  have hdrow (i : Fin 2) (z : LoopPlane) (hz : z ∈ U) :
      fderiv ℝ (row i) z (b i) = (fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) k := by
    have hDf : DifferentiableAt ℝ (fderiv ℝ X.value) z :=
      (hDX.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
    have hd := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp z
      (hDf.clm_apply (differentiableAt_const (b i))).hasFDerivAt
    have hh := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (b i)) hd.fderiv
    change fderiv ℝ (row i) z (b i) =
      (fderiv ℝ (fun z => fderiv ℝ X.value z (b i)) z (b i)) k at hh
    rw [fderiv_clm_apply hDf (differentiableAt_const (b i))] at hh
    simpa only [ContinuousLinearMap.comp_apply, fderiv_fun_const, Pi.zero_apply, zero_apply,
      map_zero, add_apply, zero_add, ContinuousLinearMap.flip_apply] using hh
  have hi (i : Fin 2) := M65Euler.classical_scalar_weak_identity hU (hrow i) test hc hs (b i)
  have hweak : (∫ z in U, ∑ i : Fin 2, row i z * fderiv ℝ test z (b i)) =
      -(∫ z in U, f k z * test z) := by
    rw [integral_finsetSum _ (fun i _ => (hi i).2.1)]
    have hfrow : (fun z => f k z * test z) =ᵐ[volume.restrict U]
        fun z => ∑ i : Fin 2, fderiv ℝ (row i) z (b i) * test z := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      simp only [hdrow _ z hz, f, Fin.sum_univ_two, PiLp.add_apply, add_mul]
    rw [integral_congr_ae hfrow, integral_finsetSum _ (fun i _ => (hi i).1)]
    simp_rw [(hi _).2.2]
    rw [Finset.sum_neg_distrib, neg_neg]
  calc
    _ = ∫ z in U, ∑ i : Fin 2, row i z * fderiv ℝ test z (b i) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hcol] with z hz
      simp only [row, hz, b]
    _ = _ := hweak

end PoincareConjecture
