import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalHarmonicObservation










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ




theorem m64LocalHarmonic_observation_vector_bound [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    {e : M → EuclideanSpace ℝ (Fin k)} (he : ContMDiff (𝓡 n) (𝓡 k) ∞ e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : M) (u : LoopPlane → EuclideanSpace ℝ (Fin n))
      (f : LoopPlane → M) (p : LoopPlane), ContDiffAt ℝ 2 u p →
      u p ∈ (extChartAt (𝓡 n) q).target →
      ((extChartAt (𝓡 n) q).symm ∘ u) =ᶠ[𝓝 p] f →
      (∑ i : Fin 2, covDerivAlong
        (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) q).symm)) u
        (fun x => fderiv ℝ u x (b i)) (b i) p) = 0 →
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ (e ∘ f)) p (b i) (b i)‖ ≤
        B * m60EnergyDensity g f p := by
  have hs (j : Fin k) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => e x j) :=
    (contMDiff_iff_contDiff.mpr (EuclideanSpace.proj j).contDiff).comp he
  choose B hB hbound using fun j : Fin k =>
    D.exists_metric_hessian_bound_on_compact (hs j) isCompact_univ
  refine ⟨∑ j, 2 * B j, Finset.sum_nonneg (fun j _ => mul_nonneg (by norm_num) (hB j)),
    fun q u f p hu hut hmap hharm => ?_⟩
  have hscalar (j : Fin k) :
      |∑ i : Fin 2, fderiv ℝ (fderiv ℝ ((fun x => e x j) ∘ f)) p (b i) (b i)| ≤
        (2 * B j) * m60EnergyDensity g f p := by
    rw [m64LocalHarmonic_scalar_observation_laplacian D (hs j) q hu hut hmap hharm]
    calc
      _ ≤ ∑ i : Fin 2, |D.hessian (fun x => e x j) (f p)
          (mfderiv (𝓡 2) (𝓡 n) f p (b i)) (mfderiv (𝓡 2) (𝓡 n) f p (b i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, B j * m60AreaGram g f p i i :=
        Finset.sum_le_sum fun i _ => hbound j (f p) (mem_univ _) _
      _ = _ := by
        simp only [m60EnergyDensity, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
        ring
  have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) q).symm (u p) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hut)
  have hf : ContMDiffAt (𝓡 2) (𝓡 n) 2 f p :=
    ((hcs.of_le (WithTop.coe_le_coe.mpr le_top)).comp p hu.contMDiffAt
      ).congr_of_eventuallyEq hmap.symm
  have hU : ContDiffAt ℝ 2 (e ∘ f) p := contMDiffAt_iff_contDiffAt.mp
    ((he.of_le (WithTop.coe_le_coe.mpr le_top)).contMDiffAt.comp p hf)
  let U := e ∘ f
  let W := ∑ i : Fin 2, fderiv ℝ (fderiv ℝ U) p (b i) (b i)
  let basis := EuclideanSpace.basisFun (Fin k) ℝ
  have hc (j : Fin k) : W j =
      ∑ i : Fin 2, fderiv ℝ (fderiv ℝ ((fun x => e x j) ∘ f)) p (b i) (b i) := by
    simp only [W, WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    let L := EuclideanSpace.proj (𝕜 := ℝ) j
    change _ = fderiv ℝ (fderiv ℝ (L ∘ U)) p _ _
    rw [M60.second_fderiv_comp (L.contDiff.contDiffAt : ContDiffAt ℝ 2 L (U p)) hU]
    have hL : fderiv ℝ L = fun _ => L := funext fun _ => L.fderiv
    rw [hL]
    erw [fderiv_const]
    change _ = 0 + _
    exact (zero_add _).symm
  calc
    ‖W‖ = ‖∑ j, basis.repr W j • basis j‖ := congrArg norm (basis.sum_repr W).symm
    _ ≤ ∑ j, ‖basis.repr W j • basis j‖ := norm_sum_le _ _
    _ = ∑ j, |W j| := by
      simp only [norm_smul, basis, EuclideanSpace.basisFun_repr, Real.norm_eq_abs,
        OrthonormalBasis.norm_eq_one, mul_one]
    _ ≤ ∑ j, (2 * B j) * m60EnergyDensity g f p := by
      apply Finset.sum_le_sum
      intro j _
      rw [hc j]
      exact hscalar j
    _ = _ := (Finset.sum_mul _ _ _).symm

end PoincareConjecture
