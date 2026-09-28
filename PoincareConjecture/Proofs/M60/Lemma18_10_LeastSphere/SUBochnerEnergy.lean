import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUChartBochner
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUConformality
import PoincareConjecture.Proofs.M60.Mathlib.SUPlaneMeanValue
import PoincareConjecture.Proofs.M01.NormalizationCurvatureBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereEnergyDensity_contDiff (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    ContDiff ℝ ∞ (m60SphereEnergyDensity g f) := by
  have hφ := hf.comp m60SphereParameter_contMDiff
  unfold m60SphereEnergyDensity m60EnergyDensity
  simp only [Matrix.trace_fin_two]
  exact contDiff_const.mul
    ((m60AreaGram_entry_contDiff g hφ 0 0).add (m60AreaGram_entry_contDiff g hφ 1 1))

theorem m60SphereEnergyDensity_eq_gram_of_harmonic (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (z : LoopPlane) (i : Fin 2) :
    m60AreaGram g (f ∘ m60SphereParameter) z i i = m60SphereEnergyDensity g f z := by
  have hgram := m60SphereGram_conformal_of_harmonic g f hf hharm z
  unfold m60SphereEnergyDensity m60EnergyDensity
  rw [Matrix.trace_fin_two, ← hgram.1]
  have hhalf : m60AreaGram g (f ∘ m60SphereParameter) z 0 0 =
      (1 / 2 : ℝ) * (m60AreaGram g (f ∘ m60SphereParameter) z 0 0 +
        m60AreaGram g (f ∘ m60SphereParameter) z 0 0) := by ring
  fin_cases i
  · exact hhalf
  · exact hgram.1.symm.trans hhalf

theorem m60HarmonicSphere_uniform_bochner [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : UnitTwoSphere → M),
      ContMDiff (𝓡 2) (𝓡 n) ∞ f → M60SphereChartHarmonic g f →
      ∀ z : LoopPlane, -K * (m60SphereEnergyDensity g f z) ^ 2 ≤
        M60.suPlaneLaplacian (m60SphereEnergyDensity g f) z := by
  obtain ⟨B, hB, hcurv⟩ := m01_riemannEvaluation_uniform_bound D
  refine ⟨2 * B, by positivity, fun f hf hharm z => ?_⟩
  let φ := f ∘ m60SphereParameter
  let a := m60SphereEnergyDensity g f
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let O := φ ⁻¹' (extChartAt (𝓡 n) (φ z)).source
  have hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ := hf.comp m60SphereParameter_contMDiff
  have hO : IsOpen O := hφ.continuous.isOpen_preimage _ (isOpen_extChartAt_source _)
  have hzO : z ∈ O := mem_extChartAt_source _
  have hnorm (q : LoopPlane) (i : Fin 2) :
      g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q (e i))
        (mfderiv (𝓡 2) (𝓡 n) φ q (e i)) = a q :=
    m60SphereEnergyDensity_eq_gram_of_harmonic g f hf hharm q i
  have hgeom := m60HarmonicChart_laplacian_lower D (φ z) hO hzO (e 0) (e 1)
    hφ.contMDiffOn (fun _ hq => hq) (fun q hq => hharm (φ z) q hq)
    (fun q _ => hnorm q 0)
  let v : Fin 2 → TangentSpace (𝓡 n) (φ z) :=
    fun i => mfderiv (𝓡 2) (𝓡 n) φ z (e i)
  have hnorm' (i : Fin 2) : g.tangentNorm (φ z) (v i) = Real.sqrt (a z) := by
    unfold RiemannianMetric.tangentNorm
    rw [hnorm z i]
  have hR := hcurv (φ z) ![v 0, v 1, v 0, v 1]
  simp only [LeviCivitaData.riemannEvaluation, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, hnorm', mul_one] at hR
  have ha0 : 0 ≤ a z := m60EnergyDensity_nonneg g φ z
  have hprod : B * (Real.sqrt (a z) * (Real.sqrt (a z) *
      (Real.sqrt (a z) * Real.sqrt (a z)))) = B * (a z) ^ 2 := by
    calc
      _ = B * (Real.sqrt (a z) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt ha0]
  rw [hprod] at hR
  have ha : ContDiff ℝ ∞ a := m60SphereEnergyDensity_contDiff g f hf
  have hsec (w : LoopPlane) : fderiv ℝ (fun q => fderiv ℝ a q w) z w =
      fderiv ℝ (fderiv ℝ a) z w w := by
    have hfd : DifferentiableAt ℝ (fderiv ℝ a) z :=
      (ha.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    rw [fderiv_clm_apply hfd (differentiableAt_const w)]
    erw [fderiv_const]
    change fderiv ℝ a z 0 + fderiv ℝ (fderiv ℝ a) z w w =
      fderiv ℝ (fderiv ℝ a) z w w
    rw [map_zero, zero_add]
  rw [hsec, hsec] at hgeom
  change -(2 * B) * (a z) ^ 2 ≤ M60.suPlaneLaplacian a z
  simp only [M60.suPlaneLaplacian, Fin.sum_univ_two]
  have hRu := (le_abs_self (D.curvatureTensor (φ z) (v 0) (v 1) (v 0) (v 1))).trans hR
  change -2 * D.curvatureTensor (φ z) (v 0) (v 1) (v 0) (v 1) ≤ _ at hgeom
  linarith

end PoincareConjecture
