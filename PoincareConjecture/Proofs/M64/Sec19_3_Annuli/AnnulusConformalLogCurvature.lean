import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusLogRegularization
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.TargetChartEstimate












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem conformal_factor_contDiffOn
    (b : M) {φ : LoopPlane → M} {a : LoopPlane → ℝ} {O : Set LoopPlane}
    (hO : IsOpen O) (d : LoopPlane) (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ O)
    (hchart : ∀ q ∈ O, φ q ∈ (extChartAt (𝓡 n) b).source)
    (hdd : ∀ q ∈ O, g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q d)
      (mfderiv (𝓡 2) (𝓡 n) φ q d) = a q) :
    ContDiffOn ℝ ∞ a O := by
  let c := extChartAt (𝓡 n) b
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  have hφq (q : LoopPlane) (hq : q ∈ O) : ContMDiffAt (𝓡 2) (𝓡 n) ∞ φ q :=
    hφ.contMDiffAt (hO.mem_nhds hq)
  have hc (q : LoopPlane) (hq : q ∈ O) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ q) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hchart q hq)
  have hu : ContDiffOn ℝ ∞ u O := by
    intro q hq
    exact (contMDiffAt_iff_contDiffAt.mp ((hc q hq).comp q (hφq q hq))).contDiffWithinAt
  have hdu : ContDiffOn ℝ ∞ (fun q => fderiv ℝ u q d) O :=
    (hu.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hB : ContDiffOn ℝ ∞ (fun q => B (u q)) O :=
    (g.contDiffOn_chartCoefficients b).comp hu (fun q hq => c.map_source (hchart q hq))
  apply ((hB.clm_apply hdu).clm_apply hdu).congr
  intro q hq
  have hd := mfderiv_comp q ((hc q hq).mdifferentiableAt (by simp))
    ((hφq q hq).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have hduq : fderiv ℝ u q d = mfderiv (𝓡 n) (𝓡 n) c (φ q)
      (mfderiv (𝓡 2) (𝓡 n) φ q d) := congrArg (fun L => L d) hd
  rw [hduq]
  exact (hdd q hq).symm.trans (chartCoefficients_apply g b (hchart q hq) _ _).symm






theorem m64ConformalHarmonicChart_log_add_laplacian_lower_bound
    (D : LeviCivitaData g) (b : M)
    {φ : LoopPlane → M} {a : LoopPlane → ℝ} {O : Set LoopPlane}
    {p : LoopPlane} {K ε : ℝ} (hO : IsOpen O) (hp : p ∈ O)
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ O)
    (hchart : ∀ q ∈ O, φ q ∈ (extChartAt (𝓡 n) b).source)
    (hharm :
      let c := extChartAt (𝓡 n) b
      let u := c ∘ φ
      let B := g.pullbackCoefficients c.symm
      ∀ q ∈ O,
        covDerivAlong (christoffelBilinear B) u
            (fun r => fderiv ℝ u r (EuclideanSpace.single (0 : Fin 2) 1))
            (EuclideanSpace.single (0 : Fin 2) 1) q +
          covDerivAlong (christoffelBilinear B) u
            (fun r => fderiv ℝ u r (EuclideanSpace.single (1 : Fin 2) 1))
            (EuclideanSpace.single (1 : Fin 2) 1) q = 0)
    (hdd : ∀ q ∈ O, g.inner (φ q)
      (mfderiv (𝓡 2) (𝓡 n) φ q (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) φ q (EuclideanSpace.single (0 : Fin 2) 1)) = a q)
    (hee : ∀ q ∈ O, g.inner (φ q)
      (mfderiv (𝓡 2) (𝓡 n) φ q (EuclideanSpace.single (1 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) φ q (EuclideanSpace.single (1 : Fin 2) 1)) = a q)
    (hde : ∀ q ∈ O, g.inner (φ q)
      (mfderiv (𝓡 2) (𝓡 n) φ q (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) φ q (EuclideanSpace.single (1 : Fin 2) 1)) = 0)
    (hK : 0 ≤ K) (hε : 0 < ε)
    (hsec : D.sectionalCurvature (φ p)
      (mfderiv (𝓡 2) (𝓡 n) φ p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) φ p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    -2 * K * a p ≤
      fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q
          (EuclideanSpace.single (0 : Fin 2) 1)) p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q
          (EuclideanSpace.single (1 : Fin 2) 1)) p
            (EuclideanSpace.single (1 : Fin 2) 1) := by
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have ha := conformal_factor_contDiffOn b hO b0 hφ hchart hdd
  have hnonneg (q : LoopPlane) (hq : q ∈ O) : 0 ≤ a q := by
    rw [← hdd q hq]
    exact (g.toRiemannianMetric.toCore (φ q)).re_inner_nonneg _
  apply m64Annulus_log_add_laplacian_lower_bound hO hp ha hnonneg hK hε
  intro hpa
  have hlocal := m60ConformalHarmonicChart_estimate D b hO hp b0 b1
    hφ hchart hharm hdd hee hde hpa
  have hsec' := hsec
  unfold LeviCivitaData.sectionalCurvature at hsec'
  rw [hdd p hp, hee p hp, hde p hp, zero_pow (by norm_num), sub_zero] at hsec'
  have hcurv := (div_le_iff₀ (mul_pos hpa hpa)).mp hsec'
  nlinarith

end PoincareConjecture
