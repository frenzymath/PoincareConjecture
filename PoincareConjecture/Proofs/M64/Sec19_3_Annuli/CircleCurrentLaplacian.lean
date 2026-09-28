import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCircleConservation
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture






theorem m64CircleCurrent_weighted_second_derivative_zero
    {J : Fin 2 → LoopPlane → ℝ} {U : Set LoopPlane} (hU : IsOpen U)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (J i) U) (alpha beta : ℝ)
    (hclosed : ∀ p ∈ U,
      fderiv ℝ (J 1) p (EuclideanSpace.single (0 : Fin 2) 1) =
        fderiv ℝ (J 0) p (EuclideanSpace.single (1 : Fin 2) 1))
    (hdiv : ∀ p ∈ U,
      alpha * fderiv ℝ (J 0) p (EuclideanSpace.single (0 : Fin 2) 1) +
        beta * fderiv ℝ (J 1) p (EuclideanSpace.single (1 : Fin 2) 1) = 0)
    {p : LoopPlane} (hp : p ∈ U) :
    alpha * fderiv ℝ (fderiv ℝ (J 0)) p
        (EuclideanSpace.single (0 : Fin 2) 1) (EuclideanSpace.single (0 : Fin 2) 1) +
      beta * fderiv ℝ (fderiv ℝ (J 0)) p
        (EuclideanSpace.single (1 : Fin 2) 1) (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
  let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hj (i : Fin 2) := (hJ i).contDiffAt (hU.mem_nhds hp)
  have hjd (i : Fin 2) : DifferentiableAt ℝ (fderiv ℝ (J i)) p :=
    ((hj i).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hpart (i : Fin 2) (v : LoopPlane) :
      DifferentiableAt ℝ (fun q => fderiv ℝ (J i) q v) p :=
    (hjd i).clm_apply (differentiableAt_const v)
  have hpartfd (i : Fin 2) (v w : LoopPlane) :
      fderiv ℝ (fun q => fderiv ℝ (J i) q v) p w = fderiv ℝ (fderiv ℝ (J i)) p w v := by
    rw [fderiv_clm_apply (hjd i) (differentiableAt_const v)]
    simp
  have hc : (fun q => fderiv ℝ (J 1) q e0) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ (J 0) q e1) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hclosed q hq
  have hcd := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L e1) hc.fderiv_eq
  simp only [hpartfd] at hcd
  have hd : (fun q => alpha * fderiv ℝ (J 0) q e0 + beta * fderiv ℝ (J 1) q e1) =ᶠ[𝓝 p]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hdiv q hq
  have hdd := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L e0) hd.fderiv_eq
  change (fderiv ℝ ((fun q => alpha * fderiv ℝ (J 0) q e0) +
    (fun q => beta * fderiv ℝ (J 1) q e1)) p) e0 = _ at hdd
  rw [fderiv_add ((hpart 0 e0).const_mul alpha) ((hpart 1 e1).const_mul beta),
    fderiv_const_mul (hpart 0 e0) alpha, fderiv_const_mul (hpart 1 e1) beta] at hdd
  simp only [add_apply, smul_apply, smul_eq_mul, hpartfd,
    fderiv_const_apply, zero_apply] at hdd
  have hsymm := (hj 1).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) e0 e1
  change fderiv ℝ (fderiv ℝ (J 1)) p e0 e1 = fderiv ℝ (fderiv ℝ (J 1)) p e1 e0 at hsymm
  rw [hsymm, hcd] at hdd
  exact hdd

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}






theorem m64AnnulusCircleCurrent_horizontal_harmonic_of_conformal_minimum
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusInterior) :
    InnerProductSpace.HarmonicOnNhd (m64AnnulusCircleCurrent P t A.map 0) m64AnnulusInterior := by
  let J := m64AnnulusCircleCurrent P t A.map
  have hJ (i : Fin 2) : ContDiffOn ℝ ∞ (J i) m64AnnulusInterior := by
    intro p hp
    exact (m64AnnulusCircleCurrent_contDiffAt P t
      (hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)) i).contDiffWithinAt
  have hpoint (p : LoopPlane) : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  have hclosed (p : LoopPlane) (hp : p ∈ m64AnnulusInterior) :
      fderiv ℝ (J 1) p (EuclideanSpace.single (0 : Fin 2) 1) =
        fderiv ℝ (J 0) p (EuclideanSpace.single (1 : Fin 2) 1) := by
    simpa only [hpoint] using m64AnnulusCircleCurrent_closed P t isOpen_m64AnnulusInterior hA
      (x := p 0) (s := p 1) (hpoint p ▸ hp)
  have hdiv (p : LoopPlane) (hp : p ∈ m64AnnulusInterior) :
      (1 : ℝ) * fderiv ℝ (J 0) p (EuclideanSpace.single (0 : Fin 2) 1) +
        (1 : ℝ) * fderiv ℝ (J 1) p (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
    simpa only [one_mul, hpoint] using
      m64AnnulusCircleCurrent_divergence_zero_of_conformal_minimum P hcirc t A
        hminimum hconformal hA (x := p 0) (s := p 1) (hpoint p ▸ hp)
  intro p hp
  refine ⟨((hJ 0).contDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)).of_le
    (by norm_cast : (2 : ℕ∞ω) ≤ ∞), ?_⟩
  filter_upwards [isOpen_m64AnnulusInterior.mem_nhds hp] with q hq
  have h := m64CircleCurrent_weighted_second_derivative_zero
    isOpen_m64AnnulusInterior hJ 1 1 hclosed hdiv hq
  change Laplacian.laplacian (J 0) q = 0
  simpa only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (J 0) (EuclideanSpace.basisFun (Fin 2) ℝ), Fin.sum_univ_two,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Pi.zero_apply, EuclideanSpace.basisFun_apply, one_mul] using h

end PoincareConjecture
