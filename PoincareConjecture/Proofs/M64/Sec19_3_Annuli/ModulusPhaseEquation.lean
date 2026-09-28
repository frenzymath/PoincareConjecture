import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CirclePhaseDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusCircleCurrent

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64CirclePhase_modulus_equation
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusInterior)
    {L : LoopPlane → ℝ} (hL : ContDiffOn ℝ ∞ L m64AnnulusInterior)
    (hquot : EqOn (P.circle.quotient ∘ L) (Prod.snd ∘ A.map) m64AnnulusInterior)
    {p : LoopPlane} (hp : p ∈ m64AnnulusInterior) :
    r * fderiv ℝ (fderiv ℝ L) p (EuclideanSpace.single (0 : Fin 2) 1)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fderiv ℝ L) p (EuclideanSpace.single (1 : Fin 2) 1)
        (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
  have hreg := hL.contDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)
  have hdL : DifferentiableAt ℝ (fderiv ℝ L) p :=
    (hreg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hcol (i : Fin 2) : (fun q => fderiv ℝ L q (EuclideanSpace.single i 1)) =ᶠ[𝓝 p]
      m64AnnulusCircleCurrent P t A.map i := by
    filter_upwards [isOpen_m64AnnulusInterior.mem_nhds hp] with q hq
    apply m64CirclePhase_current P t
      ((hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hq)).mdifferentiableAt (by simp))
      ((hL.contDiffAt (isOpen_m64AnnulusInterior.mem_nhds hq)).differentiableAt (by simp))
    filter_upwards [isOpen_m64AnnulusInterior.mem_nhds hq] with z hz
    exact hquot hz
  have hder (i : Fin 2) :
      fderiv ℝ (fderiv ℝ L) p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
        fderiv ℝ (m64AnnulusCircleCurrent P t A.map i) p (EuclideanSpace.single i 1) := by
    have h := congrArg (fun B : LoopPlane →L[ℝ] ℝ => B (EuclideanSpace.single i 1))
      (hcol i).fderiv_eq
    rw [fderiv_clm_apply hdL (differentiableAt_const _)] at h
    simpa using h
  rw [hder 0, hder 1]
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hdiv :=
    m64AnnulusCircleCurrent_divergence_zero_of_modulus_minimum P P.circle.positive t A hr
      hminimum hconformal hA (x := p 0) (s := p 1) (hpoint.symm ▸ hp)
  rw [hpoint] at hdiv
  exact hdiv

end PoincareConjecture
