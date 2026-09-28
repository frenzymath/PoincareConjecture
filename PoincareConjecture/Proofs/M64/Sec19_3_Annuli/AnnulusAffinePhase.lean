import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClosedStripCirclePhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusPhaseEquation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusAffinePhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusPeriodicHarmonicTransport






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





theorem m64Annulus_exists_nonzero_affine_phase
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hAc : ContinuousOn A.map {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hAi : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusOpenStrip)
    (hzero : ∀ x, (c0 x).2 = P.circle.quotient 0)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < circumference)
    (hone : ∀ x, (c1 x).2 = P.circle.quotient delta) :
    ∃ c : ℝ, c ≠ 0 ∧ P.circle.quotient c = P.circle.quotient delta ∧
      ∀ p, p 1 ∈ Icc (0 : ℝ) 1 → (A.map p).2 = P.circle.quotient (c * p 1) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    contMDiff_snd.comp P.charts.to_product_smooth
  obtain ⟨L, c, hL, hLi, hquot, h0, h1, hperiod, hc⟩ :=
    M64.closed_strip_exists_circle_phase P.circle (Prod.snd ∘ A.map)
      (hsnd.continuous.comp_continuousOn hAc) (hsnd.comp_contMDiffOn hAi)
      (fun x s => congrArg Prod.snd (A.periodic x s))
      (fun x => by simp only [Function.comp_apply, A.lower_boundary]; exact hzero x)
      (fun x => by simp only [Function.comp_apply, A.upper_boundary]; exact hone x)
  have hsub : m64AnnulusInterior ⊆ m64AnnulusOpenStrip := by
    intro p hp
    exact hp 1 (mem_univ _)
  have hEq : ∀ p ∈ m64AnnulusInterior,
      r * fderiv ℝ (fderiv ℝ L) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ L) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
    intro p hp
    apply m64CirclePhase_modulus_equation P t A hr hminimum hconformal
      (hAi.mono hsub) (hLi.mono hsub) _ hp
    intro q hq
    exact hquot q ⟨(hsub hq).1.le, (hsub hq).2.le⟩
  have hstrip := m64PeriodicModulus_equation_on_strip_of_open_regularity hLi hperiod hEq
  have haff := m64PeriodicModulus_eq_affine_of_constant_boundary hr hL.continuousOn
    hLi hstrip hperiod h0 h1
  have hc0 : c ≠ 0 := by
    intro he
    have hz : (delta : AddCircle circumference) = 0 := by
      simpa only [he, M62.CircleGeometry.quotient, AddCircle.coe_zero] using hc.symm
    exact hdelta.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hdelta.le, hsmall⟩).mp hz)
  refine ⟨c, hc0, hc, fun p hp => ?_⟩
  exact (hquot p hp).symm.trans (congrArg P.circle.quotient (haff p hp))

end PoincareConjecture
