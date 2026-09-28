import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusIntrinsicTension
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CircleCurrentLaplacian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64AnnulusCircleCurrent_divergence_zero_of_modulus_minimum
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusInterior)
    {x s : ℝ} (hp : annulusPoint x s ∈ m64AnnulusInterior) :
    r * fderiv ℝ (m64AnnulusCircleCurrent P t A.map 0) (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (m64AnnulusCircleCurrent P t A.map 1) (annulusPoint x s)
        (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  have hfp := hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)
  rw [m64AnnulusCircleCurrent_horizontal_derivative P t hfp,
    m64AnnulusCircleCurrent_vertical_derivative P t hfp]
  have hxx := M62.pullback_congr (P.flow.connection t)
    (γ := fun y => A.map (annulusPoint y s))
    (Y := fun y => mfderiv (𝓡 2) (𝓡 (n + 1)) A.map (annulusPoint y s)
      (EuclideanSpace.single (0 : Fin 2) 1))
    (Z := fun y => curveVelocity (fun z => A.map (annulusPoint z s)) y) (x := x) (by
      filter_upwards [(m64AnnulusPoint_horizontal_hasDerivAt s x).continuousAt
        (isOpen_m64AnnulusInterior.mem_nhds hp)] with y hy
      exact (m64Annulus_horizontal_velocity
        ((hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hy)).mdifferentiableAt
          (by simp))).symm)
  have hyy := M62.pullback_congr (P.flow.connection t)
    (γ := fun y => A.map (annulusPoint x y))
    (Y := fun y => mfderiv (𝓡 2) (𝓡 (n + 1)) A.map (annulusPoint x y)
      (EuclideanSpace.single (1 : Fin 2) 1))
    (Z := fun y => curveVelocity (fun z => A.map (annulusPoint x z)) y) (x := s) (by
      filter_upwards [(m64AnnulusPoint_vertical_hasDerivAt x s).continuousAt
        (isOpen_m64AnnulusInterior.mem_nhds hp)] with y hy
      exact (m64Annulus_vertical_velocity
        ((hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hy)).mdifferentiableAt
          (by simp))).symm)
  rw [hxx, hyy]
  have hzero := m64Annulus_intrinsic_tension_eq_zero_of_modulus_minimum
    (P.flow.connection t) A hr hminimum hconformal hA hp
  have hscalar := congrArg (fun v => (P.flow.metric t).inner (A.map (annulusPoint x s)) v
    (P.charts.circleUnit (A.map (annulusPoint x s)))) hzero
  simpa only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, map_zero, zero_apply]
    using hscalar

theorem m64AnnulusCircleCurrent_horizontal_equation_of_modulus_minimum
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusInterior)
    {p : LoopPlane} (hp : p ∈ m64AnnulusInterior) :
    r * fderiv ℝ (fderiv ℝ (m64AnnulusCircleCurrent P t A.map 0)) p
        (EuclideanSpace.single (0 : Fin 2) 1) (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fderiv ℝ (m64AnnulusCircleCurrent P t A.map 0)) p
        (EuclideanSpace.single (1 : Fin 2) 1) (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
  let J := m64AnnulusCircleCurrent P t A.map
  have hJ (i : Fin 2) : ContDiffOn ℝ ∞ (J i) m64AnnulusInterior := by
    intro q hq
    exact (m64AnnulusCircleCurrent_contDiffAt P t
      (hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hq)) i).contDiffWithinAt
  have hpoint (q : LoopPlane) : annulusPoint (q 0) (q 1) = q := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  have hclosed (q : LoopPlane) (hq : q ∈ m64AnnulusInterior) :
      fderiv ℝ (J 1) q (EuclideanSpace.single (0 : Fin 2) 1) =
        fderiv ℝ (J 0) q (EuclideanSpace.single (1 : Fin 2) 1) := by
    simpa only [hpoint] using m64AnnulusCircleCurrent_closed P t isOpen_m64AnnulusInterior hA
      (x := q 0) (s := q 1) (hpoint q ▸ hq)
  have hdiv (q : LoopPlane) (hq : q ∈ m64AnnulusInterior) :
      r * fderiv ℝ (J 0) q (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (J 1) q (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
    simpa only [hpoint] using
      m64AnnulusCircleCurrent_divergence_zero_of_modulus_minimum P hcirc t A hr
        hminimum hconformal hA (x := q 0) (s := q 1) (hpoint q ▸ hq)
  exact m64CircleCurrent_weighted_second_derivative_zero
    isOpen_m64AnnulusInterior hJ r r⁻¹ hclosed hdiv hp

end PoincareConjecture
