import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCircleCurrent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusIntrinsicTension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64AnnulusCircleCurrent_closed
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ f O)
    {x s : ℝ} (hp : annulusPoint x s ∈ O) :
    fderiv ℝ (m64AnnulusCircleCurrent P t f 1) (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) =
      fderiv ℝ (m64AnnulusCircleCurrent P t f 0) (annulusPoint x s)
        (EuclideanSpace.single (1 : Fin 2) 1) := by
  have hfp := hf.contMDiffAt (hO.mem_nhds hp)
  rw [m64AnnulusCircleCurrent_horizontal_derivative P t hfp,
    m64AnnulusCircleCurrent_vertical_derivative P t hfp]
  have hxy := M62.pullback_congr (P.flow.connection t)
    (γ := fun y => f (annulusPoint y s))
    (Y := fun y => mfderiv (𝓡 2) (𝓡 (n + 1)) f (annulusPoint y s)
      (EuclideanSpace.single (1 : Fin 2) 1))
    (Z := fun y => curveVelocity (fun r => f (annulusPoint y r)) s) (x := x) (by
      filter_upwards [(m64AnnulusPoint_horizontal_hasDerivAt s x).continuousAt
        (hO.mem_nhds hp)] with y hy
      exact (m64Annulus_vertical_velocity
        ((hf.contMDiffAt (hO.mem_nhds hy)).mdifferentiableAt (by simp))).symm)
  have hyx := M62.pullback_congr (P.flow.connection t)
    (γ := fun r => f (annulusPoint x r))
    (Y := fun r => mfderiv (𝓡 2) (𝓡 (n + 1)) f (annulusPoint x r)
      (EuclideanSpace.single (0 : Fin 2) 1))
    (Z := fun r => curveVelocity (fun y => f (annulusPoint y r)) x) (x := s) (by
      filter_upwards [(m64AnnulusPoint_vertical_hasDerivAt x s).continuousAt
        (hO.mem_nhds hp)] with r hr
      exact (m64Annulus_horizontal_velocity
        ((hf.contMDiffAt (hO.mem_nhds hr)).mdifferentiableAt (by simp))).symm)
  have hpoint : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (fun q : ℝ × ℝ => annulusPoint q.1 q.2) := by
    apply contMDiff_iff_contDiff.mpr
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  have htor := M62.pullback_velocity_commute (P.flow.connection t)
    (fun y r => f (annulusPoint y r)) (hO.preimage hpoint.continuous)
    (hf.comp hpoint.contMDiffOn (fun _ hq => hq)) hp
  rw [hxy, hyx, htor]

variable [T2Space M] [CompactSpace M]

theorem m64AnnulusCircleCurrent_divergence_zero_of_conformal_minimum
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusInterior)
    {x s : ℝ} (hp : annulusPoint x s ∈ m64AnnulusInterior) :
    fderiv ℝ (m64AnnulusCircleCurrent P t A.map 0) (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      fderiv ℝ (m64AnnulusCircleCurrent P t A.map 1) (annulusPoint x s)
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
    (γ := fun r => A.map (annulusPoint x r))
    (Y := fun r => mfderiv (𝓡 2) (𝓡 (n + 1)) A.map (annulusPoint x r)
      (EuclideanSpace.single (1 : Fin 2) 1))
    (Z := fun r => curveVelocity (fun z => A.map (annulusPoint x z)) r) (x := s) (by
      filter_upwards [(m64AnnulusPoint_vertical_hasDerivAt x s).continuousAt
        (isOpen_m64AnnulusInterior.mem_nhds hp)] with r hr
      exact (m64Annulus_vertical_velocity
        ((hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hr)).mdifferentiableAt
          (by simp))).symm)
  rw [hxx, hyy]
  have hzero := m64Annulus_intrinsic_tension_eq_zero_of_conformal_minimum
    (P.flow.connection t) A hminimum hconformal hA hp
  have hscalar := congrArg (fun v => (P.flow.metric t).inner (A.map (annulusPoint x s)) v
    (P.charts.circleUnit (A.map (annulusPoint x s)))) hzero
  simpa only [map_add, add_apply, map_zero, zero_apply] using hscalar

end PoincareConjecture
