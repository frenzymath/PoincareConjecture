import PoincareConjecture.Proofs.M60.Mathlib.CompactSupportIntegralDerivative
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M60

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]



theorem continuousOn_timeDerivative_of_contMDiffOn
    {F : ℝ × X → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hF : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ F (J ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × X => fderiv ℝ (fun t => F (t, q.2)) q.1 1) (J ×ˢ univ) := by
  intro q hq
  have hFq := hF.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds hq)
  let f := fun (r : ℝ × X) (t : ℝ) => F (t, r.2)
  have hf : ContMDiffAt (((𝓘(ℝ, ℝ)).prod I).prod (𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) (q, q.1) :=
    hFq.comp (q, q.1) (contMDiffAt_snd.prodMk contMDiffAt_fst.snd)
  have hd := hf.mfderiv (m := ∞) f Prod.fst contMDiffAt_fst (by simp)
  simp only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] at hd
  exact (hd.clm_apply contMDiffAt_const).continuousAt.continuousWithinAt




theorem differentiableAt_integral_of_contMDiffOn [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {F : ℝ × X → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hF : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ F
      (Ioo (-ε) ε ×ˢ univ)) :
    DifferentiableAt ℝ (fun s => ∫ x, F (s, x) ∂μ) 0 := by
  let G := fun s x => fderiv ℝ (fun t => F (t, x)) s 1
  have hG : ContinuousOn (Function.uncurry G) (Ioo (-ε) ε ×ˢ univ) :=
    continuousOn_timeDerivative_of_contMDiffOn isOpen_Ioo hF
  have hslice (s : ℝ) (hs : s ∈ Ioo (-ε) ε) : Continuous (fun x => F (s, x)) :=
    hF.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hs, mem_univ x⟩)
  have hdiff (s : ℝ) (hs : s ∈ Ioo (-ε) ε) (x : X) :
      HasDerivAt (fun t => F (t, x)) (G s x) s := by
    have hsmooth : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ F (s, x) := hF.contMDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ x⟩)
    have htime : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t => F (t, x)) s :=
      hsmooth.comp s (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (contMDiffAt_iff_contDiffAt.mp htime).differentiableAt (by simp)
      |>.hasFDerivAt.hasDerivAt
  exact (hasDerivAt_integral_of_common_compact_support (μ := μ) isCompact_univ hε
    hslice hG hdiff (fun _ _ x hx => False.elim (hx (mem_univ x)))).2.differentiableAt

end PoincareConjecture.M60
