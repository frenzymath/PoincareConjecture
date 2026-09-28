import PoincareConjecture.Proofs.M09.SmoothSquareFirstVariation
import PoincareConjecture.Proofs.M09.SmoothSquareAction

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
theorem fderiv_smoothSquareFamily_action [ConnectedSpace M]
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (f : E × ℝ → M) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U)
    (x0 v : E) (hsegment : ∀ s ∈ Set.Icc 0 (Real.sqrt b), (x0, s) ∈ U)
    (hcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), f (x0, s) = A.squareFamily Z s) :
    fderiv ℝ (fun x ↦ backwardLLength F T 0 b (fun t ↦ f (x, Real.sqrt t))) x0 v =
      (F.metric (T - b)).inner (A.squareFamily Z (Real.sqrt b))
        (curveVelocity (A.squareFamily Z) (Real.sqrt b))
        (curveVelocity (fun r ↦ f (x0 + r • v, Real.sqrt b)) 0) -
      (F.metric T).inner p ((2 : ℝ) • Z)
        (curveVelocity (fun r ↦ f (x0 + r • v, 0)) 0) := by
  let B : E → ℝ := fun x ↦ backwardLLength F T 0 b (fun t ↦ f (x, Real.sqrt t))
  have hsmooth : ContDiffAt ℝ ∞ B x0 := by
    have h := contDiffAt_smoothSquareFamily_action F hM04 T τmax hτmax hwindow
      f U hU hf (x0, b) ⟨hb, hmax⟩ (fun r hr ↦ hsegment _
        ⟨mul_nonneg (Real.sqrt_nonneg b) hr.1,
          mul_le_of_le_one_right (Real.sqrt_nonneg b) hr.2⟩)
    exact h.comp x0 (contDiffAt_id.prodMk contDiffAt_const)
  have hline : HasDerivAt (fun r : ℝ ↦ x0 + r • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x0
  have hactual : HasDerivAt (fun r : ℝ ↦ B (x0 + r • v)) (fderiv ℝ B x0 v) 0 := by
    have hB : DifferentiableAt ℝ B (x0 + (0 : ℝ) • v) := by
      simpa only [zero_smul, add_zero] using hsmooth.differentiableAt (by simp)
    simpa only [Function.comp_def, zero_smul, add_zero] using
      hB.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  let k : ℝ × ℝ → E × ℝ := fun z ↦ (x0 + z.2 • v, z.1)
  let U' := k ⁻¹' U
  have hk : ContDiff ℝ ∞ k :=
    (contDiff_const.add (contDiff_snd.smul contDiff_const)).prodMk contDiff_fst
  have hU' : IsOpen U' := hU.preimage hk.continuous
  have hf' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ (f ∘ k) U' := by
    convert! hf.comp hk.contMDiff.contMDiffOn (fun _ hz ↦ hz) using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ s ∈ Set.Icc 0 (Real.sqrt b), (s, r) ∈ U' := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hmem : (s, (0 : ℝ)) ∈ U' := by
      simpa only [U', Set.mem_preimage, k, zero_smul, add_zero] using hsegment s hs
    exact continuous_swap.continuousAt.preimage_mem_nhds (hU'.mem_nhds hmem)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hbox : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ U' := by
    intro z hz
    apply hρsub (show z.2 ∈ Metric.ball (0 : ℝ) ρ from ?_) z.1 hz.1
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using hz.2
  have hc : ∀ s ∈ Set.Icc 0 (Real.sqrt b), (f ∘ k) (s, 0) = A.squareFamily Z s := by
    intro s hs
    simpa only [Function.comp_apply, k, zero_smul, add_zero] using hcenter s hs
  have hfirst := hasDerivAt_smoothSquareFamily_action hM04 hL hτmax hwindow
    A Z b hb hmax (f ∘ k) U' hU' hf' ρ hρ hbox hc
  exact hactual.unique hfirst

end PoincareConjecture.Proofs.M09
