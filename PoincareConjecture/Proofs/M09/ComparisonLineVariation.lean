import PoincareConjecture.Proofs.M09.SmoothSquareVariation

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
theorem exists_initialFixedLVariation_of_parameter_line
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (f : E × ℝ → M) (Ω : Set (E × ℝ)) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f Ω)
    (hsegment : ∀ s ∈ Set.Icc 0 (Real.sqrt b), ((0 : E), s) ∈ Ω)
    (hbase : ∀ s, f (0, s) = A.squareFamily Z s)
    (hfixed : ∀ x, f (x, 0) = p) (v : E) :
    ∃ V : InitialFixedLVariation F T 0 b (A.path Z b hb hmax),
      V.toLVariation.baseSquareCurve = A.squareFamily Z ∧
      (∀ s u, V.squareFamily s u = f (u • v, s)) ∧
      ∀ u, variationLLength V.toLVariation u =
        backwardLLength F T 0 b (fun t ↦ f (u • v, Real.sqrt t)) := by
  let k : ℝ × ℝ → E × ℝ := fun z ↦ (z.2 • v, z.1)
  let W := k ⁻¹' Ω
  have hk : ContDiff ℝ ∞ k := (contDiff_snd.smul contDiff_const).prodMk contDiff_fst
  have hW : IsOpen W := hΩ.preimage hk.continuous
  have hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ (f ∘ k) W := by
    convert! hf.comp hk.contMDiff.contMDiffOn (fun _ hz ↦ hz) using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ s ∈ Set.Icc 0 (Real.sqrt b), (s, u) ∈ W := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hmem : (s, (0 : ℝ)) ∈ W := by
      simpa only [W, Set.mem_preimage, k, zero_smul] using hsegment s hs
    exact continuous_swap.continuousAt.preimage_mem_nhds (hW.mem_nhds hmem)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hbox : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ W := by
    intro z hz
    apply hρsub (show z.2 ∈ Metric.ball (0 : ℝ) ρ from ?_) z.1 hz.1
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using hz.2
  have hcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), (f ∘ k) (s, 0) = A.squareFamily Z s := by
    intro s _
    simpa only [Function.comp_apply, k, zero_smul] using hbase s
  have hleft : ∀ u ∈ Set.Ioo (-ρ) ρ, (f ∘ k) (0, u) = (f ∘ k) (0, 0) := by
    intro u _
    simp only [Function.comp_apply, k, hfixed]
  obtain ⟨V, _, hVf, _, hVa⟩ := exists_initialFixedLVariation_of_smoothSquareFamily
    hM04 hτmax hwindow A Z b hb hmax (f ∘ k) W hW hg ρ hρ hbox hcenter hleft
  refine ⟨V, ?_, hVf, hVa⟩
  funext s
  change V.squareFamily s 0 = A.squareFamily Z s
  simpa only [Function.comp_apply, k, zero_smul] using (hVf s 0).trans
    (show (f ∘ k) (s, 0) = A.squareFamily Z s by
      simpa only [Function.comp_apply, k, zero_smul] using hbase s)

end PoincareConjecture.Proofs.M09
