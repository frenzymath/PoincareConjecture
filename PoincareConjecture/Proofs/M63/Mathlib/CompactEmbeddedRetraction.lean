import PoincareConjecture.Proofs.M63.Mathlib.LocalCriticalProjection
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M63

variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [Nonempty M]






theorem exists_smooth_compact_embedded_retraction [T2Space M] (e : M → F)
    (he : Topology.IsClosedEmbedding e)
    (hs : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ e)
    (hi : ∀ p, Function.Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) e p)) :
    ∃ U : Set F, ∃ ρ : F → M,
      IsOpen U ∧ range e ⊆ U ∧ ContMDiffOn (𝓘(ℝ, F)) (𝓘(ℝ, E)) ∞ ρ U ∧
      (∀ p, ρ (e p) = p) ∧
      (∀ z p, ‖z - e (ρ z)‖ ≤ ‖z - e p‖) ∧
      ∀ z ∈ U, ∀ q, (∀ p, ‖z - e q‖ ≤ ‖z - e p‖) → q = ρ z := by
  classical
  have hmin : ∀ z : F, ∃ q : M, ∀ p : M, ‖z - e q‖ ≤ ‖z - e p‖ := by
    intro z
    obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set M).Nonempty)
      ((continuous_const.sub he.continuous).norm.continuousOn (s := univ))
    exact ⟨q, fun p => hq (mem_univ p)⟩
  choose ρ hρ using hmin
  have hρe (p : M) : ρ (e p) = p := by
    apply he.injective
    have hzero : ‖e p - e (ρ (e p))‖ = 0 :=
      le_antisymm (by simpa only [sub_self, norm_zero] using hρ (e p) p) (norm_nonneg _)
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  have hlocal : ∀ p : M, ∃ W : Set F, IsOpen W ∧ e p ∈ W ∧
      ContMDiffOn (𝓘(ℝ, F)) (𝓘(ℝ, E)) ∞ ρ W ∧
      ∀ z ∈ W, ∀ q, (∀ r, ‖z - e q‖ ≤ ‖z - e r‖) → q = ρ z := by
    intro p
    let c := chartAt E p
    let f : E → F := e ∘ c.symm
    have hp : p ∈ c.source := mem_chart_source E p
    have hcp : c p ∈ c.target := c.map_source hp
    have hf : ContDiffOn ℝ ∞ f c.target :=
      (hs.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := p))).contDiffOn
    have hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) := mdifferentiable_chart p
    have hderiv (u : E) (hu : u ∈ c.target) :
        fderiv ℝ f u = (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) e (c.symm u)).comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) c.symm u) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp u (hs.mdifferentiable (by simp)).mdifferentiableAt
        (hc.symm.mdifferentiableAt hu)
    have hfi : Function.Injective (fderiv ℝ f (c p)) := by
      rw [hderiv _ hcp]
      exact (hi _).comp (hc.symm.mfderiv_injective hcp)
    obtain ⟨W, V, g, hW, hfcW, hV, hcpV, hVs, _, hgV, hgs, _, huniq⟩ :=
      exists_local_criticalProjection c.open_target hcp hf hfi
    have hfc : f (c p) = e p := congrArg e (c.left_inv hp)
    have hepW : e p ∈ W := hfc ▸ hfcW
    let O := c.source ∩ c ⁻¹' V
    have hO : IsOpen O := c.isOpen_inter_preimage hV
    have hpO : p ∈ O := ⟨hp, hcpV⟩
    obtain ⟨B, hB, hBO⟩ := he.isEmbedding.isInducing.isOpen_iff.mp hO
    have hepB : e p ∈ B := by
      change p ∈ e ⁻¹' B
      rw [hBO]
      exact hpO
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hepB)
    let Wp := W ∩ Metric.ball (e p) (η / 3)
    have hWp : IsOpen Wp := hW.inter Metric.isOpen_ball
    have hepWp : e p ∈ Wp := ⟨hepW, Metric.mem_ball_self (by positivity)⟩
    have hformula (z : F) (hz : z ∈ Wp) (q : M)
        (hq : ∀ r, ‖z - e q‖ ≤ ‖z - e r‖) : q = c.symm (g z) := by
      have heqB : e q ∈ B := by
        apply hball
        apply Metric.mem_ball.mpr
        have hzsmall : ‖z - e p‖ < η / 3 := by
          simpa only [dist_eq_norm] using Metric.mem_ball.mp hz.2
        calc
          dist (e q) (e p) ≤ dist (e q) z + dist z (e p) := dist_triangle _ _ _
          _ = ‖z - e q‖ + ‖z - e p‖ := by rw [dist_comm (e q) z, dist_eq_norm, dist_eq_norm]
          _ ≤ 2 * ‖z - e p‖ := by linarith [hq p]
          _ < η := by linarith
      have hqO : q ∈ O := by
        rw [← hBO]
        exact heqB
      have hqV : c q ∈ V := hqO.2
      have hqtarget : c q ∈ c.target := hVs hqV
      have hfq : f (c q) = e q := congrArg e (c.left_inv hqO.1)
      have hsqmin : IsLocalMin (fun u : E => ‖z - f u‖ ^ 2) (c q) := by
        apply Filter.Eventually.of_forall
        intro u
        change ‖z - f (c q)‖ ^ 2 ≤ ‖z - f u‖ ^ 2
        rw [hfq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hq (c.symm u)) 2
      have hfd : HasFDerivAt f (fderiv ℝ f (c q)) (c q) :=
        ((hf.contDiffAt (c.open_target.mem_nhds hqtarget)).differentiableAt
          (by simp)).hasFDerivAt
      have hzero := hsqmin.hasFDerivAt_eq_zero (hfd.const_sub z).norm_sq
      have hcritical : (fderiv ℝ f (c q)).adjoint (z - f (c q)) = 0 := by
        rw [← inner_self_eq_zero (𝕜 := ℝ)]
        rw [ContinuousLinearMap.adjoint_inner_left]
        have hv := DFunLike.congr_fun hzero
          ((fderiv ℝ f (c q)).adjoint (z - f (c q)))
        simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply, neg_apply,
          innerSL_apply_apply, inner_neg_right, zero_apply] at hv
        linarith
      have hcoord := huniq z hz.1 (c q) hqV hcritical
      rw [← hcoord, c.left_inv hqO.1]
    have hρformula (z : F) (hz : z ∈ Wp) : ρ z = c.symm (g z) :=
      hformula z hz (ρ z) (hρ z)
    have hsmooth : ContMDiffOn (𝓘(ℝ, F)) (𝓘(ℝ, E)) ∞ (c.symm ∘ g) Wp :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := p)).comp
        (hgs.mono inter_subset_left).contMDiffOn (fun z hz => hVs (hgV hz.1))
    refine ⟨Wp, hWp, hepWp, hsmooth.congr hρformula, ?_⟩
    intro z hz q hq
    exact (hformula z hz q hq).trans (hρformula z hz).symm
  choose W hW hepW hsW huW using hlocal
  let U := ⋃ p, W p
  have hU : IsOpen U := isOpen_iUnion hW
  refine ⟨U, ρ, hU, ?_, ?_, hρe, hρ, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, hepW p⟩
  · intro z hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    exact ((hsW p).contMDiffAt ((hW p).mem_nhds hp)).contMDiffWithinAt
  · intro z hz q hq
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    exact huW p z hp q hq

end PoincareConjecture.M63
