


import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff









set_option autoImplicit false

open Set Metric
open scoped ContDiff Topology

namespace Poincare.Analysis

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_uniform_parametric_coordinates {H : ℝ × E → F}
    (hH : ContDiff ℝ ∞ H) (L : E ≃L[ℝ] F)
    (hdH : HasStrictFDerivAt H
      ((L : E →L[ℝ] F).comp (ContinuousLinearMap.snd ℝ ℝ E)) (0, 0)) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ →
      ∃ C : OpenPartialHomeomorph E F,
        (∀ q, C q = H (ε, q)) ∧ ball (0 : E) δ ⊆ C.source ∧
        ContDiffOn ℝ ∞ C C.source ∧ ContDiffOn ℝ ∞ C.symm C.target := by
  let A (p : ℝ × E) : ℝ × F := (p.1, H p)
  let LA := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L
  have hA : ContDiff ℝ ∞ A := contDiff_fst.prodMk hH
  have hdA : HasStrictFDerivAt A (LA : (ℝ × E) →L[ℝ] (ℝ × F)) (0, 0) := by
    exact (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (0, (0 : E)))).prodMk hdH
  let G₀ := hdA.toOpenPartialHomeomorph A
  let V := (fderiv ℝ A) ⁻¹'
    range (fun B : (ℝ × E) ≃L[ℝ] (ℝ × F) =>
      (B : (ℝ × E) →L[ℝ] (ℝ × F)))
  have hVopen : IsOpen V :=
    ContinuousLinearEquiv.isOpen.preimage (hA.continuous_fderiv (by simp))
  have hzeroV : (0, (0 : E)) ∈ V := ⟨LA, hdA.hasFDerivAt.fderiv.symm⟩
  let G := G₀.restrOpen V hVopen
  have hzeroG : (0, (0 : E)) ∈ G.source :=
    ⟨hdA.mem_toOpenPartialHomeomorph_source, hzeroV⟩
  have hGmap (p : ℝ × E) : G p = (p.1, H p) := rfl
  have hGinv : ContDiffOn ℝ ∞ G.symm G.target := by
    intro p hp
    have hsource := G.map_target hp
    obtain ⟨B, hB⟩ := hsource.2
    change (B : (ℝ × E) →L[ℝ] (ℝ × F)) = fderiv ℝ A (G.symm p) at hB
    apply (G.contDiffAt_symm (f₀' := B) hp ?_ hA.contDiffAt).contDiffWithinAt
    change HasFDerivAt A (B : (ℝ × E) →L[ℝ] (ℝ × F)) (G.symm p)
    rw [hB]
    exact (hA.differentiable (by simp) (G.symm p)).hasFDerivAt
  have hfirst {p : ℝ × F} (hp : p ∈ G.target) : (G.symm p).1 = p.1 := by
    have h := congrArg Prod.fst (G.right_inv hp)
    rwa [hGmap] at h
  have hslice (ε : ℝ) {z : F} (hz : (ε, z) ∈ G.target) :
      (ε, (G.symm (ε, z)).2) = G.symm (ε, z) :=
    Prod.ext (hfirst hz).symm rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (G.open_source.mem_nhds hzeroG)
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  let C : OpenPartialHomeomorph E F := {
    toFun := fun q => H (ε, q)
    invFun := fun z => (G.symm (ε, z)).2
    source := {q | (ε, q) ∈ G.source}
    target := {z | (ε, z) ∈ G.target}
    map_source' := by
      intro q hq
      exact G.map_source hq
    map_target' := by
      intro z hz
      have h := G.map_target hz
      change (ε, (G.symm (ε, z)).2) ∈ G.source
      rw [hslice ε hz]
      exact h
    left_inv' := by
      intro q hq
      exact congrArg Prod.snd (G.left_inv hq)
    right_inv' := by
      intro z hz
      have h := congrArg Prod.snd (G.right_inv hz)
      rw [hGmap] at h
      change H (ε, (G.symm (ε, z)).2) = z
      rw [hslice ε hz]
      exact h
    open_source := G.open_source.preimage (continuous_const.prodMk continuous_id)
    open_target := G.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun := (hH.comp (contDiff_const.prodMk contDiff_id)).continuous.continuousOn
    continuousOn_invFun := continuous_snd.comp_continuousOn
      (G.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hz => hz)) }
  refine ⟨C, fun _ => rfl, ?_,
    (hH.comp (contDiff_const.prodMk contDiff_id)).contDiffOn, ?_⟩
  · intro q hq
    apply hball
    rw [← ball_prod_same]
    exact ⟨by simpa only [mem_ball, Real.dist_eq, sub_zero] using hε, hq⟩
  · exact contDiff_snd.comp_contDiffOn
      (hGinv.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz))

end Poincare.Analysis
