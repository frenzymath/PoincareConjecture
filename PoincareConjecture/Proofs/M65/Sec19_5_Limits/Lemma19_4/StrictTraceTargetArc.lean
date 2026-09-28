import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceArcCapture
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceTangentExtension
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65StrictTrace

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem exists_chart_Jordan_tangent
    {gamma : LoopCircle → M} (hgamma : Continuous gamma)
    (hinj : Function.Injective gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    (p : M) {s : ℝ} (hsource : gamma (m65LoopAngular s) ∈ (chartAt LoopAmbient p).source) :
    let q := chartAt LoopAmbient p
    let c := q ∘ gamma ∘ m65LoopAngular
    let I := (gamma ∘ m65LoopAngular) ⁻¹' q.source
    ∃ (j : Fin 3) (U : Set LoopAmbient) (J : Set ℝ)
      (sigma : LoopAmbient → ℝ) (V : LoopAmbient → LoopAmbient),
      IsOpen I ∧ ContDiffOn ℝ ∞ c I ∧ IsOpen U ∧ c s ∈ U ∧
      ContDiffOn ℝ ∞ sigma U ∧ ContDiffOn ℝ ∞ V U ∧
      (∀ t ∈ J, sigma (c t) = t) ∧
      (∀ y ∈ U, sigma y ∈ I ∧ V y = deriv c (sigma y) ∧ V y j ≠ 0) ∧
      (∀ y ∈ U, y ∈ q.target) ∧
      ∀ y ∈ U, q.symm y ∈ range gamma → y ∈ c '' J := by
  let q := chartAt LoopAmbient p
  let C := gamma ∘ m65LoopAngular
  let c := q ∘ C
  let I := C ⁻¹' q.source
  have hI : IsOpen I := q.open_source.preimage hsmooth.continuous
  have hs : s ∈ I := hsource
  have hc : ContDiffOn ℝ ∞ c I :=
    (contMDiffOn_chart.comp hsmooth.contMDiffOn (fun _ ht => ht)).contDiffOn
  have hqd := (mdifferentiable_chart (I := 𝓡 3) p).mdifferentiableAt hsource
  have hCd := (hsmooth s).mdifferentiableAt (by simp)
  have hchain := congrArg (fun T : ℝ →L[ℝ] LoopAmbient => T 1)
    (mfderiv_comp s hqd hCd)
  have hder : deriv c s = mfderiv (𝓡 3) (𝓡 3) q (C s) (curveVelocity C s) := by
    simpa +instances only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      fderiv_apply_one_eq_deriv, curveVelocity, c, C, q] using! hchain
  have hne : deriv c s ≠ 0 := by
    intro hz
    apply hregular s
    apply ((mdifferentiable_chart (I := 𝓡 3) p).mfderiv hsource).injective
    change mfderiv (𝓡 3) (𝓡 3) q (C s) (curveVelocity C s) =
      mfderiv (𝓡 3) (𝓡 3) q (C s) 0
    rw [← hder, hz, map_zero]
  obtain ⟨j, U0, J, sigma, V, hU0, hJ, hcs, hsJ, hJI, _, hsig, hV, hinv, hdata⟩ :=
    exists_smooth_tangent_extension hI hs hc hne
  obtain ⟨A, hA, hsA, hAcap⟩ := embedded_loop_arc_capture hgamma hinj hJ hsJ
  let U := U0 ∩ (q.target ∩ q.symm ⁻¹' A)
  have hU : IsOpen U := hU0.inter
    (q.symm.continuousOn.isOpen_inter_preimage q.open_target hA)
  have hcsU : c s ∈ U := by
    refine ⟨hcs, q.map_source hsource, ?_⟩
    change q.symm (q (C s)) ∈ A
    rw [q.left_inv (show C s ∈ q.source from hsource)]
    exact hsA
  refine ⟨j, U, J, sigma, V, hI, hc, hU, hcsU,
    hsig.mono inter_subset_left, hV.mono inter_subset_left, hinv, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hsigy, hVy, hjy⟩ := hdata y hy.1
    exact ⟨hJI hsigy, hVy, hjy⟩
  · intro y hy
    exact hy.2.1
  · intro y hy hyr
    obtain ⟨t, ht, he⟩ := hAcap (q.symm y) hy.2.2 hyr
    refine ⟨t, ht, ?_⟩
    change q (gamma (m65LoopAngular t)) = y
    rw [he, q.right_inv hy.2.1]

end PoincareConjecture.M65StrictTrace
