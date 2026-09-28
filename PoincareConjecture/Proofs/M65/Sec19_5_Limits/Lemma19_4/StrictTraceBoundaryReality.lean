import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceFramedFields
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceFrame
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceTangentExtension











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace

open M65Branch



theorem halfDisk_hasDerivAt_diameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℂ → E} {r t : ℝ}
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (ht : ‖(t : ℂ)‖ < r) :
    HasDerivAt (fun s : ℝ => H (s : ℂ))
      (fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (t : ℂ) 1) t := by
  have hmem : (t : ℂ) ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im} :=
    ⟨mem_closedBall_zero_iff.mpr ht.le, by simp⟩
  have hdiff := (hH.differentiableOn one_ne_zero (t : ℂ) hmem).hasFDerivWithinAt
  have hevent : ∀ᶠ s : ℝ in 𝓝 t,
      (s : ℂ) ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im} := by
    filter_upwards [(continuous_ofReal.norm.continuousAt).eventually (gt_mem_nhds ht)]
      with s hs
    exact ⟨mem_closedBall_zero_iff.mpr hs.le, by simp⟩
  simpa only [Function.comp_def, ofRealCLM_apply, ofReal_one] using
    hdiff.comp_hasDerivAt t ofRealCLM.hasDerivAt hevent





theorem halfDisk_rowFrame_reality
    {g : RiemannianMetric 3 LoopAmbient} {H : ℂ → LoopAmbient} {r t : ℝ}
    {c : ℝ → LoopAmbient} {I J : Set ℝ} {U : Set LoopAmbient}
    {sigma : LoopAmbient → ℝ} {V : LoopAmbient → LoopAmbient} (j : Fin 3)
    (hI : IsOpen I) (hU : IsOpen U) (hc : ContDiffOn ℝ ∞ c I)
    (hsigma : ContDiffOn ℝ ∞ sigma U)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHU : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) U)
    (hparam : ∀ q ∈ U, sigma q ∈ I)
    (hinv : ∀ s ∈ J, sigma (c s) = s)
    (hV : ∀ q ∈ U, V q = deriv c (sigma q))
    (hj : ∀ q ∈ U, V q j ≠ 0)
    (harc : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → H (s : ℂ) ∈ c '' J)
    (ht : ‖(t : ℂ)‖ < r)
    (hdiag :
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (t : ℂ)
      g.inner (H (t : ℂ)) (T 1) (T 1) =
        g.inner (H (t : ℂ)) (T Complex.I) (T Complex.I))
    (hmixed :
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (t : ℂ)
      g.inner (H (t : ℂ)) (T 1) (T Complex.I) = 0) :
    boundaryReflection j
        (halfDiskFramedGradient H (fun q => complexifyOperator (rowFrame (g.inner q) (V q) j))
          r (t : ℂ)) =
      halfDiskFramedGradient H (fun q => complexifyOperator (rowFrame (g.inner q) (V q) j))
        r (t : ℂ) := by
  have hmem : (t : ℂ) ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im} :=
    ⟨mem_closedBall_zero_iff.mpr ht.le, by simp⟩
  have hHU' := hHU hmem
  have hd := halfDisk_hasDerivAt_diameter hH ht
  have ha : ∀ᶠ s : ℝ in 𝓝 t, H (s : ℂ) ∈ c '' J := by
    filter_upwards [(continuous_ofReal.norm.continuousAt).eventually (gt_mem_nhds ht)]
      with s hs
    exact harc s hs.le
  obtain ⟨a, ha⟩ := boundary_tangent_from_inverse hI hU hc hsigma hd.differentiableAt
    hHU' (hparam _ hHU') hinv (hV _ hHU') ha
  have hcol : ∃ a : ℝ,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (t : ℂ) 1 =
        a • V (H (t : ℂ)) := ⟨a, hd.deriv.symm.trans ha⟩
  exact rowFrame_boundary_reflection (g.inner (H (t : ℂ))) (V (H (t : ℂ)))
    _ _ j (hj _ hHU') (g.pos (H (t : ℂ))) hcol hdiag hmixed

end PoincareConjecture.M65StrictTrace
