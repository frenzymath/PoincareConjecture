import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceFrame
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace

theorem exists_regular_coordinate_inverse {h : ℝ → ℝ} {I : Set ℝ} {s : ℝ}
    (hI : IsOpen I) (hs : s ∈ I) (hh : ContDiffOn ℝ ∞ h I)
    (hder : deriv h s ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ, (e : ℝ → ℝ) = h ∧ s ∈ e.source ∧
      e.source ⊆ I ∧ (∀ t ∈ e.source, deriv h t ≠ 0) ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hhs : ContDiffAt ℝ ∞ h s := (hh s hs).contDiffAt (hI.mem_nhds hs)
  have hds := (hhs.differentiableAt (by simp)).hasDerivAt.hasFDerivAt_equiv hder
  let e₀ := hhs.toOpenPartialHomeomorph h hds (by simp)
  have hs₀ : s ∈ e₀.source := hhs.mem_toOpenPartialHomeomorph_source hds (by simp)
  let J := I ∩ (deriv h) ⁻¹' ({0}ᶜ)
  have hdh : ContDiffOn ℝ ∞ (deriv h) I := hh.deriv_of_isOpen hI (by simp)
  have hJ : IsOpen J := hdh.continuousOn.isOpen_inter_preimage
    hI isClosed_singleton.isOpen_compl
  let e := e₀.restrOpen J hJ
  have he : (e : ℝ → ℝ) = h := rfl
  have hsource : e.source = e₀.source ∩ J := rfl
  have hsub : e.source ⊆ I := fun _ ht => ht.2.1
  have hne (t : ℝ) (ht : t ∈ e.source) : deriv h t ≠ 0 := ht.2.2
  refine ⟨e, he, ⟨hs₀, hs, hder⟩, hsub, hne, ?_⟩
  intro y hy
  have ht := e.map_target hy
  have hd : ContDiffAt ℝ ∞ h (e.symm y) :=
    (hh _ (hsub ht)).contDiffAt (hI.mem_nhds (hsub ht))
  apply (e.contDiffAt_symm_deriv (hne _ ht) hy ?_ ?_).contDiffWithinAt
  · simpa only [he] using (hd.differentiableAt (by simp)).hasDerivAt
  · simpa only [he] using hd

theorem exists_smooth_tangent_extension {c : ℝ → LoopAmbient} {I : Set ℝ} {s : ℝ}
    (hI : IsOpen I) (hs : s ∈ I) (hc : ContDiffOn ℝ ∞ c I)
    (hder : deriv c s ≠ 0) :
    ∃ (j : Fin 3) (U : Set LoopAmbient) (J : Set ℝ)
      (sigma : LoopAmbient → ℝ) (V : LoopAmbient → LoopAmbient),
      IsOpen U ∧ IsOpen J ∧ c s ∈ U ∧ s ∈ J ∧ J ⊆ I ∧ MapsTo c J U ∧
      ContDiffOn ℝ ∞ sigma U ∧ ContDiffOn ℝ ∞ V U ∧
      (∀ t ∈ J, sigma (c t) = t) ∧
      (∀ q ∈ U, sigma q ∈ J ∧ V q = deriv c (sigma q) ∧ V q j ≠ 0) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, deriv c s j ≠ 0 := by
    by_contra h
    push Not at h
    apply hder
    ext j
    exact h j
  let pr : LoopAmbient →L[ℝ] ℝ := EuclideanSpace.proj j
  let h : ℝ → ℝ := fun t => c t j
  have hhc : ContDiffOn ℝ ∞ h I := pr.contDiff.comp_contDiffOn hc
  have hcd (t : ℝ) (ht : t ∈ I) : DifferentiableAt ℝ c t :=
    ((hc t ht).contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have hd (t : ℝ) (ht : t ∈ I) : deriv h t = deriv c t j :=
    (pr.hasFDerivAt.comp_hasDerivAt t (hcd t ht).hasDerivAt).deriv
  obtain ⟨e, he, hse, hsub, hne, hinv⟩ :=
    exists_regular_coordinate_inverse hI hs hhc (by rwa [hd s hs])
  let U : Set LoopAmbient := pr ⁻¹' e.target
  let sigma : LoopAmbient → ℝ := fun q => e.symm (pr q)
  let V : LoopAmbient → LoopAmbient := fun q => deriv c (sigma q)
  have hU : IsOpen U := e.open_target.preimage pr.continuous
  have hsig : ContDiffOn ℝ ∞ sigma U :=
    hinv.comp pr.contDiff.contDiffOn (fun _ hq => hq)
  have hsigmem (q : LoopAmbient) (hq : q ∈ U) : sigma q ∈ e.source := e.map_target hq
  have hmap : MapsTo c e.source U := by
    intro t ht
    change pr (c t) ∈ e.target
    simpa only [he, h, pr, EuclideanSpace.proj, PiLp.proj_apply] using e.map_source ht
  refine ⟨j, U, e.source, sigma, V, hU, e.open_source, hmap hse, hse, hsub, hmap,
    hsig, ?_, ?_, ?_⟩
  · exact (hc.deriv_of_isOpen hI (by simp)).comp hsig
      (fun q hq => hsub (hsigmem q hq))
  · intro t ht
    change e.symm (h t) = t
    rw [← he]
    exact e.left_inv ht
  · intro q hq
    refine ⟨hsigmem q hq, rfl, ?_⟩
    have hn := hne _ (hsigmem q hq)
    rwa [hd _ (hsub (hsigmem q hq))] at hn

theorem boundary_tangent_from_inverse
    {c b : ℝ → LoopAmbient} {I J : Set ℝ} {U : Set LoopAmbient}
    {sigma : LoopAmbient → ℝ} {V : LoopAmbient → LoopAmbient} {a : ℝ}
    (hI : IsOpen I) (hU : IsOpen U) (hc : ContDiffOn ℝ ∞ c I)
    (hsigma : ContDiffOn ℝ ∞ sigma U) (hb : DifferentiableAt ℝ b a)
    (hba : b a ∈ U) (hparam : sigma (b a) ∈ I)
    (hinv : ∀ t ∈ J, sigma (c t) = t)
    (hV : V (b a) = deriv c (sigma (b a)))
    (harc : ∀ᶠ t in 𝓝 a, b t ∈ c '' J) :
    ∃ r : ℝ, deriv b a = r • V (b a) := by
  have hsig : DifferentiableAt ℝ sigma (b a) :=
    ((hsigma _ hba).contDiffAt (hU.mem_nhds hba)).differentiableAt (by simp)
  have hp := hsig.comp a hb
  have hcurve : DifferentiableAt ℝ c (sigma (b a)) :=
    ((hc _ hparam).contDiffAt (hI.mem_nhds hparam)).differentiableAt (by simp)
  have heq : (fun t => c (sigma (b t))) =ᶠ[𝓝 a] b := by
    filter_upwards [harc] with t ht
    obtain ⟨u, hu, he⟩ := ht
    rw [← he, hinv u hu]
  have hderiv := (hcurve.hasDerivAt.scomp a hp.hasDerivAt).congr_of_eventuallyEq heq.symm
  refine ⟨deriv (fun t => sigma (b t)) a, ?_⟩
  rw [hV]
  exact hderiv.deriv

end PoincareConjecture.M65StrictTrace
