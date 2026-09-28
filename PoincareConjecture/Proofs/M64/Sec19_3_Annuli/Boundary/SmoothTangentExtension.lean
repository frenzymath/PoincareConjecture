import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.MetricRowFrame











noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)






theorem exists_smooth_tangent_extension {c : ℝ → E} {I : Set ℝ} {s : ℝ}
    (hI : IsOpen I) (hs : s ∈ I) (hc : ContDiffOn ℝ ∞ c I)
    (hder : deriv c s ≠ 0) :
    ∃ (j : Fin n) (U : Set E) (J : Set ℝ) (sigma : E → ℝ) (V : E → E),
      IsOpen U ∧ IsOpen J ∧ c s ∈ U ∧ s ∈ J ∧ J ⊆ I ∧ MapsTo c J U ∧
      ContDiffOn ℝ ∞ sigma U ∧ ContDiffOn ℝ ∞ V U ∧
      (∀ t ∈ J, sigma (c t) = t) ∧
      (∀ q ∈ U, sigma q ∈ J ∧ V q = deriv c (sigma q) ∧ V q j ≠ 0) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin n, deriv c s j ≠ 0 := by
    by_contra h
    push Not at h
    apply hder
    ext j
    exact h j
  let pr : E →L[ℝ] ℝ := EuclideanSpace.proj j
  let h : ℝ → ℝ := fun t => c t j
  have hhc : ContDiffOn ℝ ∞ h I := pr.contDiff.comp_contDiffOn hc
  have hcd (t : ℝ) (ht : t ∈ I) : DifferentiableAt ℝ c t :=
    ((hc t ht).contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have hd (t : ℝ) (ht : t ∈ I) : deriv h t = deriv c t j :=
    (pr.hasFDerivAt.comp_hasDerivAt t (hcd t ht).hasDerivAt).deriv
  obtain ⟨e, he, hse, hsub, hne, hinv⟩ :=
    M65StrictTrace.exists_regular_coordinate_inverse hI hs hhc (by rwa [hd s hs])
  let U : Set E := pr ⁻¹' e.target
  let sigma : E → ℝ := fun q => e.symm (pr q)
  let V : E → E := fun q => deriv c (sigma q)
  have hU : IsOpen U := e.open_target.preimage pr.continuous
  have hsig : ContDiffOn ℝ ∞ sigma U :=
    hinv.comp pr.contDiff.contDiffOn (fun _ hq => hq)
  have hsigmem (q : E) (hq : q ∈ U) : sigma q ∈ e.source := e.map_target hq
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

end PoincareConjecture.M64
