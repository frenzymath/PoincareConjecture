import PoincareConjecture.Proofs.M25.Topology3D.Space3.MorseCoefficients
import PoincareConjecture.Proofs.M25.Topology3D.Space3.MorseSquareCompletion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_morse_chart_zero (hdim : Module.finrank ℝ E = 2)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hzero : fderiv ℝ f 0 = 0)
    (hinj : Function.Injective (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (σ τ : ℝ) (e : OpenPartialHomeomorph E (ℝ × ℝ)),
      σ * σ = 1 ∧ τ * τ = 1 ∧ 0 ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, f x = f 0 + σ * (e x).1 ^ 2 + τ * (e x).2 ^ 2 := by
  obtain ⟨L, a, b, c, ha, hb, hc, ha0, hb0, hc0, hform⟩ :=
    exists_morse_quadratic_coefficients hdim f hf hzero hinj
  obtain ⟨σ, τ, e0, hσ, hτ, h0, he0, hes, hei, heform⟩ :=
    exists_morse_square_chart a b c ha hb hc ha0 hb0 hc0
  let e := L.symm.toHomeomorph.toOpenPartialHomeomorph.trans e0
  refine ⟨σ, τ, e, hσ, hτ, ⟨mem_univ _, by
    change L.symm 0 ∈ e0.source
    simpa only [map_zero] using h0⟩,
    ?_, ?_, ?_, ?_⟩
  · change e0 (L.symm 0) = 0
    simpa only [map_zero] using he0
  · exact hes.comp L.symm.contDiff.contDiffOn (fun _ hx => hx.2)
  · exact L.contDiff.comp_contDiffOn (hei.mono inter_subset_left)
  · intro x hx
    have h := (hform (L.symm x)).trans (heform (L.symm x) hx.2)
    rw [L.apply_symm_apply] at h
    change f x = f 0 + σ * (e0 (L.symm x)).1 ^ 2 + τ * (e0 (L.symm x)).2 ^ 2
    linarith




theorem exists_morse_chart (hdim : Module.finrank ℝ E = 2)
    (f : E → ℝ) {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (x : E) (hx : x ∈ U) (hzero : fderiv ℝ f x = 0)
    (hinj : Function.Injective (fderiv ℝ (fderiv ℝ f) x)) :
    ∃ (σ τ : ℝ) (e : OpenPartialHomeomorph E (ℝ × ℝ)),
      σ * σ = 1 ∧ τ * τ = 1 ∧ x ∈ e.source ∧ e.source ⊆ U ∧ e x = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ y ∈ e.source, f y = f x + σ * (e y).1 ^ 2 + τ * (e y).2 ^ 2 := by
  obtain ⟨g, hg, _, _, hgf⟩ :=
    exists_compactField_extension (isCompact_singleton (x := x)) hU
      (singleton_subset_iff.mpr hx) f hf
  have heq : g =ᶠ[𝓝 x] f := by
    change ∀ᶠ y in 𝓝 x, g y = f y
    simpa only [nhdsSet_singleton] using hgf
  let F : E → ℝ := fun y => g (y + x)
  have hF : ContDiff ℝ ∞ F := hg.comp (contDiff_id.add contDiff_const)
  have hF0 : fderiv ℝ F 0 = 0 := by
    change fderiv ℝ (fun y => g (y + x)) 0 = 0
    rw [fderiv_comp_add_right, zero_add, heq.fderiv_eq, hzero]
  have hFD : fderiv ℝ F = fun y => fderiv ℝ g (y + x) := by
    funext y
    exact fderiv_comp_add_right x
  have hFi : Function.Injective (fderiv ℝ (fderiv ℝ F) 0) := by
    rw [hFD, fderiv_comp_add_right, zero_add, heq.fderiv.fderiv_eq]
    exact hinj
  obtain ⟨σ, τ, e0, hσ, hτ, h0, he0, hes, hei, hform⟩ :=
    exists_morse_chart_zero hdim F hF hF0 hFi
  obtain ⟨W, hWeq, hW, hxW⟩ := mem_nhds_iff.mp heq
  let T := (Homeomorph.subRight x).toOpenPartialHomeomorph
  let e1 := T.trans e0
  let e := e1.restrOpen (U ∩ W) (hU.inter hW)
  have hx1 : x ∈ e1.source := ⟨mem_univ _, by
    change x - x ∈ e0.source
    simpa only [sub_self] using h0⟩
  have he1s : ContDiffOn ℝ ∞ e1 e1.source :=
    hes.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hy => hy.2)
  have he1i : ContDiffOn ℝ ∞ e1.symm e1.target :=
    (hei.mono inter_subset_left).add contDiffOn_const
  refine ⟨σ, τ, e, hσ, hτ, ⟨hx1, hx, hxW⟩, fun _ hy => hy.2.1,
    ?_, he1s.mono inter_subset_left, he1i.mono inter_subset_left, ?_⟩
  · change e0 (x - x) = 0
    simpa only [sub_self] using he0
  · intro y hy
    have h := hform (y - x) hy.1.2
    change g (y - x + x) = g (0 + x) +
      σ * (e0 (y - x)).1 ^ 2 + τ * (e0 (y - x)).2 ^ 2 at h
    rw [sub_add_cancel, zero_add, hWeq hy.2.2, heq.self_of_nhds] at h
    exact h

end PoincareConjecture.M25.Topology3D
