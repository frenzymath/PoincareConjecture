import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Ring.Units









open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace Poincare.Geometry.Manifold.RegularLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




private def straighteningMap (f : E → ℝ) (u₀ : E) (ℓ : E →L[ℝ] ℝ) (e : E) :
    E → E :=
  fun u => u + (f u - f u₀ - ℓ (u - u₀)) • e

private theorem straighteningMap_apply_self (f : E → ℝ) (u₀ : E)
    (ℓ : E →L[ℝ] ℝ) (e : E) : straighteningMap f u₀ ℓ e u₀ = u₀ := by
  simp [straighteningMap]



private theorem hasFDerivAt_straighteningCoef {f : E → ℝ} {u₀ : E}
    {ℓ : E →L[ℝ] ℝ} (hf' : HasFDerivAt f ℓ u₀) :
    HasFDerivAt (fun u => f u - f u₀ - ℓ (u - u₀)) (0 : E →L[ℝ] ℝ) u₀ := by
  have h1 : HasFDerivAt (fun u : E => ℓ (u - u₀)) ℓ u₀ := by
    simpa [map_sub] using ℓ.hasFDerivAt.sub_const (ℓ u₀)
  have h := (hf'.sub_const (f u₀)).sub h1
  have hfun : ((fun u => f u - f u₀) - fun u => ℓ (u - u₀)) =
      fun u => f u - f u₀ - ℓ (u - u₀) := by
    ext u
    rfl
  rw [hfun] at h
  exact h.congr_fderiv (sub_self ℓ)



private theorem hasFDerivAt_straighteningMap {f : E → ℝ} {u₀ : E}
    {ℓ : E →L[ℝ] ℝ} (hf' : HasFDerivAt f ℓ u₀) (e : E) :
    HasFDerivAt (straighteningMap f u₀ ℓ e)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) u₀ := by
  have h := (hasFDerivAt_id u₀).add
    ((hasFDerivAt_straighteningCoef hf').smul_const e)
  have h0 : ContinuousLinearMap.id ℝ E + (0 : E →L[ℝ] ℝ).smulRight e
      = ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) := by
    ext v; simp
  rw [← h0]
  exact h

private theorem contDiffOn_straighteningMap {f : E → ℝ} {s : Set E}
    (hf : ContDiffOn ℝ ∞ f s) (u₀ : E) (ℓ : E →L[ℝ] ℝ) (e : E) :
    ContDiffOn ℝ ∞ (straighteningMap f u₀ ℓ e) s := by
  unfold straighteningMap
  exact contDiffOn_id.add (((hf.sub contDiffOn_const).sub
    ((ℓ.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)).smul
      contDiffOn_const)
















theorem exists_openPartialHomeomorph_comp_symm_eq_affine [CompleteSpace E]
    {f : E → ℝ} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {u₀ : E} (hu₀ : u₀ ∈ s) {ℓ : E →L[ℝ] ℝ} (hf' : HasFDerivAt f ℓ u₀)
    (hl : ℓ ≠ 0) :
    ∃ G : OpenPartialHomeomorph E E, G.source ⊆ s ∧ u₀ ∈ G.source ∧
      G u₀ = u₀ ∧ ContDiffOn ℝ ∞ G G.source ∧
      ContDiffOn ℝ ∞ G.symm G.target ∧
      ∀ v ∈ G.target, f (G.symm v) = f u₀ + ℓ (v - u₀) := by
  classical

  obtain ⟨w, hw⟩ : ∃ w, ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hl (ContinuousLinearMap.ext fun v => by simpa using h v)
  set e : E := (ℓ w)⁻¹ • w with he_def
  have he : ℓ e = 1 := by
    rw [he_def, map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

  have hg_smooth : ContDiffOn ℝ ∞ (straighteningMap f u₀ ℓ e) s :=
    contDiffOn_straighteningMap hf u₀ ℓ e
  have hgAt : ContDiffAt ℝ ∞ (straighteningMap f u₀ ℓ e) u₀ :=
    hg_smooth.contDiffAt (hs.mem_nhds hu₀)
  have hg' := hasFDerivAt_straighteningMap hf' e
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp

  set G₀ : OpenPartialHomeomorph E E :=
    hgAt.toOpenPartialHomeomorph (straighteningMap f u₀ ℓ e) hg' hn with hG₀_def
  have hG₀_coe : (G₀ : E → E) = straighteningMap f u₀ ℓ e := rfl
  have hu₀_G₀ : u₀ ∈ G₀.source :=
    hgAt.mem_toOpenPartialHomeomorph_source hg' hn

  set t : Set E := (s ∩ G₀.source) ∩
    (fderiv ℝ (straighteningMap f u₀ ℓ e)) ⁻¹' {L : E →L[ℝ] E | IsUnit L}
    with ht_def
  have ht_open : IsOpen t := by
    apply ContinuousOn.isOpen_inter_preimage
    · exact (hg_smooth.continuousOn_fderiv_of_isOpen hs
        (by exact_mod_cast le_top)).mono inter_subset_left
    · exact hs.inter G₀.open_source
    · exact Units.isOpen
  have ht_sub_s : t ⊆ s := fun u hu => hu.1.1
  have ht_sub_G₀ : t ⊆ G₀.source := fun u hu => hu.1.2
  have hu₀_t : u₀ ∈ t := by
    refine ⟨⟨hu₀, hu₀_G₀⟩, ?_⟩
    show IsUnit (fderiv ℝ (straighteningMap f u₀ ℓ e) u₀)
    rw [hg'.fderiv, show ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) :
      E →L[ℝ] E) = 1 from ContinuousLinearMap.ext fun x => by
        simp [ContinuousLinearMap.one_def]]
    exact isUnit_one

  refine ⟨G₀.restrOpen t ht_open, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun u hu => ht_sub_s hu.2
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hu₀_G₀, hu₀_t⟩
  · exact straighteningMap_apply_self f u₀ ℓ e
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact hg_smooth.mono fun u hu => ht_sub_s hu.2
  ·
    intro v hv
    set G := G₀.restrOpen t ht_open
    have hu_src : G.symm v ∈ G.source := G.map_target hv
    have hu_t : G.symm v ∈ t := by
      have := hu_src
      rw [OpenPartialHomeomorph.restrOpen_source] at this
      exact this.2
    have hu_s : G.symm v ∈ s := ht_sub_s hu_t
    have hu_unit : IsUnit (fderiv ℝ (straighteningMap f u₀ ℓ e) (G.symm v)) :=
      hu_t.2
    have hDg : HasFDerivAt (straighteningMap f u₀ ℓ e)
        (fderiv ℝ (straighteningMap f u₀ ℓ e) (G.symm v)) (G.symm v) :=
      ((hg_smooth.contDiffAt (hs.mem_nhds hu_s)).differentiableAt
        hn).hasFDerivAt
    have hDgEquiv : HasFDerivAt (straighteningMap f u₀ ℓ e)
        ((ContinuousLinearEquiv.ofUnit hu_unit.unit : E ≃L[ℝ] E) :
          E →L[ℝ] E) (G.symm v) := by
      rwa [show ((ContinuousLinearEquiv.ofUnit hu_unit.unit : E ≃L[ℝ] E) :
          E →L[ℝ] E) = fderiv ℝ (straighteningMap f u₀ ℓ e) (G.symm v) from
        ContinuousLinearMap.ext fun x => by
          simp [ContinuousLinearEquiv.ofUnit, IsUnit.unit_spec]]
    exact (G.contDiffAt_symm hv hDgEquiv
      (hg_smooth.contDiffAt (hs.mem_nhds hu_s))).contDiffWithinAt
  ·
    intro v hv
    set G := G₀.restrOpen t ht_open
    have hgv : straighteningMap f u₀ ℓ e (G.symm v) = v := G.right_inv hv
    have h := congrArg ℓ hgv
    simp only [straighteningMap, map_add, map_smul, smul_eq_mul, map_sub,
      he, mul_one] at h
    rw [map_sub]
    linarith

end Poincare.Geometry.Manifold.RegularLevel

end
