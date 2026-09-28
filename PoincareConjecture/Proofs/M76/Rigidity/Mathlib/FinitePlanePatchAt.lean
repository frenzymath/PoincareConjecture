import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FinitePlanePatchChart

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)

theorem exists_pair_chart_of_finitePL_plane_patch_at {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    {Q : Set V2} {S V : Set E} {f : V2 → E} {z : V2}
    (hf : FinitePiecewiseAffineOn f Q) (hinj : InjOn f Q)
    (hzQ : z ∈ interior Q) (hV : IsOpen V) (hfzV : f z ∈ V)
    (hfull : S ∩ V = (f '' Q) ∩ V) :
    ∃ H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ),
      f z ∈ H.source ∧ H.source ⊆ V ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧ H (f z) = 0 ∧
      ∀ x ∈ H.source, x ∈ S ↔ (H x).2 = 0 := by
  let a : V2 ≃ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousAffineEquiv.constVAdd ℝ V2 (-z)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousAffineEquiv
  have haz : a z = 0 := by
    change (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) (-z + z) = 0
    rw [neg_add_cancel, map_zero]
  have hai0 : a.symm 0 = z := by rw [← haz, a.symm_apply_apply]
  let τ : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-f z)
  have hτz : τ (f z) = 0 := by change -f z + f z = 0; exact neg_add_cancel _
  let Q' := a '' Q
  let g : (ℝ × ℝ) → E := τ ∘ (f ∘ a.symm)
  have hg : FinitePiecewiseAffineOn g Q' :=
    (hf.precomp_affineEquiv a.symm).postcomp τ.toContinuousAffineMap
  have hginj : InjOn g Q' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have hxy' : τ (f x) = τ (f y) := by
      simpa only [g, Function.comp_apply, a.symm_apply_apply] using hxy
    exact congrArg a (hinj hx hy (τ.injective hxy'))
  have hg0 : g 0 = 0 := by
    change τ (f (a.symm 0)) = 0
    rw [hai0, hτz]
  have h0Q : (0 : ℝ × ℝ) ∈ interior Q' := by
    change (0 : ℝ × ℝ) ∈ interior (a.toHomeomorph '' Q)
    rw [← a.toHomeomorph.image_interior]
    exact ⟨z, hzQ, haz⟩
  have hgimage : g '' Q' = τ '' (f '' Q) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨f y, mem_image_of_mem f hy, ?_⟩
      change τ (f y) = τ (f (a.symm (a y)))
      rw [a.symm_apply_apply]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨a y, mem_image_of_mem a hy, ?_⟩
      change τ (f (a.symm (a y))) = τ (f y)
      rw [a.symm_apply_apply]
  have hfull' : (τ '' S) ∩ (τ '' V) = (g '' Q') ∩ (τ '' V) := by
    rw [hgimage, ← Set.image_inter τ.injective, ← Set.image_inter τ.injective, hfull]
  obtain ⟨C, h0C, hCV, hCt, hC, hCi, hC0, hCS⟩ :=
    exists_pair_chart_of_finitePL_plane_patch hdim hg hginj hg0 h0Q
      (τ.toHomeomorph.isOpenMap V hV) ⟨f z, hfzV, hτz⟩ hfull'
  let H := τ.toHomeomorph.toOpenPartialHomeomorph.trans C
  have hHt : H.target = C.target := by
    change C.target ∩ C.symm ⁻¹' (univ : Set E) = C.target
    rw [preimage_univ, inter_univ]
  have hH : LocallyPiecewiseAffineOn H H.source :=
    hC.comp (locallyPiecewiseAffineOn_affine τ.toContinuousAffineMap isOpen_univ)
  have hHi : LocallyPiecewiseAffineOn H.symm H.target :=
    (locallyPiecewiseAffineOn_affine τ.symm.toContinuousAffineMap isOpen_univ).comp hCi
  have hpH : f z ∈ H.source := by
    change f z ∈ (univ : Set E) ∧ τ (f z) ∈ C.source
    exact ⟨mem_univ _, by rw [hτz]; exact h0C⟩
  refine ⟨H, hpH, ?_, hHt.trans hCt, hH, hHi, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hCV hx.2
    exact τ.injective hyx ▸ hy
  · change C (τ (f z)) = 0
    rw [hτz, hC0]
  · intro x hx
    have hmem : τ x ∈ τ '' S ↔ x ∈ S :=
      ⟨fun ⟨y, hy, hyx⟩ => τ.injective hyx ▸ hy, fun hy => mem_image_of_mem τ hy⟩
    exact hmem.symm.trans (hCS (τ x) hx.2)

end PoincareConjecture.M76.HamiltonIndexOne
