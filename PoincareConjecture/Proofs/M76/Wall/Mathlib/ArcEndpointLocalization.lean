import PoincareConjecture.Proofs.M76.Wall.InitialArcCoordinates










set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph




theorem exists_endpoint_arc_neighborhood
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : OpenPartialHomeomorph X E) {f : ℝ → X}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hi : InjOn f (Icc (0 : ℝ) 1))
    (hxB : f 0 ∈ B.source) (hzero : B (f 0) = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d : E} (hd : d ≠ 0)
    (hmap : MapsTo f (Icc 0 δ) B.source)
    (hformula : ∀ t ∈ Icc 0 δ, B (f t) = t • d)
    {W : Set X} (hW : IsOpen W) (hxW : f 0 ∈ W) :
    ∃ U : Set X, IsOpen U ∧ f 0 ∈ U ∧ U ⊆ B.source ∩ W ∧
      ∀ x ∈ U, x ∈ f '' Icc (0 : ℝ) 1 ↔ ∃ t : ℝ, 0 ≤ t ∧ B x = t • d := by
  let T : Set X := f '' Icc (δ / 2) 1
  have hTI : Icc (δ / 2) 1 ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hT : IsCompact T := isCompact_Icc.image_of_continuousOn (hf.mono hTI)
  have hxT : f 0 ∉ T := by
    rintro ⟨t, ht, hft⟩
    have ht0 := hi (hTI ht) ⟨le_rfl, zero_le_one⟩ hft
    linarith [ht.1]
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let r : ℝ := (δ / 2) * ‖d‖
  have hr : 0 < r := mul_pos (by linarith) hnorm
  let U : Set X := ((B.source ∩ B ⁻¹' ball 0 r) ∩ W) ∩ Tᶜ
  have hU : IsOpen U :=
    ((B.isOpen_inter_preimage isOpen_ball).inter hW).inter hT.isClosed.isOpen_compl
  have hxU : f 0 ∈ U := by
    refine ⟨⟨⟨hxB, ?_⟩, hxW⟩, hxT⟩
    change B (f 0) ∈ ball 0 r
    rw [hzero]
    exact mem_ball_self hr
  refine ⟨U, hU, hxU, fun _ hx => ⟨hx.1.1.1, hx.1.2⟩, ?_⟩
  intro x hx
  constructor
  · rintro ⟨t, ht, hft⟩
    have hshort : t < δ / 2 := lt_of_not_ge
      (fun h => hx.2 ⟨t, ⟨h, ht.2⟩, hft⟩)
    refine ⟨t, ht.1, ?_⟩
    rw [← hft]
    exact hformula t ⟨ht.1, by linarith⟩
  · rintro ⟨t, ht, hxt⟩
    have hsmall : ‖B x‖ < r := mem_ball_zero_iff.mp hx.1.1.2
    rw [hxt, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hsmall
    change t * ‖d‖ < (δ / 2) * ‖d‖ at hsmall
    have hshort : t < δ / 2 := by nlinarith
    have htδ : t ∈ Icc 0 δ := ⟨ht, by linarith⟩
    refine ⟨t, ⟨ht, by linarith⟩, ?_⟩
    exact B.injOn (hmap htδ) hx.1.1.1 ((hformula t htδ).trans hxt.symm)

end OpenPartialHomeomorph
