import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmallGermExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmallPerturbation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalPerturbation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialIsotopyTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactField











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_boundary_germ_isotopy_at (v : E) (hv : ‖v‖ = 1)
    (c : (ℝ ∙ v)ᗮ)
    (h : (ℝ ∙ v)ᗮ → (ℝ ∙ v)ᗮ) (hh : ContDiff ℝ ∞ h)
    (hh0 : h 0 = 0) (hd0 : fderiv ℝ h 0 = 0) :
    ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) ∧
      (∀ y, Ψ 0 y = y) ∧ (∀ t y, ‖Ψ t y‖ = ‖y‖) ∧
      (∀ᶠ w in 𝓝 0, Ψ 1 (stereoInvFun hv (c + w) : E) =
        (stereoInvFun hv (c + w + h w) : E)) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ radialStereoTarget v ∧
        ∀ t y, y ∉ C → Ψ t y = y := by
  obtain ⟨χ, hχ, hχc, hχs, hnear, hχrange⟩ := exists_compact_smooth_cutoff
    (K := {(1 : ℝ)}) (U := Ioi 0) isCompact_singleton isOpen_Ioi
    (by intro r hr; simpa only [mem_singleton_iff.mp hr, mem_Ioi] using zero_lt_one)
  have hχone : χ 1 = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnear 1 (mem_singleton 1)).self_of_nhds
  obtain ⟨k, _, hk, _⟩ := compactField_bounds χ hχ hχc
  let L : ℝ≥0 := (2 * (1 + k))⁻¹
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall : L + k * L < 1 := by
    have heq : L + k * L = 1 / 2 := by dsimp [L]; field_simp
    rw [heq]
    norm_num
  obtain ⟨g, hg, hgc, hgs, hglip, hgerm⟩ :=
    exists_small_germ_extension h hh hh0 hd0 hL (b := 1) zero_lt_one
  have hg0 : g 0 = 0 := hgerm.eq_of_nhds.trans hh0
  have hgnorm (w : (ℝ ∙ v)ᗮ) : ‖g w‖ ≤ L := by
    simpa only [mul_one] using
      norm_le_of_lipschitz_supported_ball g hglip hg0 zero_le_one hgs w
  let g' : (ℝ ∙ v)ᗮ → (ℝ ∙ v)ᗮ := fun w => g (w - c)
  have hg' : ContDiff ℝ ∞ g' := hg.comp (contDiff_id.sub contDiff_const)
  have hgc' : HasCompactSupport g' := hgc.comp_homeomorph (Homeomorph.subRight c)
  have hglip' : LipschitzWith L g' := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hglip.norm_sub_le (x - c) (y - c)
  let V := horizontalFieldLift χ g'
  have hV : ContDiff ℝ ∞ V := horizontalFieldLift_contDiff χ hχ g' hg'
  have hVc : HasCompactSupport V := horizontalFieldLift_hasCompactSupport χ hχc g' hgc'
  have hVlip : LipschitzWith (L + k * L) V :=
    horizontalFieldLift_lipschitz χ g' hk
      (fun r => by rw [Real.norm_eq_abs, abs_of_nonneg (hχrange r).1]; exact (hχrange r).2)
      hglip' (fun w => hgnorm (w - c))
  obtain ⟨Φ, hΦ, hformula, hzero, hone, _⟩ :=
    exists_smallPerturbation_isotopy V hV hVc hsmall hVlip
  have hsnd (t : ℝ) (p : (ℝ ∙ v)ᗮ × ℝ) : (Φ t p).2 = p.2 := by
    rw [hformula]
    simp only [V, horizontalFieldLift, Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]
  have hVs : tsupport V ⊆ univ ×ˢ Ioi (0 : ℝ) := by
    intro p hp
    exact ⟨mem_univ _, hχs ((horizontalFieldLift_tsupport χ g' hp).2)⟩
  have hfix (t : ℝ) (p : (ℝ ∙ v)ᗮ × ℝ) (hp : p ∉ tsupport V) : Φ t p = p := by
    rw [hformula, image_eq_zero_of_notMem_tsupport hp, smul_zero, add_zero]
  obtain ⟨Ψ, hΨ, hΨzero, hnorm, htrack, C, hC, hCt, hΨfix⟩ :=
    exists_radialStereo_transport_isotopy v hv Φ hΦ (fun p => hzero 0 p le_rfl)
      hsnd hVc hVs hfix
  refine ⟨Ψ, hΨ, hΨzero, hnorm, ?_, C, hC, hCt, hΨfix⟩
  filter_upwards [hgerm] with w hw
  rw [htrack, hone 1 (c + w, 1) le_rfl]
  simp only [V, horizontalFieldLift, Prod.fst_add, hχone, one_smul, g',
    add_sub_cancel_left, hw]



theorem exists_boundary_germ_isotopy (v : E) (hv : ‖v‖ = 1)
    (h : (ℝ ∙ v)ᗮ → (ℝ ∙ v)ᗮ) (hh : ContDiff ℝ ∞ h)
    (hh0 : h 0 = 0) (hd0 : fderiv ℝ h 0 = 0) :
    ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) ∧
      (∀ y, Ψ 0 y = y) ∧ (∀ t y, ‖Ψ t y‖ = ‖y‖) ∧
      (∀ᶠ w in 𝓝 0, Ψ 1 (stereoInvFun hv w : E) =
        (stereoInvFun hv (w + h w) : E)) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ radialStereoTarget v ∧
        ∀ t y, y ∉ C → Ψ t y = y := by
  simpa only [zero_add] using exists_boundary_germ_isotopy_at v hv 0 h hh hh0 hd0

end PoincareConjecture.M25.Topology3D
