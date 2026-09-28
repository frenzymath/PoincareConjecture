import PoincareConjecture.Proofs.M47.CanonicalCoreBallTail
import PoincareConjecture.Proofs.M34.Mathlib.PartialImageTopology










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [MeasurableSpace X] [BorelSpace X] [T3Space X]



theorem exists_cap_image_exit_neck_tail
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (N : CapCertificate g) (E : EpsilonNeck h) (e : OpenPartialHomeomorph M X)
    (hsource : N.carrier ⊆ e.source)
    (hcarrier : E.carrier = e '' N.end_neck.carrier)
    (hinverse : E.coordinate_inverse = N.end_neck.coordinate_inverse ∘ e.symm)
    {b : ℝ} (hb16 : 16 ≤ b) (hb : b < N.epsilon⁻¹)
    {gamma : ℝ → X} {s t : ℝ} (hst : s ≤ t)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc s t))
    (hmem : MapsTo gamma (Icc s t) (e '' N.carrier))
    (hstart : gamma s ∈ e '' N.closed_core)
    (hfinish : gamma t ∈ frontier (e '' N.recutCarrier b)) :
    ∃ a ∈ Ico s t, gamma a ∈ E.central_sphere ∧
      ENNReal.ofReal (8 * E.scale) ≤ h.pathELength gamma a t ∧
      h.edist (gamma a) E.center ≤ h.pathELength gamma a t := by
  let : T25Space X := T3Space.t25Space
  let : T2Space X := T25Space.t2Space
  let c := -N.epsilon⁻¹ / 2
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hc : -N.epsilon⁻¹ < c := by dsimp only [c]; linarith
  have hc0 : c < 0 := by dsimp only [c]; linarith
  have hb0 : 0 < b := by linarith
  have hclosedSource : N.closed_core ⊆ e.source := by
    intro x hx
    rw [N.closed_core_eq_complement_end] at hx
    exact hsource hx.1
  have htarget : MapsTo gamma (Icc s t) e.target := by
    intro a ha
    obtain ⟨x, hx, heq⟩ := hmem ha
    rw [← heq]
    exact e.map_source (hsource hx)
  have hmemOld : MapsTo (e.symm ∘ gamma) (Icc s t) N.carrier := by
    intro a ha
    obtain ⟨x, hx, heq⟩ := hmem ha
    change e.symm (gamma a) ∈ N.carrier
    rw [← heq, e.left_inv (hsource hx)]
    exact hx
  have hstartOld : e.symm (gamma s) ∈ N.closed_core := by
    obtain ⟨x, hx, heq⟩ := hstart
    rw [← heq, e.left_inv (hclosedSource hx)]
    exact hx
  have hcapture := N.recutCarrier_compact_closure (b := b) (by linarith) hb
  have hcaptureSource : closure (N.recutCarrier b) ⊆ e.source :=
    hcapture.2.trans hsource
  have hfront := e.image_frontier_eq_of_isCompact hcapture.1 hcaptureSource
  have hfinishOld : e.symm (gamma t) ∈ frontier (N.recutCarrier b) := by
    rw [← hfront] at hfinish
    obtain ⟨x, hx, heq⟩ := hfinish
    rw [← heq, e.left_inv (hcaptureSource (frontier_subset_closure hx))]
    exact hx
  have hcont : ContinuousOn (N.collarHeight c ∘ (e.symm ∘ gamma)) (Icc s t) :=
    (N.collarHeight_continuousOn hc (hc0.trans (hb0.trans hb))).comp
      (e.symm.continuousOn.comp hgamma.continuousOn htarget) hmemOld
  have hstartH : N.collarHeight c (e.symm (gamma s)) = c :=
    N.collarHeight_eq_of_mem_recut (Or.inl hstartOld)
  have hfinishH : N.collarHeight c (e.symm (gamma t)) = b :=
    N.collarHeight_eq_of_mem_frontier (by linarith) hb (hc0.trans hb0).le hfinishOld
  obtain ⟨a, ha, halevel, hafter⟩ := hcont.exists_last_eq_of_lt hst
    (by simpa only [Function.comp_apply, hstartH] using hc0.le)
    (by simpa only [Function.comp_apply, hfinishH] using hb0)
  change N.collarHeight c (e.symm (gamma a)) = 0 at halevel
  have htail : MapsTo gamma (Icc a t) E.carrier := by
    intro z hz
    have hcut : c < N.collarHeight c (e.symm (gamma z)) := by
      rcases hz.1.eq_or_lt with heq | hlt
      · subst z
        exact halevel.symm ▸ hc0
      · exact hc0.trans (hafter z ⟨hlt, hz.2⟩)
    rw [hcarrier]
    exact ⟨e.symm (gamma z), (N.collarHeight_above_cutoff hcut).1,
      e.right_inv (htarget ⟨ha.1.trans hz.1, hz.2⟩)⟩
  have haH : (E.coordinate_inverse (gamma a)).2 = 0 := by
    rw [hinverse, Function.comp_apply]
    exact (N.collarHeight_above_cutoff (halevel.symm ▸ hc0)).2.symm.trans halevel
  have htH : (E.coordinate_inverse (gamma t)).2 = b := by
    rw [hinverse, Function.comp_apply]
    exact (N.collarHeight_above_cutoff
      (hfinishH.symm ▸ hc0.trans hb0)).2.symm.trans hfinishH
  have hcentral : gamma a ∈ E.central_sphere :=
    (M36.neck_central_iff E).mpr ⟨htail ⟨le_rfl, ha.2.le⟩, haH⟩
  have hA : 0 < 2 / E.scale := div_pos (by norm_num) E.scale_pos
  have hbarrier := E.height_displacement_le_pathELength_of_axial_speed hA.le
    (fun _ hx w => E.coordinate_inverse_axial_le_tangentNorm hx w) ha.2.le
    (hgamma.mono (Icc_subset_Icc_left ha.1)) htail
  rw [htH, haH, sub_zero, abs_of_pos hb0] at hbarrier
  have hlength : ENNReal.ofReal (8 * E.scale) ≤ h.pathELength gamma a t := by
    apply (ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top).mp
    apply le_trans _ hbarrier
    rw [← ENNReal.ofReal_mul hA.le,
      show (2 / E.scale) * (8 * E.scale) = 16 by field_simp [E.scale_pos.ne']; ring]
    exact ENNReal.ofReal_le_ofReal hb16
  refine ⟨a, ha, hcentral, hlength, ?_⟩
  apply (E.edist_central_sphere_le_two_pi_mul_scale hcentral E.center_on_central_sphere).trans
  apply le_trans _ hlength
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (by linarith [Real.pi_le_four]) E.scale_pos.le)

end PoincareConjecture.M47
