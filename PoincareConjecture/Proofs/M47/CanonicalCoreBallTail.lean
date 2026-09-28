import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlBarrier
import PoincareConjecture.Proofs.M36.NeckCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem exists_cap_exit_neck_tail
    {g h : RiemannianMetric 3 M} (N : CapCertificate g) (E : EpsilonNeck h)
    (hcarrier : E.carrier = N.end_neck.carrier)
    (hinverse : E.coordinate_inverse = N.end_neck.coordinate_inverse)
    {b : ℝ} (hb16 : 16 ≤ b) (hb : b < N.epsilon⁻¹)
    {gamma : ℝ → M} {s t : ℝ} (hst : s ≤ t)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc s t))
    (hmem : MapsTo gamma (Icc s t) N.carrier)
    (hstart : gamma s ∈ N.closed_core)
    (hfinish : gamma t ∈ frontier (N.recutCarrier b)) :
    ∃ u ∈ Ico s t, gamma u ∈ E.central_sphere ∧
      ENNReal.ofReal (8 * E.scale) ≤ h.pathELength gamma u t ∧
      h.edist (gamma u) E.center ≤ h.pathELength gamma u t := by
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let c := -N.epsilon⁻¹ / 2
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hc : -N.epsilon⁻¹ < c := by dsimp only [c]; linarith
  have hc0 : c < 0 := by dsimp only [c]; linarith
  have hb0 : 0 < b := by linarith
  have hcont : ContinuousOn (N.collarHeight c ∘ gamma) (Icc s t) :=
    (N.collarHeight_continuousOn hc (hc0.trans (hb0.trans hb))).comp
      hgamma.continuousOn hmem
  have hstartH : N.collarHeight c (gamma s) = c :=
    N.collarHeight_eq_of_mem_recut (Or.inl hstart)
  have hfinishH : N.collarHeight c (gamma t) = b :=
    N.collarHeight_eq_of_mem_frontier (by linarith) hb (hc0.trans hb0).le hfinish
  obtain ⟨u, hu, hulevel, hafter⟩ := hcont.exists_last_eq_of_lt hst
    (by simpa only [Function.comp_apply, hstartH] using hc0.le)
    (by simpa only [Function.comp_apply, hfinishH] using hb0)
  change N.collarHeight c (gamma u) = 0 at hulevel
  have htail : MapsTo gamma (Icc u t) E.carrier := by
    intro v hv
    have hcut : c < N.collarHeight c (gamma v) := by
      rcases hv.1.eq_or_lt with heq | hlt
      · subst v
        exact hulevel.symm ▸ hc0
      · exact hc0.trans (hafter v ⟨hlt, hv.2⟩)
    rw [hcarrier]
    exact (N.collarHeight_above_cutoff hcut).1
  have huH : (E.coordinate_inverse (gamma u)).2 = 0 := by
    rw [hinverse]
    exact (N.collarHeight_above_cutoff (hulevel.symm ▸ hc0)).2.symm.trans hulevel
  have htH : (E.coordinate_inverse (gamma t)).2 = b := by
    rw [hinverse]
    exact (N.collarHeight_above_cutoff
      (hfinishH.symm ▸ hc0.trans hb0)).2.symm.trans hfinishH
  have hcentral : gamma u ∈ E.central_sphere :=
    (M36.neck_central_iff E).mpr ⟨htail ⟨le_rfl, hu.2.le⟩, huH⟩
  have hA : 0 < 2 / E.scale := div_pos (by norm_num) E.scale_pos
  have hbarrier := E.height_displacement_le_pathELength_of_axial_speed hA.le
    (fun _ hx v => E.coordinate_inverse_axial_le_tangentNorm hx v) hu.2.le
    (hgamma.mono (Icc_subset_Icc_left hu.1)) htail
  rw [htH, huH, sub_zero, abs_of_pos hb0] at hbarrier
  have hlength : ENNReal.ofReal (8 * E.scale) ≤ h.pathELength gamma u t := by
    apply (ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top).mp
    apply le_trans _ hbarrier
    rw [← ENNReal.ofReal_mul hA.le,
      show (2 / E.scale) * (8 * E.scale) = 16 by field_simp [E.scale_pos.ne']; ring]
    exact ENNReal.ofReal_le_ofReal hb16
  refine ⟨u, hu, hcentral, hlength, ?_⟩
  apply (E.edist_central_sphere_le_two_pi_mul_scale hcentral E.center_on_central_sphere).trans
  apply le_trans _ hlength
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (by linarith [Real.pi_le_four]) E.scale_pos.le)

end PoincareConjecture.Proofs.M47
