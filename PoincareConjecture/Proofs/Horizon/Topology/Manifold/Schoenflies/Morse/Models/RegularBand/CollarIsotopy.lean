import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.CollarExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Normal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem radial_annulus_subset_cthickening
    {δ ε : Real} (hεδ : ε ≤ δ) (hε : ε < 1) {x : E2}
    (hx : |‖x‖ - 1| < ε) : x ∈ cthickening δ (sphere (0 : E2) 1) := by
  have hx0 : x ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_sub, abs_neg, abs_one] at hx
    linarith
  let p : S1 := ⟨‖x‖⁻¹ • x, by simp [norm_smul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]⟩
  have hxp : x = ‖x‖ • (p : E2) := by
    change x = ‖x‖ • (‖x‖⁻¹ • x)
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
  have hdist : dist x (p : E2) = |‖x‖ - 1| := by
    calc
      dist x (p : E2) = ‖‖x‖ • (p : E2) - (p : E2)‖ := by
        rw [dist_eq_norm]
        exact congrArg (fun y : E2 => ‖y - (p : E2)‖) hxp
      _ = ‖(‖x‖ - 1) • (p : E2)‖ := by rw [sub_smul, one_smul]
      _ = |‖x‖ - 1| := by simp [norm_smul, Real.norm_eq_abs]
  exact mem_cthickening_of_dist_le x p δ _ p.property (hdist ▸ hx.le.trans hεδ)

theorem exists_circle_fixing_collar_isotopy
    {e : E2 → E2} (he : ContDiff Real ∞ e)
    (hfix : ∀ p : S1, e p = p)
    (hnormal : ∀ p : S1, 0 < inner Real (p : E2) (fderiv Real e p p))
    {U : Set E2} (hU : IsOpen U) (hcircleU : sphere (0 : E2) 1 ⊆ U) :
    ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
      ∃ S : Set E2, IsCompact S ∧ S ⊆ U ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        (∀ t x, x ∉ S → Φ t x = x) ∧
        (∀ t ∈ Icc (0 : Real) 1, ∀ p : S1, Φ t p = p) ∧
        (∀ x, |‖x‖ - 1| < ε → Φ 1 x = e x) := by
  let H : Real × E2 → E2 := fun z => (1 - z.1) • z.2 + z.1 • e z.2
  have hH : ContDiff Real ∞ H :=
    ((contDiff_const.sub contDiff_fst).smul contDiff_snd).add
      (contDiff_fst.smul (he.comp contDiff_snd))
  have hHp (t : Real) (p : S1) : H (t, p) = p := by
    simp only [H, hfix p, ← add_smul, sub_add_cancel, one_smul]
  obtain ⟨F, hsource, heq, _, hinverse⟩ :=
    exists_spacetime_neighborhood_of_codimZero_isotopy (a := 0) (b := 1)
      (isCompact_sphere (0 : E2) 1) H hH
      (by
        intro t _ x hx y hy hxy
        simpa only [hHp t ⟨x, hx⟩, hHp t ⟨y, hy⟩] using hxy)
      (fun t ht x hx => bijective_fderiv_circle_collar_homotopy he hfix hnormal ht ⟨x, hx⟩)
  have hopen : IsOpen (F.source ∩ H ⁻¹' U) := F.open_source.inter (hU.preimage hH.continuous)
  have htrace : Icc (0 : Real) 1 ×ˢ sphere (0 : E2) 1 ⊆ F.source ∩ H ⁻¹' U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨hsource ⟨ht, hx⟩, ?_⟩
    change H (t, x) ∈ U
    rw [hHp t ⟨x, hx⟩]
    exact hcircleU hx
  obtain ⟨T, V, _, hV, hIT, hcircleV, hTV⟩ :=
    generalized_tube_lemma isCompact_Icc (isCompact_sphere (0 : E2) 1) hopen htrace
  obtain ⟨δ, hδ, hδV⟩ :=
    (isCompact_sphere (0 : E2) 1).exists_cthickening_subset_open hV hcircleV
  let K := cthickening δ (sphere (0 : E2) 1)
  have hK : IsCompact K := (isCompact_sphere (0 : E2) 1).cthickening
  have hKF : Icc (0 : Real) 1 ×ˢ K ⊆ F.source := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact (hTV ⟨hIT ht, hδV hx⟩).1
  have hagreeK : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, F (t, x) = (t, H (t, x)) := by
    intro t ht x hx
    exact heq (hKF ⟨ht, hx⟩)
  have htraceK : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, H (t, x) ∈ U := by
    intro t ht x hx
    have hz : (t, x) ∈ F.source ∩ H ⁻¹' U := hTV ⟨hIT ht, hδV hx⟩
    exact hz.2
  obtain ⟨S, hS, hSU, Φ, hΦ0, hΦ, hΦfix, hmotion⟩ :=
    exists_ambient_isotopy_of_compact_isotopy_within (a := 0) (b := 1)
      (K := K) (U := U) hK hU H hH F hKF hinverse hagreeK htraceK
  let ε := min δ (1 / 2)
  have hεpos : 0 < ε := lt_min hδ (by norm_num)
  have hεone : ε < 1 := (min_le_right δ (1 / 2)).trans_lt (by norm_num)
  refine ⟨ε, hεpos, hεone, S, hS, hSU, Φ, hΦ0, hΦ, hΦfix, ?_, ?_⟩
  · intro t ht p
    have hpK : (p : E2) ∈ K :=
      self_subset_cthickening (δ := δ) (sphere (0 : E2) 1) p.property
    simpa only [hHp] using hmotion t ht p hpK
  · intro x hx
    have hxK := radial_annulus_subset_cthickening (min_le_left δ _) hεone hx
    simpa only [H, sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add] using
      hmotion 1 ⟨by norm_num, le_rfl⟩ x hxK

theorem exists_circle_fixing_collar_isotopy_of_diffeomorph
    (P : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hfix : ∀ p : S1, P p = p)
    {U : Set E2} (hU : IsOpen U) (hcircleU : sphere (0 : E2) 1 ⊆ U) :
    ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
      ∃ S : Set E2, IsCompact S ∧ S ⊆ U ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        (∀ t x, x ∉ S → Φ t x = x) ∧
        (∀ t ∈ Icc (0 : Real) 1, ∀ p : S1, Φ t p = p) ∧
        (∀ x, |‖x‖ - 1| < ε → Φ 1 x = P x) := by
  have hsphere : P.toHomeomorph '' sphere (0 : E2) 1 =
      (Homeomorph.refl E2) '' sphere (0 : E2) 1 := by
    simp only [Homeomorph.refl_apply, id_eq, image_id']
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      change P p ∈ sphere (0 : E2) 1
      rw [hfix ⟨p, hp⟩]
      exact hp
    · intro hx
      exact ⟨x, hx, hfix ⟨x, hx⟩⟩
  have hdim : 1 < Module.rank Real E2 := by rw [← Module.finrank_eq_rank]; norm_num
  have hball : P '' ball (0 : E2) 1 = ball (0 : E2) 1 := by
    simpa using P.toHomeomorph.image_ball_eq_of_image_sphere_eq
      (Homeomorph.refl E2) hdim hsphere
  apply exists_circle_fixing_collar_isotopy P.contDiff hfix ?_ hU hcircleU
  apply CircleCollar.normal_derivative_pos_of_inward P.contDiff hfix
  · intro p
    have h := (P.mfderivToContinuousLinearEquiv (by simp) (p : E2)).injective
    change Injective (mfderiv (𝓡 2) (𝓡 2) P (p : E2)) at h
    simpa only [mfderiv_eq_fderiv, TangentSpace] using h
  · intro p
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : Real) < 0 by norm_num)] with t ht
    have hx : (1 + t) • (p : E2) ∈ ball (0 : E2) 1 := by
      rw [mem_ball_zero_iff, norm_smul]
      simp only [norm_eq_of_mem_sphere, Real.norm_eq_abs, mul_one,
        abs_of_pos (by linarith [ht.1] : 0 < 1 + t)]
      linarith [ht.2]
    exact mem_ball_zero_iff.mp (hball ▸ mem_image_of_mem P hx)

end Poincare.Manifold.Schoenflies
