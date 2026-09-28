import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverBoundaryDifferential












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

private theorem derivative_ge_of_right_linear_bound
    {f : ℝ → ℝ} {a c : ℝ} (hd : HasDerivWithinAt f a (Ioi 0) 0)
    (hf0 : f 0 = 0) (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), c * t ≤ f t) : c ≤ a := by
  apply ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope'
    (by simp : (0 : ℝ) ∉ Ioi 0)).mp hd)
  filter_upwards [hb, self_mem_nhdsWithin] with t ht htpos
  change 0 < t at htpos
  simp only [slope_def_field, hf0, sub_zero]
  exact (le_div_iff₀ htpos).mpr ht

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem scalarCoverPotential_boundary_radial_pos
    {H : Plane → ℝ} {J : Plane → Plane →L[ℝ] ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hJc : ContinuousOn J (closure scalarAnnulus))
    (hJeq : EqOn J (fderiv ℝ H) scalarAnnulus)
    {r : ℝ} (hr : r = 1 ∨ r = 2) (t : ℝ) :
    0 < scalarCoverPotentialDifferential J (r, t) (1, 0) := by
  obtain ⟨c, hc, hsep⟩ :=
    annular_harmonic_linear_boundary_separation D hHc hHs hlap hinner houter
  have hsmall : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (gt_mem_nhds zero_lt_one))
  rcases hr with rfl | rfl
  · have hz : (1, t) ∈ closure scalarCoverStrip := by
      rw [scalarCoverStrip_closure]
      norm_num
    have hD := scalarCoverPotential_hasFDerivWithinAt_closure hHc hHs hJc hJeq hz
    let b : ℝ → Cover := fun s => (1 + s, t)
    have hb : HasDerivAt b (1, 0) 0 := by
      simpa only [b, id_eq] using
        ((hasDerivAt_id (0 : ℝ)).const_add 1).prodMk (hasDerivAt_const (0 : ℝ) t)
    have hmap : MapsTo b (Ioo 0 1) (closure scalarCoverStrip) := by
      intro s hs
      rw [scalarCoverStrip_closure]
      change 1 + s ∈ Icc (1 : ℝ) 2
      constructor <;> linarith [hs.1, hs.2]
    have hd : HasDerivWithinAt ((H ∘ scalarCoverMap) ∘ b)
        (scalarCoverPotentialDifferential J (1, t) (1, 0)) (Ioi 0) 0 :=
      (hD.comp_hasDerivWithinAt_of_eq 0 hb.hasDerivWithinAt hmap
        (by simp [b])).mono_of_mem_nhdsWithin hsmall
    apply hc.trans_le (derivative_ge_of_right_linear_bound hd ?_ ?_)
    · change H (scalarCoverMap (1 + 0, t)) = 0
      apply hinner
      norm_num [scalarCoverMap, scalarCirclePoint_norm]
    · filter_upwards [hsmall] with s hs
      have hn : ‖scalarCoverMap (1 + s, t)‖ = 1 + s := by
        rw [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos (by linarith [hs.1])]
      have hmem : 0 ≤ scalarAnnulusDefining (scalarCoverMap (1 + s, t)) := by
        rw [scalarAnnulusDefining_nonneg, hn]
        constructor <;> linarith [hs.1, hs.2]
      have h := (hsep _ hmem).1
      rw [hn] at h
      change c * s ≤ H (scalarCoverMap (1 + s, t))
      nlinarith
  · have hz : (2, t) ∈ closure scalarCoverStrip := by
      rw [scalarCoverStrip_closure]
      norm_num
    have hD := scalarCoverPotential_hasFDerivWithinAt_closure hHc hHs hJc hJeq hz
    let b : ℝ → Cover := fun s => (2 - s, t)
    have hb : HasDerivAt b (-1, 0) 0 := by
      simpa only [b, id_eq, zero_sub, Pi.sub_apply] using!
        ((hasDerivAt_const (0 : ℝ) 2).sub (hasDerivAt_id (0 : ℝ))).prodMk
          (hasDerivAt_const (0 : ℝ) t)
    have hmap : MapsTo b (Ioo 0 1) (closure scalarCoverStrip) := by
      intro s hs
      rw [scalarCoverStrip_closure]
      change 2 - s ∈ Icc (1 : ℝ) 2
      constructor <;> linarith [hs.1, hs.2]
    have hd0 := (hD.comp_hasDerivWithinAt_of_eq 0 hb.hasDerivWithinAt hmap
      (by simp [b])).mono_of_mem_nhdsWithin hsmall
    have hd : HasDerivWithinAt (fun s : ℝ => 1 - H (scalarCoverMap (2 - s, t)))
        (scalarCoverPotentialDifferential J (2, t) (1, 0)) (Ioi 0) 0 := by
      have h := (hasDerivWithinAt_const (0 : ℝ) (Ioi 0) 1).sub hd0
      have hneg : ((-1, 0) : ℝ × ℝ) = -(1, 0) := by ext <;> norm_num
      simpa only [b, Function.comp_apply, hneg, map_neg, zero_sub, neg_neg, Pi.sub_apply] using! h
    apply hc.trans_le (derivative_ge_of_right_linear_bound hd ?_ ?_)
    · have hh := houter (scalarCoverMap (2, t)) (by
        norm_num [scalarCoverMap, scalarCirclePoint_norm])
      simp only [sub_zero, hh, sub_self]
    · filter_upwards [hsmall] with s hs
      have hn : ‖scalarCoverMap (2 - s, t)‖ = 2 - s := by
        rw [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos (by linarith [hs.2])]
      have hmem : 0 ≤ scalarAnnulusDefining (scalarCoverMap (2 - s, t)) := by
        rw [scalarAnnulusDefining_nonneg, hn]
        constructor <;> linarith [hs.1, hs.2]
      have h := (hsep _ hmem).2
      rw [hn] at h
      nlinarith

end PoincareConjecture.M64Uniformization
