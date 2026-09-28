import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularEvolution











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_stackAnnularChart_in_open
    (g : (ℝ × E2) → E2) (U W : Set (ℝ × E2))
    (hU : IsOpen U) (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g U)
    (A a b B : ℝ) (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCU : Icc A B ×ˢ sphere (0 : E2) 1 ⊆ U)
    (hCW : Icc A B ×ˢ sphere (0 : E2) 1 ⊆ W)
    (hfixed : ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1, g (z, q) = q)
    (hn : ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1,
      0 < ⟪q, fderiv ℝ (fun y => g (z, y)) q q⟫_ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 / 4 ∧
      ∃ e : OpenPartialHomeomorph (ℝ × (ℝ × E2)) (ℝ × (ℝ × E2)),
        (e : (ℝ × (ℝ × E2)) → (ℝ × (ℝ × E2))) = stackAnnularInterpolation g ∧
        e.source = Ioo (-2 : ℝ) 3 ×ˢ
          (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * delta}) ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
        (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * delta}) ⊆ U ∧
        e.target ⊆ (univ : Set ℝ) ×ˢ W ∧
        Icc (-1 : ℝ) 2 ×ˢ
          (Icc a b ×ˢ {x : E2 | |‖x‖ - 1| ≤ delta}) ⊆ e.source := by
  obtain ⟨delta0, hd0, hd0quarter, e0, heq, hs0, he0, hi0, hAnnU, _hinner⟩ :=
    exists_stackAnnularInterpolationChart g U hU hg A a b B hAa hab hbB hCU hfixed hn
  let K : Set (ℝ × (ℝ × E2)) :=
    Icc (-2 : ℝ) 3 ×ˢ (Icc A B ×ˢ sphere (0 : E2) 1)
  have hK : IsCompact K := isCompact_Icc.prod
    (isCompact_Icc.prod (isCompact_sphere (0 : E2) 1))
  have hF : ContDiffOn ℝ ∞ (stackAnnularInterpolation g) (univ ×ˢ U) :=
    contDiff_fst.contDiffOn.prodMk (contDiff_snd.fst.contDiffOn.prodMk
      (contDiff_snd.snd.contDiffOn.add
        ((Real.smoothTransition.contDiff.comp contDiff_fst).contDiffOn.smul
          ((hg.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)).sub
            contDiff_snd.snd.contDiffOn))))
  let V : Set (ℝ × (ℝ × E2)) :=
    (univ ×ˢ U) ∩ (stackAnnularInterpolation g) ⁻¹' (univ ×ˢ W)
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod hU) (isOpen_univ.prod hW)
  have hKV : K ⊆ V := by
    rintro ⟨t, z, q⟩ ⟨_ht, hz, hq⟩
    refine ⟨⟨mem_univ _, hCU ⟨hz, hq⟩⟩, ?_⟩
    have hfix : stackAnnularInterpolation g (t, (z, q)) = (t, (z, q)) := by
      simp only [stackAnnularInterpolation, hfixed z hz q hq,
        sub_self, smul_zero, add_zero]
    change stackAnnularInterpolation g (t, (z, q)) ∈ univ ×ˢ W
    rw [hfix]
    exact ⟨mem_univ _, hCW ⟨hz, hq⟩⟩
  obtain ⟨d, hd, hdV⟩ := hK.exists_thickening_subset_open hV hKV
  obtain ⟨delta, hdelta, hdm⟩ := exists_between
    (show (0 : ℝ) < min delta0 (d / 3) from lt_min hd0 (div_pos hd (by norm_num)))
  have hdd0 : delta < delta0 := (lt_min_iff.mp hdm).1
  have hdd : 2 * delta < d := by linarith only [(lt_min_iff.mp hdm).2, hd]
  have hdist (x : E2) : dist x (circleDirection x : E2) = |‖x‖ - 1| := by
    rw [dist_eq_norm]
    have hsub : x - (circleDirection x : E2) =
        (‖x‖ - 1) • (circleDirection x : E2) := by
      rw [sub_smul, one_smul, circleDirection_norm_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
  let O : Set (ℝ × (ℝ × E2)) := Ioo (-2 : ℝ) 3 ×ˢ
    (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * delta})
  have hO : IsOpen O := isOpen_Ioo.prod (isOpen_Ioo.prod
    (isOpen_lt (continuous_norm.sub continuous_const).abs continuous_const))
  have hOe : O ⊆ e0.source := by
    rintro ⟨t, z, x⟩ ⟨ht, hz, hx⟩
    rw [hs0]
    refine ⟨ht, hz, ?_⟩
    change |‖x‖ - 1| < 2 * delta at hx
    change |‖x‖ - 1| < 2 * delta0
    linarith only [hx, hdd0]
  have hOV : O ⊆ V := by
    rintro ⟨t, z, x⟩ ⟨ht, hz, hx⟩
    apply hdV
    apply mem_thickening_iff.mpr
    refine ⟨(t, (z, (circleDirection x : E2))),
      ⟨⟨ht.1.le, ht.2.le⟩, ⟨hz.1.le, hz.2.le⟩, (circleDirection x).2⟩, ?_⟩
    simpa only [dist_prod_same_left, hdist] using hx.trans hdd
  let e := e0.restrOpen O hO
  have hse : e.source = O := inter_eq_right.mpr hOe
  refine ⟨delta, hdelta, hdd0.trans hd0quarter, e, heq, hse,
    he0.mono inter_subset_left, hi0.mono (fun _ hp => hp.1), ?_, ?_, ?_⟩
  · rintro ⟨z, x⟩ ⟨hz, hx⟩
    apply hAnnU
    refine ⟨hz, ?_⟩
    change |‖x‖ - 1| < 2 * delta at hx
    change |‖x‖ - 1| < 2 * delta0
    linarith only [hx, hdd0]
  · intro p hp
    have hinv : e.symm p ∈ O := hse ▸ e.map_target hp
    have himage := (hOV hinv).2
    change stackAnnularInterpolation g (e.symm p) ∈ univ ×ˢ W at himage
    have hform : (e : (ℝ × (ℝ × E2)) → (ℝ × (ℝ × E2))) =
        stackAnnularInterpolation g := heq
    rw [← hform, e.right_inv hp] at himage
    exact himage
  · rintro ⟨t, z, x⟩ ⟨ht, hz, hx⟩
    change |‖x‖ - 1| ≤ delta at hx
    rw [hse]
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      ⟨hAa.trans_le hz.1, hz.2.trans_lt hbB⟩, ?_⟩
    change |‖x‖ - 1| < 2 * delta
    linarith only [hx, hdelta]

end PoincareConjecture.M25.Topology3D
