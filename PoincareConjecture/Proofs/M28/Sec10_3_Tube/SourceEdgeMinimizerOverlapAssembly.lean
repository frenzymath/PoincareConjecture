import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe v

namespace PoincareConjecture.M28

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

set_option maxHeartbeats 1000000 in

theorem source_edge_whole_overlap_of_minimizer_anchors
    (N Q : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : Q.epsilon = N.epsilon)
    (hscale : (0.999 : ℝ) * N.scale < Q.scale ∧
      Q.scale < (1.001 : ℝ) * N.scale)
    (hcenter : Q.center ∈
      closure (N.region ((255 : ℝ) * N.epsilon⁻¹ / 256) N.epsilon⁻¹))
    (hout : Q.center ∉ N.carrier)
    (hforward : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2))
    (hrecip : Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
      N.region (-(0.2 : ℝ) * N.epsilon⁻¹)
        ((0.6 : ℝ) * N.epsilon⁻¹))
    (hband : ∀ y ∈ Q.region (-(0.31 : ℝ) * N.epsilon⁻¹)
        (-(0.29 : ℝ) * N.epsilon⁻¹),
      y ∈ N.region ((0.59 : ℝ) * N.epsilon⁻¹)
        ((0.76 : ℝ) * N.epsilon⁻¹))
    {γ : ℝ → M} {t₁ tN tP t₂ : ℝ}
    (htransition : Q.center ∈ frontier N.carrier →
      ∃ σ : ℝ, σ = 1 ∧
      ∃ v ∈ Ioo tN tP,
        σ * (N.coordinate_inverse (γ v)).2 =
          (509 : ℝ) * N.epsilon⁻¹ / 512 ∧
        (∀ t ∈ Ioo v tP,
          (509 : ℝ) * N.epsilon⁻¹ / 512 <
            σ * (N.coordinate_inverse (γ t)).2) ∧
        neckSignedRegion N σ ((127 : ℝ) * N.epsilon⁻¹ / 128)
          N.epsilon⁻¹ ⊆ Q.carrier)
    {U : Set M} (hNU : N.carrier ⊆ U) (hQU : Q.carrier ⊆ U)
    (h₁ : t₁ < tN) (hNP : tN < tP) (h₂ : tP < t₂)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc t₁ t₂))
    (_hγU : MapsTo γ (Icc t₁ t₂) U)
    (hcN : γ tN = N.center) (hcQ : γ tP = Q.center)
    (hedge : MapsTo γ (Ico tN tP) N.carrier)
    (hmin : ∀ a b, t₁ ≤ a → a ≤ b → b ≤ t₂ →
      g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hadd : ∀ a b c, t₁ ≤ a → a ≤ b → b ≤ c → c ≤ t₂ →
      g.pathELength γ a c = g.pathELength γ a b + g.pathELength γ b c)
    (hanchor₁ : g.pathELength γ t₁ tN =
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹))
    (hanchor₂ : g.pathELength γ tP t₂ =
      ENNReal.ofReal ((0.3 : ℝ) * Q.scale * N.epsilon⁻¹)) :
    N.carrier ∩ Q.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) := by
  let A : ℝ := N.epsilon⁻¹
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcenter_path : g.edist N.center Q.center ≤
      g.pathELength γ tN tP := by
    rw [← hcN, ← hcQ]
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc h₁.le h₂.le)) rfl rfl hNP.le
  have hApos : 0 < A := inv_pos.mpr N.epsilon_pos
  have hA : (1000 : ℝ) ≤ A := by
    change (1000 : ℝ) ≤ N.epsilon⁻¹
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    norm_num at hε ⊢
    nlinarith [hε]
  have hrootLower : (0.999 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    apply Real.le_sqrt_of_sq_le
    have he : N.epsilon ≤ (0.001 : ℝ) := by
      norm_num at hε ⊢
      exact hε
    nlinarith [N.epsilon_pos, he]
  have hrootUpper : Real.sqrt (1 + N.epsilon) ≤ (1.0005 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hfront : Q.center ∈ frontier N.carrier := by
    rw [N.carrier_open.frontier_eq]
    exact ⟨closure_mono (N.region_subset_carrier _ _) hcenter, hout⟩
  obtain ⟨σ, hσ, v, hv, hvlevel, hafter, hQband⟩ := htransition hfront
  subst σ
  have hγN (t : ℝ) (ht : t ∈ Icc tN v) : γ t ∈ N.carrier := by
    exact hedge ⟨ht.1, lt_of_le_of_lt ht.2 hv.2⟩
  have hγQ : MapsTo γ (Icc v tP) Q.carrier := by
    intro t ht
    by_cases htv : t = tP
    · subst t
      rw [hcQ]
      exact Q.central_sphere_subset Q.center_on_central_sphere
    · have htv' : t < tP := lt_of_le_of_ne ht.2 htv
      have htvN : t ∈ Ico tN tP := ⟨hv.1.le.trans ht.1, htv'⟩
      have hN := hedge htvN
      have hcoord := (N.coordinate_inverse_mem (γ t) hN).2
      have hsig : (N.coordinate_inverse (γ t)).2 ∈ Ioo (-A) A := by
        simpa [A] using hcoord
      have hsigned : (127 : ℝ) * A / 128 <
          (N.coordinate_inverse (γ t)).2 := by
        by_cases htvv : t = v
        · subst t
          linarith [hvlevel]
        · have hlt : v < t := lt_of_le_of_ne ht.1 (Ne.symm htvv)
          linarith [hafter t ⟨hlt, htv'⟩]
      exact hQband ⟨hN, by simpa [A] using hsigned,
        by simpa [A] using hsig.2⟩
  let z₁ := γ t₁
  let z₂ := γ t₂
  have hz₁N : z₁ ∈ N.carrier := by
    have hd : g.edist N.center z₁ ≤ g.pathELength γ t₁ tN := by
      rw [← hcN]
      rw [show g.edist (γ tN) (γ t₁) = g.edist (γ t₁) (γ tN) from
        Manifold.riemannianEDist_comm]
      have htN₂ : tN ≤ t₂ := hNP.le.trans h₂.le
      exact Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc le_rfl htN₂)) rfl rfl h₁.le
    have hs : g.pathELength γ t₁ tN =
        ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) := by
      simpa [A] using hanchor₁
    have hz := mem_middle_slab_of_edist_center_le N hε (hs ▸ hd)
    exact hz.1
  have hz₁slab : z₁ ∈ N.region (-(0.31 : ℝ) * A) ((0.31 : ℝ) * A) := by
    have hd : g.edist N.center z₁ ≤ g.pathELength γ t₁ tN := by
      rw [← hcN]
      rw [show g.edist (γ tN) (γ t₁) = g.edist (γ t₁) (γ tN) from
        Manifold.riemannianEDist_comm]
      have htN₂ : tN ≤ t₂ := hNP.le.trans h₂.le
      exact Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc le_rfl htN₂)) rfl rfl h₁.le
    simpa [A] using (mem_middle_slab_of_edist_center_le N hε (hanchor₁ ▸ hd))
  have hz₂Q : z₂ ∈ Q.carrier := by
    have hpath : g.edist Q.center z₂ ≤ g.pathELength γ tP t₂ := by
      rw [← hcQ]
      have ht₁P : t₁ ≤ tP := h₁.le.trans hNP.le
      exact Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc ht₁P le_rfl)) rfl rfl h₂.le
    have hs : g.pathELength γ tP t₂ =
        ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) := by
      simpa [A] using hanchor₂
    exact (mem_middle_slab_of_edist_center_le Q
      (heq ▸ hε) (by simpa [heq] using (hanchor₂ ▸ hpath))).1
  have hz₂slab : z₂ ∈ Q.region (-(0.31 : ℝ) * A) ((0.31 : ℝ) * A) := by
    have hpath : g.edist Q.center z₂ ≤ g.pathELength γ tP t₂ := by
      rw [← hcQ]
      have ht₁P : t₁ ≤ tP := h₁.le.trans hNP.le
      exact Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc ht₁P le_rfl)) rfl rfl h₂.le
    simpa [A, heq] using (mem_middle_slab_of_edist_center_le Q (heq ▸ hε)
      (by simpa [heq] using (hanchor₂ ▸ hpath)))
  have hmin₁ : ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) ≤
      intrinsicEDist g U z₁ N.center := by
    have hdist : g.pathELength γ t₁ tN =
        intrinsicEDist g U z₁ N.center := by
      simpa [z₁, hcN] using hmin t₁ tN le_rfl h₁.le
        (hNP.le.trans h₂.le)
    have heqall : ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) =
        intrinsicEDist g U z₁ N.center := by
      calc
        _ = g.pathELength γ t₁ tN := by simpa [A] using hanchor₁.symm
        _ = intrinsicEDist g U z₁ N.center := hdist
    exact heqall.le
  have hmin₂ : ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) ≤
      intrinsicEDist g U Q.center z₂ := by
    have hdist : g.pathELength γ tP t₂ =
        intrinsicEDist g U Q.center z₂ := by
      simpa [z₂, hcQ] using hmin tP t₂ (h₁.le.trans hNP.le) h₂.le le_rfl
    have heqall : ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) =
        intrinsicEDist g U Q.center z₂ := by
      calc
        _ = g.pathELength γ tP t₂ := by simpa [A] using hanchor₂.symm
        _ = intrinsicEDist g U Q.center z₂ := hdist
    exact heqall.le
  have hheight₁ : (0.292 : ℝ) * A ≤
      |(N.coordinate_inverse z₁).2| := by
    apply anchor_height_lower N hε (by simpa [A] using hA) hNU hz₁N
    have hmin₁' : ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) ≤
        intrinsicEDist g U N.center z₁ := by
      rw [intrinsicEDist_comm_set]
      simpa [A] using hmin₁
    exact hmin₁'
  have hAq : (1000 : ℝ) ≤ Q.epsilon⁻¹ := by
    simpa [heq] using hA
  have hheight₂ : (0.292 : ℝ) * A ≤
      |(Q.coordinate_inverse z₂).2| := by
    have hqmin : ENNReal.ofReal ((0.3 : ℝ) * Q.scale * Q.epsilon⁻¹) ≤
        intrinsicEDist g U Q.center z₂ := by
      simpa [heq] using hmin₂
    have hq := anchor_height_lower Q (heq ▸ hε) hAq hQU hz₂Q hqmin
    simpa [heq] using hq
  have hcenter0 : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier
      (N.central_sphere_subset N.center_on_central_sphere)).mp
      N.center_on_central_sphere
  have hsign₁ : (N.coordinate_inverse z₁).2 < 0 := by
    by_contra hnot
    have hpos : 0 ≤ (N.coordinate_inverse z₁).2 := le_of_not_gt hnot
    have hheight₁' : (0.292 : ℝ) * A ≤
        (N.coordinate_inverse z₁).2 := by
      simpa [abs_of_nonneg hpos] using hheight₁
    have hzl : -(0.31 : ℝ) * A < (N.coordinate_inverse z₁).2 :=
      hz₁slab.2.1
    have hzu : (N.coordinate_inverse z₁).2 < (0.31 : ℝ) * A :=
      hz₁slab.2.2
    have hvcoord : (N.coordinate_inverse (γ v)).2 =
        (509 : ℝ) * A / 512 := by
      simpa [A] using hvlevel
    have hvabs : |(N.coordinate_inverse (γ v)).2| =
        (509 : ℝ) * A / 512 := by
      rw [hvcoord, abs_of_pos (by positivity)]
    have hdisp := N.path_axial_displacement_le_sharp hv.1.le
      (hγ.mono (Icc_subset_Icc h₁.le (hv.2.le.trans h₂.le))) hγN
    rw [hcN, hcenter0, sub_zero, hvabs] at hdisp
    have hdisp' : ENNReal.ofReal
        (N.scale * (0.999 : ℝ) * ((509 : ℝ) * A / 512)) ≤
        g.pathELength γ tN v := by
      calc
        _ ≤ ENNReal.ofReal
            (N.scale * Real.sqrt (1 - N.epsilon) *
              ((509 : ℝ) * A / 512)) := by
          apply ENNReal.ofReal_le_ofReal
          have hnonneg : 0 ≤ N.scale * ((509 : ℝ) * A / 512) := by
            exact mul_nonneg N.scale_pos.le (by positivity)
          have hmul := mul_le_mul_of_nonneg_right hrootLower hnonneg
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
        _ ≤ g.pathELength γ tN v := hdisp
    have hprefix := hadd t₁ tN v le_rfl h₁.le hv.1.le
      (hv.2.le.trans h₂.le)
    have hprefixLower : ENNReal.ofReal
        ((0.3 : ℝ) * N.scale * A +
          N.scale * (0.999 : ℝ) * ((509 : ℝ) * A / 512)) ≤
        g.pathELength γ t₁ v := by
      calc
        _ = ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) +
            ENNReal.ofReal
              (N.scale * (0.999 : ℝ) * ((509 : ℝ) * A / 512)) := by
          have h₁nonneg : 0 ≤ (0.3 : ℝ) * N.scale * A := by
            exact mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
          have h₂nonneg : 0 ≤ N.scale * (0.999 : ℝ) *
              ((509 : ℝ) * A / 512) := by
            have hK : 0 ≤ (509 : ℝ) * A / 512 := by
              nlinarith [hApos]
            exact mul_nonneg (mul_nonneg N.scale_pos.le (by norm_num)) hK
          rw [ENNReal.ofReal_add h₁nonneg h₂nonneg]
        _ ≤ g.pathELength γ t₁ tN + g.pathELength γ tN v :=
          add_le_add hanchor₁.symm.le hdisp'
        _ = g.pathELength γ t₁ v := by
          simpa only [hanchor₁] using hprefix.symm
    have hdiff : |(N.coordinate_inverse (γ v)).2 -
        (N.coordinate_inverse z₁).2| ≤ (0.7047 : ℝ) * A := by
      rw [hvcoord, abs_of_nonneg (by nlinarith)]
      nlinarith
    have hconst : Real.sqrt 2 * (Real.pi + 1) ≤ (7.1 : ℝ) := by
      have hs2 : Real.sqrt 2 ≤ (1.415 : ℝ) := by
        have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
        nlinarith [Real.sqrt_nonneg 2]
      have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
      have hmul := mul_le_mul hs2
        (show Real.pi + 1 ≤ (5 : ℝ) by nlinarith [Real.pi_le_four])
        (by positivity) (by positivity)
      nlinarith [hmul]
    have hreal : N.scale * Real.sqrt (1 + N.epsilon) *
          (|(N.coordinate_inverse (γ v)).2 -
            (N.coordinate_inverse z₁).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
        N.scale * (1.0005 : ℝ) * ((0.7047 : ℝ) * A + 7.1) := by
      have hsum : |(N.coordinate_inverse (γ v)).2 -
            (N.coordinate_inverse z₁).2| + Real.sqrt 2 * (Real.pi + 1) ≤
          (0.7047 : ℝ) * A + 7.1 := by linarith [hconst, hdiff]
      have hinner0 : 0 ≤ |(N.coordinate_inverse (γ v)).2 -
          (N.coordinate_inverse z₁).2| + Real.sqrt 2 * (Real.pi + 1) := by
        positivity
      have hstep := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrootUpper hinner0) N.scale_pos.le
      have hstep' : N.scale * Real.sqrt (1 + N.epsilon) *
          (|(N.coordinate_inverse (γ v)).2 -
            (N.coordinate_inverse z₁).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
          N.scale * (1.0005 : ℝ) *
            (|(N.coordinate_inverse (γ v)).2 -
              (N.coordinate_inverse z₁).2| + Real.sqrt 2 * (Real.pi + 1)) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep
      have hstep'' := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg N.scale_pos.le (by norm_num : (0 : ℝ) ≤ 1.0005))
      have hstep''' : N.scale * (1.0005 : ℝ) *
          (|(N.coordinate_inverse (γ v)).2 -
            (N.coordinate_inverse z₁).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
          N.scale * (1.0005 : ℝ) * ((0.7047 : ℝ) * A + 7.1) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep''
      exact hstep'.trans hstep'''
    have hcost : intrinsicEDist g U z₁ (γ v) ≤
        ENNReal.ofReal
          (N.scale * (1.0005 : ℝ) * ((0.7047 : ℝ) * A + 7.1)) := by
      apply (intrinsicEDist_mono_of_subset (g := g) hNU).trans
      apply (N.intrinsicEDist_le_axial_add hz₁N
        (hγN v ⟨hv.1.le, le_rfl⟩)).trans
      exact ENNReal.ofReal_le_ofReal hreal
    have hpathUpper : g.pathELength γ t₁ v ≤
        ENNReal.ofReal
          (N.scale * (1.0005 : ℝ) * ((0.7047 : ℝ) * A + 7.1)) := by
      rw [hmin t₁ v le_rfl (h₁.trans hv.1).le
        (hv.2.le.trans h₂.le)]
      exact hcost
    have hbad := hprefixLower.trans hpathUpper
    have hbad' : (0.3 : ℝ) * N.scale * A +
          N.scale * (0.999 : ℝ) * ((509 : ℝ) * A / 512) ≤
        N.scale * (1.0005 : ℝ) * ((0.7047 : ℝ) * A + 7.1) := by
      have hcoef : 0 ≤ N.scale * (1.0005 : ℝ) :=
        mul_nonneg N.scale_pos.le (by norm_num)
      have hpositive : 0 ≤ (0.7047 : ℝ) * A + 7.1 := by
        nlinarith [hApos]
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hcoef hpositive)).mp hbad
    nlinarith only [hbad', N.scale_pos, hA]
  have hsign₂ : 0 < (Q.coordinate_inverse z₂).2 := by
    by_contra hnot
    have hnonpos : (Q.coordinate_inverse z₂).2 ≤ 0 := le_of_not_gt hnot
    have hheight₂' : (Q.coordinate_inverse z₂).2 ≤ -(0.292 : ℝ) * A := by
      rw [abs_of_nonpos hnonpos] at hheight₂
      have hh := neg_le_neg hheight₂
      simpa only [neg_neg, neg_mul] using hh
    have hz₂band : z₂ ∈ Q.region (-(0.31 : ℝ) * A) (-(0.29 : ℝ) * A) := by
      refine ⟨hz₂Q, hz₂slab.2.1, ?_⟩
      linarith only [hheight₂', hApos]
    have hz₂N : z₂ ∈ N.region ((0.59 : ℝ) * A) ((0.76 : ℝ) * A) := by
      have hz₂band' : z₂ ∈ Q.region (-(0.31 : ℝ) * N.epsilon⁻¹)
          (-(0.29 : ℝ) * N.epsilon⁻¹) := by
        change z₂ ∈ Q.region (-(0.31 : ℝ) * A) (-(0.29 : ℝ) * A)
        exact hz₂band
      change z₂ ∈ N.region ((0.59 : ℝ) * N.epsilon⁻¹)
        ((0.76 : ℝ) * N.epsilon⁻¹)
      exact hband z₂ hz₂band'
    have hdistNP : ENNReal.ofReal ((0.99 : ℝ) * N.scale * A) ≤
        g.pathELength γ tN tP := by
      have hdist := N.balanced_edist_lower_of_not_mem_carrier hε hout
      have hdistA : ENNReal.ofReal ((0.99 : ℝ) * N.scale * A) ≤
          g.edist N.center Q.center := by
        change ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
          g.edist N.center Q.center
        exact hdist
      exact hdistA.trans hcenter_path
    have hanchor₂lower : ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) ≤
        g.pathELength γ tP t₂ := by
      exact hanchor₂.symm.le
    have hpathN₂ : ENNReal.ofReal
          ((0.99 : ℝ) * N.scale * A + (0.3 : ℝ) * Q.scale * A) ≤
        g.pathELength γ tN t₂ := by
      have ha : 0 ≤ (0.99 : ℝ) * N.scale * A := by
        exact mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
      have hb : 0 ≤ (0.3 : ℝ) * Q.scale * A := by
        exact mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) hApos.le
      rw [ENNReal.ofReal_add ha hb]
      calc
        ENNReal.ofReal ((0.99 : ℝ) * N.scale * A) +
              ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) ≤
            g.pathELength γ tN tP + g.pathELength γ tP t₂ :=
          add_le_add hdistNP hanchor₂lower
        _ = g.pathELength γ tN t₂ :=
          (hadd tN tP t₂ h₁.le hNP.le h₂.le le_rfl).symm
    have hz₂Ncar : z₂ ∈ N.carrier := hz₂N.1
    have hNcenter : N.center ∈ N.carrier :=
      N.central_sphere_subset N.center_on_central_sphere
    have hcoordN : |(N.coordinate_inverse z₂).2 -
        (N.coordinate_inverse N.center).2| ≤ (0.76 : ℝ) * A := by
      rw [hcenter0, sub_zero, abs_of_nonneg]
      · exact hz₂N.2.2.le
      · nlinarith [hz₂N.2.1, hApos]
    have hrealN : N.scale * Real.sqrt (1 + N.epsilon) *
          (|(N.coordinate_inverse z₂).2 -
            (N.coordinate_inverse N.center).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
        N.scale * (1.0005 : ℝ) * ((0.76 : ℝ) * A + 7.1) := by
      have hs2 : Real.sqrt 2 ≤ (1.415 : ℝ) := by
        have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
        nlinarith only [hs2sq, Real.sqrt_nonneg 2]
      have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
      have hconst : Real.sqrt 2 * (Real.pi + 1) ≤ (7.1 : ℝ) := by
        have hmul := mul_le_mul hs2
          (show Real.pi + 1 ≤ (5 : ℝ) by linarith only [Real.pi_le_four])
          (add_nonneg Real.pi_pos.le (by norm_num))
          (by norm_num : (0 : ℝ) ≤ 1.415)
        nlinarith only [hmul]
      have hsum : |(N.coordinate_inverse z₂).2 -
            (N.coordinate_inverse N.center).2| +
            Real.sqrt 2 * (Real.pi + 1) ≤ (0.76 : ℝ) * A + 7.1 := by
        linarith only [hcoordN, hconst]
      have hinner0 : 0 ≤ |(N.coordinate_inverse z₂).2 -
          (N.coordinate_inverse N.center).2| + Real.sqrt 2 * (Real.pi + 1) := by
        exact add_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
          (add_nonneg Real.pi_pos.le (by norm_num)))
      have hstep := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrootUpper hinner0) N.scale_pos.le
      have hstep' : N.scale * Real.sqrt (1 + N.epsilon) *
          (|(N.coordinate_inverse z₂).2 -
            (N.coordinate_inverse N.center).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
          N.scale * (1.0005 : ℝ) *
            (|(N.coordinate_inverse z₂).2 -
              (N.coordinate_inverse N.center).2| + Real.sqrt 2 * (Real.pi + 1)) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep
      have hstep'' := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg N.scale_pos.le (by norm_num : (0 : ℝ) ≤ 1.0005))
      have hstep''' : N.scale * (1.0005 : ℝ) *
          (|(N.coordinate_inverse z₂).2 -
            (N.coordinate_inverse N.center).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
          N.scale * (1.0005 : ℝ) * ((0.76 : ℝ) * A + 7.1) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep''
      exact hstep'.trans hstep'''
    have hcostN : intrinsicEDist g U N.center z₂ ≤
        ENNReal.ofReal
          (N.scale * (1.0005 : ℝ) * ((0.76 : ℝ) * A + 7.1)) := by
      apply (intrinsicEDist_mono_of_subset (g := g) hNU).trans
      apply (N.intrinsicEDist_le_axial_add hNcenter hz₂Ncar).trans
      exact ENNReal.ofReal_le_ofReal hrealN
    have hpathUpper : g.pathELength γ tN t₂ ≤
        ENNReal.ofReal
          (N.scale * (1.0005 : ℝ) * ((0.76 : ℝ) * A + 7.1)) := by
      rw [hmin tN t₂ h₁.le (hNP.le.trans h₂.le) le_rfl]
      simpa [hcN, z₂] using hcostN
    have hbad := hpathN₂.trans hpathUpper
    have hscaleProd : (0.999 : ℝ) * N.scale * A ≤ Q.scale * A := by
      have hq := mul_le_mul_of_nonneg_right hscale.1.le hApos.le
      simpa only [mul_assoc] using hq
    have hbad' : (0.99 : ℝ) * N.scale * A +
          (0.3 : ℝ) * Q.scale * A ≤
        N.scale * (1.0005 : ℝ) * ((0.76 : ℝ) * A + 7.1) := by
      have hleft : 0 ≤ (0.99 : ℝ) * N.scale * A +
          (0.3 : ℝ) * Q.scale * A := by
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le)
          (mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) hApos.le)
      have hright : 0 ≤ N.scale * (1.0005 : ℝ) *
          ((0.76 : ℝ) * A + 7.1) := by
        have hpos : 0 ≤ (0.76 : ℝ) * A + 7.1 := by
          have : 0 ≤ (0.76 : ℝ) * A := mul_nonneg (by norm_num) hApos.le
          linarith
        exact mul_nonneg (mul_nonneg N.scale_pos.le (by norm_num)) hpos
      exact (ENNReal.ofReal_le_ofReal_iff hright).mp hbad
    have hSA : 0 < N.scale * A := mul_pos N.scale_pos hApos
    nlinarith only [hbad', hscaleProd, hSA, hA]
  have hrootUpperQ : Real.sqrt (1 + Q.epsilon) ≤ (1.0005 : ℝ) := by
    simpa only [heq] using hrootUpper
  have hconst : Real.sqrt 2 * (Real.pi + 1) ≤ (7.1 : ℝ) := by
    have hs2 : Real.sqrt 2 ≤ (1.415 : ℝ) := by
      have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
      nlinarith [Real.sqrt_nonneg 2]
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    have hmul := mul_le_mul hs2
      (show Real.pi + 1 ≤ (5 : ℝ) by nlinarith [Real.pi_le_four])
      (by positivity) (by positivity)
    nlinarith [hmul]
  have haxial_bound (R : EpsilonNeck g) (hRU : R.carrier ⊆ U)
      (hroot : Real.sqrt (1 + R.epsilon) ≤ (1.0005 : ℝ))
      {x y : M} (hx : x ∈ R.carrier) (hy : y ∈ R.carrier)
      {C : ℝ} (hcoord : |(R.coordinate_inverse y).2 -
        (R.coordinate_inverse x).2| ≤ C * A) :
      intrinsicEDist g U x y ≤
        ENNReal.ofReal (R.scale * (1.0005 : ℝ) * (C * A + 7.1)) := by
    have hsum : |(R.coordinate_inverse y).2 -
          (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1) ≤
        C * A + 7.1 := by
      linarith [hcoord, hconst]
    have hinner0 : 0 ≤ |(R.coordinate_inverse y).2 -
        (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1) := by
      positivity
    have hreal : R.scale * Real.sqrt (1 + R.epsilon) *
          (|(R.coordinate_inverse y).2 -
            (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
        R.scale * (1.0005 : ℝ) * (C * A + 7.1) := by
      have hstep := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hroot hinner0) R.scale_pos.le
      have hstep' : R.scale * Real.sqrt (1 + R.epsilon) *
          (|(R.coordinate_inverse y).2 -
            (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
          R.scale * (1.0005 : ℝ) *
            (|(R.coordinate_inverse y).2 -
              (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1)) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep
      have hstep'' := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg R.scale_pos.le (by norm_num : (0 : ℝ) ≤ 1.0005))
      have hstep''' : R.scale * (1.0005 : ℝ) *
          (|(R.coordinate_inverse y).2 -
            (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
          R.scale * (1.0005 : ℝ) * (C * A + 7.1) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep''
      exact hstep'.trans hstep'''
    apply (intrinsicEDist_mono_of_subset (g := g) hRU).trans
    apply (R.intrinsicEDist_le_axial_add hx hy).trans
    exact ENNReal.ofReal_le_ofReal hreal
  have hdistNP : ENNReal.ofReal ((0.99 : ℝ) * N.scale * A) ≤
      g.pathELength γ tN tP := by
    have hdist := N.balanced_edist_lower_of_not_mem_carrier hε hout
    have hdistA : ENNReal.ofReal ((0.99 : ℝ) * N.scale * A) ≤
        g.edist N.center Q.center := by
      change ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
        g.edist N.center Q.center
      exact hdist
    exact hdistA.trans hcenter_path
  have hanchor₁lower : ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) ≤
      g.pathELength γ t₁ tN := hanchor₁.symm.le
  have hanchor₂lower : ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) ≤
      g.pathELength γ tP t₂ := hanchor₂.symm.le
  intro y hy
  have hyN := hy.1
  have hyQ := hy.2
  have hyNcoord := N.coordinate_inverse_mem y hyN
  have hyQcoord := Q.coordinate_inverse_mem y hyQ
  have hNlower : -(A / 2) < (N.coordinate_inverse y).2 := by
    by_contra hnot
    have hNle : (N.coordinate_inverse y).2 ≤ -(A / 2) := le_of_not_gt hnot
    have hQlower : -(A / 2) ≤ (Q.coordinate_inverse y).2 := by
      by_contra hqnot
      have hQlt : (Q.coordinate_inverse y).2 < -(A / 2) :=
        lt_of_not_ge hqnot
      have hyQrecip : y ∈ Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) := by
        refine ⟨hyQ, ?_, ?_⟩
        · simpa [heq] using hyQcoord.2.1
        · have hQlt' : (Q.coordinate_inverse y).2 < -N.epsilon⁻¹ / 2 := by
            convert hQlt using 1; ring
          exact hQlt'
      have hyNrecip := hrecip hyQrecip
      have hyNrecipLower : -(0.2 : ℝ) * A <
          (N.coordinate_inverse y).2 := by
        simpa [A] using hyNrecip.2.1
      nlinarith only [hyNrecipLower, hNle, hApos]
    have hz₁coord : (N.coordinate_inverse z₁).2 ≤ -(0.292 : ℝ) * A := by
      rw [abs_of_neg hsign₁] at hheight₁
      have hh : (N.coordinate_inverse z₁).2 ≤ -((0.292 : ℝ) * A) := by
        linarith only [hheight₁]
      convert hh using 1; ring
    have hz₂coord : (0.292 : ℝ) * A ≤
        (Q.coordinate_inverse z₂).2 := by
      rw [abs_of_pos hsign₂] at hheight₂
      exact hheight₂
    have hdiffN : |(N.coordinate_inverse y).2 -
        (N.coordinate_inverse z₁).2| ≤ (0.708 : ℝ) * A := by
      rw [abs_le]
      constructor <;> nlinarith only [hyNcoord.2.1, hNle,
        hz₁slab.2.1, hz₁coord, hApos]
    have hdiffQ : |(Q.coordinate_inverse z₂).2 -
        (Q.coordinate_inverse y).2| ≤ (0.81 : ℝ) * A := by
      have hyQupperA : (Q.coordinate_inverse y).2 < A := by
        simpa [A, heq] using hyQcoord.2.2
      rw [abs_le]
      constructor
      · nlinarith only [hyQupperA, hz₂coord, hApos]
      · nlinarith only [hz₂slab.2.2, hQlower, hApos]
    have hcostN := haxial_bound N hNU hrootUpper hz₁N hyN hdiffN
    have hcostQ := haxial_bound Q hQU hrootUpperQ hyQ hz₂Q hdiffQ
    have htriangle := intrinsicEDist_triangle_set (g := g) (U := U)
      (p := z₁) (q := y) (r := z₂)
    have hcomp : intrinsicEDist g U z₁ z₂ ≤
        ENNReal.ofReal (N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1)) +
          ENNReal.ofReal (Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1)) := by
      exact htriangle.trans (add_le_add hcostN hcostQ)
    have hpathUpper : g.pathELength γ t₁ t₂ ≤
        ENNReal.ofReal (N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1)) +
          ENNReal.ofReal (Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1)) := by
      rw [hmin t₁ t₂ le_rfl (h₁.le.trans (hNP.le.trans h₂.le)) le_rfl]
      simpa [z₁, z₂] using hcomp
    have hpathLower : ENNReal.ofReal
          ((0.3 : ℝ) * N.scale * A + (0.99 : ℝ) * N.scale * A +
            (0.3 : ℝ) * Q.scale * A) ≤ g.pathELength γ t₁ t₂ := by
      have ha : 0 ≤ (0.3 : ℝ) * N.scale * A :=
        mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
      have hb : 0 ≤ (0.99 : ℝ) * N.scale * A :=
        mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
      have hc : 0 ≤ (0.3 : ℝ) * Q.scale * A :=
        mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) hApos.le
      rw [ENNReal.ofReal_add (add_nonneg ha hb) hc,
        ENNReal.ofReal_add ha hb]
      calc
        (ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) +
            ENNReal.ofReal ((0.99 : ℝ) * N.scale * A)) +
            ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) ≤
          (g.pathELength γ t₁ tN + g.pathELength γ tN tP) +
            g.pathELength γ tP t₂ := by
          exact add_le_add (add_le_add hanchor₁lower hdistNP) hanchor₂lower
        _ = g.pathELength γ t₁ t₂ := by
          rw [← hadd t₁ tN tP le_rfl h₁.le hNP.le h₂.le,
            ← hadd t₁ tP t₂ le_rfl (h₁.le.trans hNP.le) h₂.le le_rfl]
    have hbad := hpathLower.trans hpathUpper
    have hscaleUpperProd : Q.scale * A ≤ (1.001 : ℝ) * N.scale * A := by
      have hq := mul_le_mul_of_nonneg_right hscale.2.le hApos.le
      nlinarith only [hq]
    have hbad' : (0.3 : ℝ) * N.scale * A + (0.99 : ℝ) * N.scale * A +
          (0.3 : ℝ) * Q.scale * A ≤
        N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) +
          Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) := by
      have hR : 0 ≤ N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) +
          Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) := by
        have hN : 0 ≤ N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) :=
          mul_nonneg (mul_nonneg N.scale_pos.le (by norm_num)) (by nlinarith [hApos])
        have hQ : 0 ≤ Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) :=
          mul_nonneg (mul_nonneg Q.scale_pos.le (by norm_num)) (by nlinarith [hApos])
        exact add_nonneg hN hQ
      have hleft0 : 0 ≤ (0.3 : ℝ) * N.scale * A +
          (0.99 : ℝ) * N.scale * A + (0.3 : ℝ) * Q.scale * A := by
        exact add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le)
            (mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le))
          (mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) hApos.le)
      have hR1 : 0 ≤ N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) := by
        exact mul_nonneg (mul_nonneg N.scale_pos.le (by norm_num)) (by nlinarith [hApos])
      have hR2 : 0 ≤ Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) := by
        exact mul_nonneg (mul_nonneg Q.scale_pos.le (by norm_num)) (by nlinarith [hApos])
      have hbad'' : ENNReal.ofReal
          ((0.3 : ℝ) * N.scale * A + (0.99 : ℝ) * N.scale * A +
            (0.3 : ℝ) * Q.scale * A) ≤ ENNReal.ofReal
          (N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) +
            Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1)) := by
        rw [← ENNReal.ofReal_add hR1 hR2] at hbad
        exact hbad
      exact (ENNReal.ofReal_le_ofReal_iff hR).mp hbad''
    have hNscaleA : (1000 : ℝ) * N.scale ≤ N.scale * A := by
      have h := mul_le_mul_of_nonneg_left hA N.scale_pos.le
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    have hQscaleA : (1000 : ℝ) * Q.scale ≤ Q.scale * A := by
      have h := mul_le_mul_of_nonneg_left (show (1000 : ℝ) ≤ Q.epsilon⁻¹ by
        simpa [heq] using hA) Q.scale_pos.le
      rw [heq] at h
      simpa [A, mul_assoc, mul_left_comm, mul_comm] using h
    have hN71 : (7.1 : ℝ) * N.scale ≤ (0.0071 : ℝ) * N.scale * A := by
      nlinarith only [hNscaleA]
    have hQ71 : (7.1 : ℝ) * Q.scale ≤ (0.0071 : ℝ) * Q.scale * A := by
      nlinarith only [hQscaleA]
    have hNterm : N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) ≤
        (1.0005 : ℝ) * (0.7151 : ℝ) * N.scale * A := by
      nlinarith only [hN71]
    have hQterm : Q.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) ≤
        (1.0005 : ℝ) * (0.8171 : ℝ) * Q.scale * A := by
      nlinarith only [hQ71]
    nlinarith only [hbad', hNterm, hQterm, hscaleUpperProd, N.scale_pos,
      Q.scale_pos, hApos]
  have hQupper : (Q.coordinate_inverse y).2 < A / 2 := by
    by_contra hnot
    have hQge : A / 2 ≤ (Q.coordinate_inverse y).2 := le_of_not_gt hnot
    have hNupper : (N.coordinate_inverse y).2 ≤ A / 2 := by
      by_contra hNnot
      have hNgt : A / 2 < (N.coordinate_inverse y).2 := lt_of_not_ge hNnot
      have hyNpos : y ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
        refine ⟨hyN, ?_, hyNcoord.2.2⟩
        simpa [A] using hNgt
      have hyQpos := hforward hyNpos
      have hQlt : (Q.coordinate_inverse y).2 < A / 2 := by
        simpa [A] using hyQpos.2.2
      exact (not_lt_of_ge hQge) hQlt
    have hz₁coord : (N.coordinate_inverse z₁).2 ≤ -(0.292 : ℝ) * A := by
      rw [abs_of_neg hsign₁] at hheight₁
      have hh : (N.coordinate_inverse z₁).2 ≤ -((0.292 : ℝ) * A) := by
        linarith only [hheight₁]
      convert hh using 1; ring
    have hz₂coord : (0.292 : ℝ) * A ≤
        (Q.coordinate_inverse z₂).2 := by
      rw [abs_of_pos hsign₂] at hheight₂
      exact hheight₂
    have hdiffN : |(N.coordinate_inverse y).2 -
        (N.coordinate_inverse z₁).2| ≤ (0.81 : ℝ) * A := by
      rw [abs_le]
      constructor
      · nlinarith only [hyNcoord.2.1, hNupper, hz₁slab.2.1,
          hz₁coord, hApos]
      · nlinarith only [hyNcoord.2.2, hNupper, hz₁slab.2.1,
          hz₁slab.2.2, hz₁coord, hApos]
    have hdiffQ : |(Q.coordinate_inverse z₂).2 -
        (Q.coordinate_inverse y).2| ≤ (0.708 : ℝ) * A := by
      have hyQupperA : (Q.coordinate_inverse y).2 < A := by
        simpa [A, heq] using hyQcoord.2.2
      rw [abs_le]
      constructor
      · nlinarith only [hyQupperA, hz₂coord, hApos]
      · nlinarith only [hz₂slab.2.2, hQge, hApos]
    have hcostN := haxial_bound N hNU hrootUpper hz₁N hyN hdiffN
    have hcostQ := haxial_bound Q hQU hrootUpperQ hyQ hz₂Q hdiffQ
    have htriangle := intrinsicEDist_triangle_set (g := g) (U := U)
      (p := z₁) (q := y) (r := z₂)
    have hcomp : intrinsicEDist g U z₁ z₂ ≤
        ENNReal.ofReal (N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1)) +
          ENNReal.ofReal (Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1)) := by
      exact htriangle.trans (add_le_add hcostN hcostQ)
    have hpathUpper : g.pathELength γ t₁ t₂ ≤
        ENNReal.ofReal (N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1)) +
          ENNReal.ofReal (Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1)) := by
      rw [hmin t₁ t₂ le_rfl (h₁.le.trans (hNP.le.trans h₂.le)) le_rfl]
      simpa [z₁, z₂] using hcomp
    have hpathLower : ENNReal.ofReal
          ((0.3 : ℝ) * N.scale * A + (0.99 : ℝ) * N.scale * A +
            (0.3 : ℝ) * Q.scale * A) ≤ g.pathELength γ t₁ t₂ := by
      have ha : 0 ≤ (0.3 : ℝ) * N.scale * A := by
        exact mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
      have hb : 0 ≤ (0.99 : ℝ) * N.scale * A := by
        exact mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
      have hc : 0 ≤ (0.3 : ℝ) * Q.scale * A := by
        exact mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) hApos.le
      rw [ENNReal.ofReal_add (add_nonneg ha hb) hc,
        ENNReal.ofReal_add ha hb]
      calc
        (ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) +
            ENNReal.ofReal ((0.99 : ℝ) * N.scale * A)) +
            ENNReal.ofReal ((0.3 : ℝ) * Q.scale * A) ≤
          (g.pathELength γ t₁ tN + g.pathELength γ tN tP) +
            g.pathELength γ tP t₂ := by
          exact add_le_add (add_le_add hanchor₁lower hdistNP) hanchor₂lower
        _ = g.pathELength γ t₁ t₂ := by
          rw [← hadd t₁ tN tP le_rfl h₁.le hNP.le h₂.le,
            ← hadd t₁ tP t₂ le_rfl (h₁.le.trans hNP.le) h₂.le le_rfl]
    have hbad := hpathLower.trans hpathUpper
    have hscaleUpperProd : Q.scale * A ≤ (1.001 : ℝ) * N.scale * A := by
      have hq := mul_le_mul_of_nonneg_right hscale.2.le hApos.le
      nlinarith only [hq]
    have hbad' : (0.3 : ℝ) * N.scale * A + (0.99 : ℝ) * N.scale * A +
          (0.3 : ℝ) * Q.scale * A ≤
        N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) +
          Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) := by
      have hR : 0 ≤ N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) +
          Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) := by
        have hN : 0 ≤ N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) :=
          mul_nonneg (mul_nonneg N.scale_pos.le (by norm_num)) (by nlinarith [hApos])
        have hQ : 0 ≤ Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) :=
          mul_nonneg (mul_nonneg Q.scale_pos.le (by norm_num)) (by nlinarith [hApos])
        exact add_nonneg hN hQ
      have hleft0 : 0 ≤ (0.3 : ℝ) * N.scale * A +
          (0.99 : ℝ) * N.scale * A + (0.3 : ℝ) * Q.scale * A := by
        exact add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le)
            (mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le))
          (mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) hApos.le)
      have hR1 : 0 ≤ N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) := by
        exact mul_nonneg (mul_nonneg N.scale_pos.le (by norm_num)) (by nlinarith [hApos])
      have hR2 : 0 ≤ Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) := by
        exact mul_nonneg (mul_nonneg Q.scale_pos.le (by norm_num)) (by nlinarith [hApos])
      have hbad'' : ENNReal.ofReal
          ((0.3 : ℝ) * N.scale * A + (0.99 : ℝ) * N.scale * A +
            (0.3 : ℝ) * Q.scale * A) ≤ ENNReal.ofReal
          (N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) +
            Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1)) := by
        rw [← ENNReal.ofReal_add hR1 hR2] at hbad
        exact hbad
      exact (ENNReal.ofReal_le_ofReal_iff hR).mp hbad''
    have hNscaleA : (1000 : ℝ) * N.scale ≤ N.scale * A := by
      have h := mul_le_mul_of_nonneg_left hA N.scale_pos.le
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    have hQscaleA : (1000 : ℝ) * Q.scale ≤ Q.scale * A := by
      have h := mul_le_mul_of_nonneg_left (show (1000 : ℝ) ≤ Q.epsilon⁻¹ by
        simpa [heq] using hA) Q.scale_pos.le
      rw [heq] at h
      simpa [A, mul_assoc, mul_left_comm, mul_comm] using h
    have hN71 : (7.1 : ℝ) * N.scale ≤ (0.0071 : ℝ) * N.scale * A := by
      nlinarith only [hNscaleA]
    have hQ71 : (7.1 : ℝ) * Q.scale ≤ (0.0071 : ℝ) * Q.scale * A := by
      nlinarith only [hQscaleA]
    have hNterm : N.scale * (1.0005 : ℝ) * ((0.81 : ℝ) * A + 7.1) ≤
        (1.0005 : ℝ) * (0.8171 : ℝ) * N.scale * A := by
      nlinarith only [hN71]
    have hQterm : Q.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) ≤
        (1.0005 : ℝ) * (0.7151 : ℝ) * Q.scale * A := by
      nlinarith only [hQ71]
    nlinarith only [hbad', hNterm, hQterm, hscaleUpperProd, N.scale_pos,
      Q.scale_pos, hApos]
  have hNlower' : -N.epsilon⁻¹ / 2 < (N.coordinate_inverse y).2 := by
    have h := hNlower
    dsimp [A] at h
    convert h using 1; ring
  have hQlower' : -N.epsilon⁻¹ < (Q.coordinate_inverse y).2 := by
    simpa [A, heq] using hyQcoord.2.1
  have hQupper' : (Q.coordinate_inverse y).2 < N.epsilon⁻¹ / 2 := by
    simpa [A] using hQupper
  exact ⟨⟨hyN, hNlower', hyNcoord.2.2⟩,
    ⟨hyQ, hQlower', hQupper'⟩⟩

end PoincareConjecture.M28
