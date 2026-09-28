import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlBarrier
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlBalls
import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound
import PoincareConjecture.Proofs.M34.Mathlib.CompactPartialImage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {m : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [IsManifold (𝓡 m) ∞ X]
  [T3Space X] {g : RiemannianMetric 3 M} (N : CapCertificate g)





theorem ball_subset_image_recutCarrier_of_tangentNorm_le
    (h : RiemannianMetric m X) (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 3) 1 e.symm e.target)
    {c d b A r : ℝ} (hc : -N.epsilon⁻¹ < c) (hcd : c < d) (hdb : d < b)
    (hb : b < N.epsilon⁻¹) (hA : 0 < A)
    (hcapture : closure (N.recutCarrier b) ⊆ e.source)
    (hbound : ∀ x ∈ closure (N.recutCarrier b), ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ A * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 m) e x v))
    (hshort : (2 / N.end_neck.scale) * A * r ≤ b - d)
    {o : M} (ho : o ∈ N.closed_core) :
    h.ball (e o) r ⊆ e '' N.recutCarrier b := by
  have hb0 := hc.trans (hcd.trans hdb)
  have hK := N.recutCarrier_compact_closure hb0 hb
  have hsource : N.recutCarrier b ⊆ e.source := subset_closure.trans hcapture
  have hoW : o ∈ N.recutCarrier b := Or.inl ho
  have himage := e.isImage_image_of_subset_source hsource
  have hopen := e.isOpen_image_of_subset_source (N.recutCarrier_isOpen hb0 hb) hsource
  intro z hz
  by_contra hzout
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ := h.exists_short_path_in_ball (e o) z hz
  obtain ⟨t, ht, hfront, hbefore⟩ := hγ.continuousOn.exists_first_exit_open zero_le_one
    hopen (hγ0.symm ▸ mem_image_of_mem e hoW) (hγ1.symm ▸ hzout)
  have hcl : MapsTo γ (Icc (0 : ℝ) t) (closure (e '' N.recutCarrier b)) := by
    intro u hu
    rcases hu.2.eq_or_lt with he | he
    · subst u
      exact frontier_subset_closure hfront
    · exact subset_closure (hbefore u ⟨hu.1, he⟩)
  have htarget : MapsTo γ (Icc (0 : ℝ) t) e.target := fun u hu =>
    e.closure_image_subset_target_of_isCompact hK.1 hcapture (hcl hu)
  let η : ℝ → M := e.symm ∘ γ
  have hηK : MapsTo η (Icc (0 : ℝ) t) (closure (N.recutCarrier b)) := fun u hu =>
    (himage.closure.symm_apply_mem_iff (htarget hu)).mpr (hcl hu)
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc (0 : ℝ) t) :=
    hi.comp (hγ.mono (Icc_subset_Icc_right ht.2)) htarget
  have hη0 : η 0 = o := by
    change e.symm (γ 0) = o
    rw [hγ0, e.left_inv (hsource hoW)]
  have hηt : η t ∈ frontier (N.recutCarrier b) :=
    (himage.frontier.symm_apply_mem_iff (htarget ⟨ht.1.le, le_rfl⟩)).mpr hfront
  have hbarrier := N.collar_height_le_pathELength hc hcd hdb hb ht.1.le hη
    (fun u hu => hK.2 (hηK hu)) (hη0.symm ▸ ho) hηt
  have hlength : g.pathELength η 0 t ≤ ENNReal.ofReal A * h.pathELength γ 0 t := by
    apply g.pathELength_le_mul_of_speed_le h η γ 0 t hA.le
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) t := ⟨hu.1.le, hu.2.le⟩
    have hiu := ((hi (γ u) (htarget hu')).contMDiffAt
      (e.open_target.mem_nhds (htarget hu'))).mdifferentiableAt (by simp)
    have hγu := ((hγ u ⟨hu.1.le, hu.2.le.trans ht.2⟩).contMDiffAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2))).mdifferentiableAt (by simp)
    change g.tangentNorm (η u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (e.symm ∘ γ) u 1) ≤ _
    rw [mfderiv_comp_apply u hiu hγu]
    exact g.inverse_tangentNorm_le_of_forward_lower_bound h e hf hi (htarget hu')
      (hbound (η u) (hηK hu')) _
  have hmono : h.pathELength γ 0 t ≤ h.pathELength γ 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : X → Type _) :=
      ⟨h.toRiemannianMetric⟩
    exact Manifold.pathELength_mono le_rfl ht.2
  have hunit : 0 < 2 / N.end_neck.scale := div_pos (by norm_num) N.end_neck.scale_pos
  have hcoef : 0 < (2 / N.end_neck.scale) * A := mul_pos hunit hA
  have hstrict : ENNReal.ofReal (2 / N.end_neck.scale) *
      (ENNReal.ofReal A * h.pathELength γ 0 1) < ENNReal.ofReal (b - d) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hunit.le]
    calc
      _ < ENNReal.ofReal ((2 / N.end_neck.scale) * A) * ENNReal.ofReal r :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hcoef).ne'
          ENNReal.ofReal_ne_top hlen
      _ = ENNReal.ofReal ((2 / N.end_neck.scale) * A * r) :=
        (ENNReal.ofReal_mul hcoef.le).symm
      _ ≤ ENNReal.ofReal (b - d) := ENNReal.ofReal_le_ofReal hshort
  have hweak := hbarrier.trans (mul_le_mul' le_rfl
    (hlength.trans (mul_le_mul' le_rfl hmono)))
  exact not_lt_of_ge hweak hstrict

end PoincareConjecture.CapCertificate
