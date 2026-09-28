import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

omit [T2Space M] in

theorem axial_displacement_le_pathELength {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 γ)
    (hcarrier : MapsTo γ (Icc a b) N.carrier) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
      |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2|) ≤
      g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let f : M → ℝ := fun x => (N.coordinate_inverse x).2
  let η : ℝ → ℝ := f ∘ γ
  have hf : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f N.carrier :=
    contMDiff_snd.comp_contMDiffOn N.coordinate_inverse_smooth
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 η (Icc a b) :=
    (hf.of_le (by simp)).comp hγ.contMDiffOn hcarrier
  have hdist : EDist.edist (η a) (η b) ≤ Manifold.pathELength 𝓘(ℝ, ℝ) η a b := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ))]
    exact riemannianEDist_le_pathELength hη rfl rfl hab
  have hfactor : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) *
        ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) η t 1‖ₑ ≤
      ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1‖ₑ := by
    have hchain : mvfderiv 𝓘(ℝ, ℝ) η t 1 =
        mvfderiv (𝓡 3) f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) := by
      change mvfderiv 𝓘(ℝ, ℝ) (f ∘ γ) t 1 = _
      rw [mvfderiv_comp t ((hf.contMDiffAt
        (N.carrier_open.mem_nhds (hcarrier ht))).mdifferentiableAt (by simp))
        (hγ.mdifferentiable one_ne_zero t)]
      rfl
    have h := N.axial_mvfderiv_bound (hcarrier ht)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
    change N.scale * Real.sqrt (1 - N.epsilon) *
      |mvfderiv (𝓡 3) f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)| ≤ _ at h
    rw [← hchain] at h
    have he := ENNReal.ofReal_le_ofReal h
    simp only [mvfderiv, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs,
      ENNReal.ofReal_mul hfactor] at he
    rw [← ofReal_norm, ← ofReal_norm, norm_tangentSpace_vectorSpace]
    exact he
  calc
    _ = ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) *
        EDist.edist (η a) (η b) := by
      rw [edist_dist, Real.dist_eq, abs_sub_comm, ← ENNReal.ofReal_mul hfactor]
      rfl
    _ ≤ ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) *
        Manifold.pathELength 𝓘(ℝ, ℝ) η a b := mul_le_mul_right hdist _
    _ = ∫⁻ t in Icc a b, ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) *
        ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) η t 1‖ₑ := by
      rw [pathELength_eq_lintegral_mfderiv_Icc,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ t in Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1‖ₑ :=
      lintegral_mono_ae (ae_restrict_mem measurableSet_Icc |>.mono hpoint)
    _ = g.pathELength γ a b := (pathELength_eq_lintegral_mfderiv_Icc).symm

theorem edist_center_lower_of_not_mem_carrier {x : M} (hx : x ∉ N.carrier) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * N.epsilon⁻¹) ≤
      g.edist N.center x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hε : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hcenter := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
  have hradius (r : ℝ) (hr : r ∈ Ioo 0 N.epsilon⁻¹) :
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) ≤
        g.edist N.center x := by
    by_contra h
    have hdist : Manifold.riemannianEDist (𝓡 3) N.center x <
        ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) := lt_of_not_ge h
    obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hdist (show (0 : ℝ) < 1 by norm_num)
    have hleft : -N.epsilon⁻¹ < -r := neg_lt_neg hr.2
    have hstart : γ 0 ∈ N.region (-r) r := by
      rw [hγ0]
      exact ⟨hcenter.1, hcenter.2 ▸ neg_lt_zero.mpr hr.1, hcenter.2 ▸ hr.1⟩
    have hout : γ 1 ∉ N.coordinate_map '' (univ ×ˢ Icc (-r) r) := by
      rw [hγ1]
      intro hmem
      exact hx ((N.mem_coordinate_slab_iff hleft hr.2).mp hmem).1
    obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
      (show (0 : ℝ) ≤ 1 by norm_num) hleft hr.2 hγ.continuous.continuousOn hstart hout
    have hax := N.axial_displacement_le_pathELength ht.1.le hγ hcarrier
    have hvalue : |(N.coordinate_inverse (γ t)).2 -
        (N.coordinate_inverse (γ 0)).2| = r := by
      rw [hγ0, hcenter.2, sub_zero]
      rcases hboundary with hneg | hpos
      · rw [hneg, abs_neg, abs_of_pos hr.1]
      · rw [hpos, abs_of_pos hr.1]
    rw [hvalue] at hax
    have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    exact (not_lt_of_ge (hax.trans hmono)) hlength
  have hclosed : IsClosed {r : ℝ |
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) ≤ g.edist N.center x} :=
    isClosed_le (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id))
      continuous_const
  have hclosure := hclosed.closure_subset_iff.mpr (show Ioo 0 N.epsilon⁻¹ ⊆
      {r : ℝ | ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) ≤
        g.edist N.center x} from hradius)
  rw [closure_Ioo hε.ne] at hclosure
  exact hclosure ⟨hε.le, le_rfl⟩

theorem balanced_edist_lower_of_not_mem_carrier (hε : N.epsilon ≤ 1 / 1000)
    {x : M} (hx : x ∉ N.carrier) :
    ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤ g.edist N.center x := by
  have hs : (0.99 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  apply (ENNReal.ofReal_le_ofReal ?_).trans (N.edist_center_lower_of_not_mem_carrier hx)
  have hscale := N.scale_pos
  have hinv := inv_pos.mpr N.epsilon_pos
  nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg hscale.le hinv.le)]

end PoincareConjecture.EpsilonNeck
