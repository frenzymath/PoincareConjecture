import PoincareConjecture.Proofs.M25.AppA_21_Local.CapUniformGain












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture




theorem ConnectedNeckCapCover.exists_uniform_cap_truncation_depth_gain :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (H : ConnectedNeckCapCover g),
      H.epsilon ≤ epsilon0 →
      ∀ (seed : CapCertificate g), seed ∈ H.caps → ∀ (x : M), x ∈ seed.core →
      ∀ (C0 : CapCertificate g), C0 ∈ H.caps → x ∈ C0.core →
      ¬ connectedComponent x ⊆ C0.carrier →
      ∀ (C1 : CapCertificate g), C1 ∈ H.caps →
      (C0.carrier \ C0.end_neck.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆ C1.core) →
      C0.exteriorEDepth x + ENNReal.ofReal
        ((9 / 10) * H.epsilon⁻¹ *
          (H.cap_constant * seed.connection.scalarCurvature x) ^ (-1 / 2 : ℝ)) ≤
        C1.exteriorEDepth x := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hgain⟩ :=
    ConnectedNeckCapCover.exists_uniform_cap_truncation_depth_gain_of_end_neck_overlap.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hH seed hseed x hxseed C0 hC0 hx0 hproper C1 hC1 hcut
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := H.epsilon⁻¹
  let P0 := C0.end_neck.region (L / 2) L
  let D0 := C0.carrier \ P0
  have hxK0 : x ∈ C0.closed_core := by
    rw [C0.core_eq_interior_closed_core] at hx0
    exact interior_subset hx0
  have hxD : x ∈ D0 := by
    rw [C0.closed_core_eq_complement_end] at hxK0
    exact ⟨hxK0.1, fun hxP => hxK0.2 hxP.1⟩
  have hx1 : x ∈ C1.core := hcut hxD
  have hxK1 : x ∈ interior C1.closed_core := by
    rwa [← C1.core_eq_interior_closed_core]
  have hKclosed : IsClosed C1.closed_core := C1.closed_core_compact.isClosed
  by_cases hsub : C0.carrier ⊆ C1.closed_core
  · have hxint : x ∈ interior C0.carrier := by
      rw [C0.carrier_open.interior_eq]
      exact C0.m25_core_subset_carrier hx0
    have hw := C1.exteriorEDepth_add_end_width_le hxint (closure_minimal hsub hKclosed)
    rw [H.cap_epsilon C1 hC1] at hw
    change C0.exteriorEDepth x + ENNReal.ofReal
      (2 * L * C1.end_neck.scale * Real.sqrt (1 - H.epsilon)) ≤
        C1.exteriorEDepth x at hw
    let h0 := (H.cap_constant * seed.connection.scalarCurvature x) ^ (-1 / 2 : ℝ)
    have hscalar : C1.connection.scalarCurvature x = seed.connection.scalarCurvature x := by
      unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
      simp_rw [C1.connection.horizon_curvatureTensor_eq seed.connection x]
    have hscale := C1.end_neck_scale_lower (C1.m25_core_subset_carrier hx1)
      (H.cap_constant_bound C1 hC1)
    rw [hscalar] at hscale
    change h0 ≤ C1.end_neck.scale at hscale
    have hL : 0 < L := inv_pos.mpr H.epsilon_pos
    have hs : (9 / 10 : ℝ) ≤ Real.sqrt (1 - H.epsilon) :=
      Real.le_sqrt_of_sq_le (by nlinarith [hH.trans hcap])
    have hbudget : (9 / 10 : ℝ) * L * h0 ≤
        2 * L * C1.end_neck.scale * Real.sqrt (1 - H.epsilon) := by
      calc
        (9 / 10 : ℝ) * L * h0 ≤ (9 / 10) * L * C1.end_neck.scale :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ ≤ (9 / 5) * L * C1.end_neck.scale :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (9 / 10 : ℝ) ≤ 9 / 5) hL.le)
            C1.end_neck.scale_pos.le
        _ = (2 * L * C1.end_neck.scale) * (9 / 10) := by ring
        _ ≤ 2 * L * C1.end_neck.scale * Real.sqrt (1 - H.epsilon) :=
          mul_le_mul_of_nonneg_left hs
            (mul_nonneg (mul_nonneg (by norm_num) hL.le) C1.end_neck.scale_pos.le)
    exact (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hbudget)).trans hw
  · have hfront : (C0.carrier ∩ frontier C1.closed_core).Nonempty := by
      by_contra hnone
      have hcover : C0.carrier ⊆ interior C1.closed_core ∪ C1.closed_coreᶜ := by
        intro z hz
        by_cases hzK : z ∈ C1.closed_core
        · left
          by_contra hzI
          exact hnone ⟨z, hz, subset_closure hzK, hzI⟩
        · exact Or.inr hzK
      rcases C0.m25_isConnected_carrier.isPreconnected.subset_or_subset
        isOpen_interior hKclosed.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset) hcover with h | h
      · exact hsub (h.trans interior_subset)
      · exact h (C0.m25_core_subset_carrier hx0) (interior_subset hxK1)
    obtain ⟨p, hp0, hpfront⟩ := hfront
    have hpP : p ∈ P0 := by
      by_contra hp
      have hp1 := hcut (show p ∈ D0 from ⟨hp0, hp⟩)
      rw [C1.core_eq_interior_closed_core] at hp1
      exact hpfront.2 hp1
    have hpnew : p ∈ closure C1.end_neck.carrier := by
      rw [C1.core_frontier_eq_boundary, C1.boundary_eq_end_frontier] at hpfront
      exact frontier_subset_closure hpfront.2
    obtain ⟨z, hzP, hznew⟩ := mem_closure_iff.mp hpnew P0
      (C0.end_neck.isOpen_region _ _) hpP
    exact hgain H hH seed hseed x hxseed C0 hC0 hx0 hproper C1 hC1 hcut
      ⟨z, hzP.1, hznew⟩




theorem ConnectedNeckCapCover.exists_singleCap_or_core_cap_without_enlarging_truncation :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (H : ConnectedNeckCapCover g),
      H.epsilon ≤ epsilon0 →
      ∀ (x : M), x ∈ H.X → (∃ C ∈ H.caps, x ∈ C.core) →
      (∃ C ∈ H.caps, ∃ hX : H.X ⊆ C.carrier,
        NeckCapRegionCompatible g H (.singleCap C hX)) ∨
      (∃ C0 ∈ H.caps, x ∈ C0.core ∧
        ∀ C1 ∈ H.caps,
          ¬ (C0.carrier \ C0.end_neck.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆
            C1.core)) := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hgain⟩ :=
    ConnectedNeckCapCover.exists_uniform_cap_truncation_depth_gain.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hH x hx hseed
  obtain ⟨seed, hseed, hxseed⟩ := hseed
  let delta := (9 / 10 : ℝ) * H.epsilon⁻¹ *
    (H.cap_constant * seed.connection.scalarCurvature x) ^ (-1 / 2 : ℝ)
  have hd : 0 < delta := mul_pos
    (mul_pos (by norm_num) (inv_pos.mpr H.epsilon_pos))
    (Real.rpow_pos_of_pos (mul_pos H.cap_constant_pos
      (seed.scalar_pos x (seed.m25_core_subset_carrier hxseed))) _)
  by_cases hsingle : ∃ C ∈ H.caps, H.X ⊆ C.carrier
  · obtain ⟨C, hC, hX⟩ := hsingle
    exact Or.inl ⟨C, hC, hX, H.cap_epsilon C hC, H.cap_constant_bound C hC⟩
  · have hproper : ∀ C ∈ H.caps, x ∈ C.core → ¬ connectedComponent x ⊆ C.carrier := by
      intro C hC _ hK
      exact hsingle ⟨C, hC, (H.connected_X.subset_connectedComponent hx).trans hK⟩
    obtain ⟨C0, hC0, hx0, hfinite, hmax⟩ :=
      H.exists_core_cap_exteriorEDepth_near_max ⟨seed, hseed, hxseed⟩ hproper hd
    refine Or.inr ⟨C0, hC0, hx0, ?_⟩
    intro C1 hC1 hcut
    have hxK0 : x ∈ C0.closed_core := by
      rw [C0.core_eq_interior_closed_core] at hx0
      exact interior_subset hx0
    have hxD : x ∈ C0.carrier \
        C0.end_neck.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ := by
      rw [C0.closed_core_eq_complement_end] at hxK0
      exact ⟨hxK0.1, fun hxP => hxK0.2 hxP.1⟩
    have hx1 : x ∈ C1.core := hcut hxD
    have hg := hgain H hH seed hseed x hxseed C0 hC0 hx0
      (hproper C0 hC0 hx0) C1 hC1 hcut
    change C0.exteriorEDepth x + ENNReal.ofReal delta ≤ C1.exteriorEDepth x at hg
    have hr := ENNReal.toReal_mono (hfinite C1 hC1 hx1).2.ne hg
    rw [ENNReal.toReal_add (hfinite C0 hC0 hx0).2.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hd.le] at hr
    exact (not_lt_of_ge hr) (hmax C1 hC1 hx1)

end PoincareConjecture
