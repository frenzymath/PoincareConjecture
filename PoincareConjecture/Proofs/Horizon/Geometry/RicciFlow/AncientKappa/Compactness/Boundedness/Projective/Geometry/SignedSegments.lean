import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.Segments

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CylinderCover

theorem exists_minimizing_segment_with_signed_axial_initial_direction
    {α W : ℝ} (hα : 0 < α) (hW : 0 ≤ W) :
    ∃ ε₀ > 0, ε₀ ≤ 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
        [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g) (_hc : MetricComplete g)
        (f : RoundCylinderSpace → M) {ε r : ℝ}, 0 < ε → 0 < r → ε ≤ ε₀ →
        IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
          (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) →
        RoundCylinderClose ε 0
          (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w) →
        ∀ {a : M → ℝ},
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) →
        (∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, a (f z) = z.2) →
        ∀ {z : RoundCylinderSpace} {p : M}, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ → |z.2| ≤ W →
        p ∉ f '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2)) →
        ∃ (L : ℝ) (γ : ℝ → M), 0 < L ∧ γ 0 = f z ∧ γ L = p ∧
          g.IsGeodesicOn γ (Icc 0 L) ∧
          (∀ t ∈ Icc 0 L,
            g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) ∧
          (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
            g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
          ∃ σ : ℝ, |σ| = 1 ∧
            g.tangentNorm (f z)
              (σ • (show TangentSpace (𝓡 3) (f z) from
                  mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) -
                r⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z (0, 1)) < α := by
  obtain ⟨ε₁, hε₁, hε₁half, haxial⟩ := long_geodesics_are_almost_axial_signed.{u} hα
  let ε₀ := min ε₁ (1 / (4 * (W + 1)))
  have hWpos : 0 < W + 1 := by linarith
  have hquarter : 1 / (4 * (W + 1)) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (W + 1))).mpr
    nlinarith
  refine ⟨ε₀, lt_min hε₁ (by positivity), (min_le_right _ _).trans hquarter, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D hc f ε r hε hr hεsmall hf hclose a ha hvalue z p hz haxis hp
  have hεhalf : ε < 1 / 2 := (hεsmall.trans (min_le_left _ _)).trans_lt hε₁half
  have hεW : ε * (W + 1) ≤ 1 / 4 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (W + 1))).mp
      (hεsmall.trans (min_le_right _ _))
    nlinarith
  have hi : 0 < ε⁻¹ := inv_pos.mpr hε
  have hWquarter : W < ε⁻¹ / 4 := by
    rw [inv_eq_one_div, div_div]
    apply (lt_div_iff₀ (by positivity : 0 < ε * 4)).mpr
    nlinarith
  have hxslab : f z ∈ f '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2)) :=
    ⟨z, ⟨mem_univ _, by linarith [(abs_le.mp haxis).1],
      by linarith [(abs_le.mp haxis).2]⟩, rfl⟩
  have hxp : f z ≠ p := fun heq => hp (heq ▸ hxslab)
  let := g.toMetricSpace
  let L := (g.edist (f z) p).toReal
  have hL : 0 < L := dist_pos.mpr hxp
  obtain ⟨γ, h0, hLend, hγ, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc (f z) p hL
  have hstart : γ 0 ∈ f '' (univ ×ˢ Ioo (-ε⁻¹ / 2) (ε⁻¹ / 2)) := by
    rw [h0]
    exact ⟨z, ⟨mem_univ _, by linarith [(abs_le.mp haxis).1],
      by linarith [(abs_le.mp haxis).2]⟩, rfl⟩
  obtain ⟨T, hT, hcarrier, hexit⟩ := exists_initial_segment_to_half_slab
    hε hf hvalue hL.le hγ.contMDiffOn.continuousOn hstart
    (by simpa only [L, hLend] using hp)
  have hsub : Icc 0 T ⊆ Icc 0 L := fun _ ht => ⟨ht.1, ht.2.trans hT.2⟩
  have hlong : r / (100 * ε) < T := by
    have hdisp := axial_displacement_le_of_unit_speed g hε hεhalf hr hf hclose ha hvalue
      hT.1.le (fun t ht => hγ t (hsub ht)) hcarrier (fun t ht => hspeed t (hsub ht))
    have htriangle := abs_sub_abs_le_abs_sub (a (γ T)) (a (γ 0))
    rw [hexit, h0, hvalue z ⟨mem_univ _, hz⟩] at htriangle
    have hdiff : 1 / (4 * ε) ≤ |a (γ T) - a (γ 0)| := by
      rw [h0, hvalue z ⟨mem_univ _, hz⟩]
      have hid : 1 / (4 * ε) = ε⁻¹ / 4 := by ring
      rw [hid]
      linarith
    have hscaled := mul_le_mul_of_nonneg_left (hdiff.trans hdisp) hr.le
    have hcancel : r * (2 / r * T) = 2 * T := by field_simp
    rw [hcancel] at hscaled
    have hlower : r / (8 * ε) ≤ T := by
      have heq : r / (8 * ε) = (r * (1 / (4 * ε))) / 2 := by ring
      rw [heq]
      linarith
    exact (div_lt_div_of_pos_left hr (by positivity) (by nlinarith)).trans_le hlower
  have hintrinsic : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      s ≤ t → ENNReal.ofReal (t - s) ≤
        intrinsicEDist g (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) (γ s) (γ t) := by
    intro s hs t ht hst
    have hd := g.edist_le_intrinsicEDist (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) (γ s) (γ t)
    rw [hmin s (hsub hs) t (hsub ht), abs_sub_comm s t,
      abs_of_nonneg (sub_nonneg.mpr hst)] at hd
    exact hd
  have hsign : ∃ σ : ℝ, |σ| = 1 ∧ σ * a (γ 0) < σ * a (γ T) := by
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ ε⁻¹ / 2)).mp hexit with he | he
    · refine ⟨1, by norm_num, ?_⟩
      simp only [one_mul, h0, hvalue z ⟨mem_univ _, hz⟩, he]
      linarith [(abs_le.mp haxis).2]
    · refine ⟨-1, by norm_num, ?_⟩
      simp only [neg_one_mul, h0, hvalue z ⟨mem_univ _, hz⟩, he]
      linarith [(abs_le.mp haxis).1]
  obtain ⟨σ, hσ, horient⟩ := hsign
  refine ⟨L, γ, hL, h0, hLend, hγ, hspeed, hmin, σ, hσ, ?_⟩
  have hh := haxial g D f hε (hεsmall.trans (min_le_left _ _)) hr hf hclose a ha hvalue
    hlong (fun t ht => hγ t (hsub ht)) (fun t ht => hcarrier ht)
    (fun t ht => hspeed t (hsub ht)) hintrinsic hσ horient
    0 ⟨le_rfl, hT.1.le⟩ z ⟨mem_univ _, hz⟩ h0.symm
  rwa [h0] at hh

end PoincareConjecture.CylinderCover
