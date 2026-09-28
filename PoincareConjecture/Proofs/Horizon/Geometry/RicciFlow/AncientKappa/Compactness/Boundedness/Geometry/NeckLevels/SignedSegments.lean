import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Directional.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_minimizing_segment_with_signed_axial_initial_part
    {α W : ℝ} (hα : 0 < α) (hW : 0 ≤ W) :
    ∃ ε₀ > 0, ε₀ ≤ 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
        [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (hc : MetricComplete g) (N : EpsilonNeck g),
        N.epsilon ≤ ε₀ → ∀ {x p : M}, x ∈ N.carrier →
        |(N.coordinate_inverse x).2| ≤ W →
        p ∉ N.coordinate_map '' (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) →
        ∃ (L : ℝ) (γ : ℝ → M), 0 < L ∧ γ 0 = x ∧ γ L = p ∧
          g.IsGeodesicOn γ (Icc 0 L) ∧
          (∀ t ∈ Icc 0 L,
            g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) ∧
          (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
            g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
          ∃ T ∈ Ioc 0 L, N.scale / (100 * N.epsilon) < T ∧
            MapsTo γ (Icc 0 T) N.carrier ∧
            ∃ σ : ℝ, |σ| = 1 ∧
              σ * (N.coordinate_inverse (γ 0)).2 <
                σ * (N.coordinate_inverse (γ T)).2 ∧
              ∀ t ∈ Icc 0 T,
                let a : TangentSpace (𝓡 3) (γ t) := N.scale⁻¹ •
                  mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
                    N.coordinate_map (N.coordinate_inverse (γ t)) (0, 1)
                g.tangentNorm (γ t)
                  (σ • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1 - a) < α := by
  obtain ⟨ε₁, hε₁, haxial⟩ := long_neck_geodesics_are_almost_axial_signed.{u} hα
  let ε₀ := min ε₁ (1 / (4 * (W + 1)))
  have hWpos : 0 < W + 1 := by linarith
  have hquarter : 1 / (4 * (W + 1)) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (W + 1))).mpr
    nlinarith
  refine ⟨ε₀, lt_min hε₁ (by positivity), (min_le_right _ _).trans hquarter, ?_⟩
  intro M _ _ _ _ _ _ _ _ g hc N hN x p hx haxis hp
  have hepspos := N.epsilon_pos
  have hscalepos := N.scale_pos
  have hεW : N.epsilon * (W + 1) ≤ 1 / 4 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (W + 1))).mp
      (hN.trans (min_le_right _ _))
    nlinarith
  have hi : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hWquarter : W < N.epsilon⁻¹ / 4 := by
    rw [inv_eq_one_div, div_div]
    apply (lt_div_iff₀ (by positivity : 0 < N.epsilon * 4)).mpr
    nlinarith [N.epsilon_pos]
  have hxslab : x ∈ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) := by
    apply (N.mem_coordinate_slab_iff (by linarith) (by linarith)).mpr
    exact ⟨hx, by linarith [(abs_le.mp haxis).1], by linarith [(abs_le.mp haxis).2]⟩
  have hxp : x ≠ p := by
    intro heq
    exact hp (heq ▸ hxslab)
  letI := g.toMetricSpace
  let L := (g.edist x p).toReal
  have hL : 0 < L := dist_pos.mpr hxp
  obtain ⟨γ, h0, hLend, hγ, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc x p hL
  have hstart : γ 0 ∈ N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2) := by
    rw [h0]
    exact ⟨hx, by linarith [(abs_le.mp haxis).1], by linarith [(abs_le.mp haxis).2]⟩
  obtain ⟨T, hT, hcarrier, hexit', _⟩ :=
    N.exists_initial_segment_to_slab_boundary hL.le (by linarith) (by linarith)
      hγ.contMDiffOn.continuousOn hstart (by simpa only [L, hLend] using hp)
  have hsub : Icc 0 T ⊆ Icc 0 L := fun _ ht => ⟨ht.1, ht.2.trans hT.2⟩
  have hexit : |(N.coordinate_inverse (γ T)).2| = N.epsilon⁻¹ / 2 := by
    rcases hexit' with he | he
    · rw [he, abs_of_neg (by linarith)]
      ring
    · rw [he, abs_of_pos (by positivity)]
  have hlong : N.scale / (100 * N.epsilon) < T := by
    have hroot : 1 / 2 ≤ Real.sqrt (1 - N.epsilon) := by
      have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
      nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
    have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) := by
      exact mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
    have hdisp := N.axial_displacement_le_of_unit_speed hT.1.le
      (fun t ht => hγ t (hsub ht)) hcarrier (fun t ht => hspeed t (hsub ht))
    have hscaled := (le_inv_mul_iff₀ hfactor).mp hdisp
    have htriangle := abs_sub_abs_le_abs_sub
      (N.coordinate_inverse (γ T)).2 (N.coordinate_inverse (γ 0)).2
    rw [hexit, h0] at htriangle
    have hdiff : 1 / (4 * N.epsilon) ≤
        |(N.coordinate_inverse (γ T)).2 - (N.coordinate_inverse (γ 0)).2| := by
      rw [h0]
      have hid : 1 / (4 * N.epsilon) = N.epsilon⁻¹ / 4 := by ring
      rw [hid]
      linarith
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hroot N.scale_pos.le) hdiff
      (by positivity) (by positivity : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon))
    have heq : (N.scale * (1 / 2)) * (1 / (4 * N.epsilon)) =
        N.scale / (8 * N.epsilon) := by ring
    rw [heq] at hm
    have hlower : N.scale / (8 * N.epsilon) ≤ T := hm.trans hscaled
    exact (div_lt_div_of_pos_left N.scale_pos (by positivity)
      (by nlinarith [N.epsilon_pos])).trans_le hlower
  have hintrinsic : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      s ≤ t → ENNReal.ofReal (t - s) ≤ intrinsicEDist g N.carrier (γ s) (γ t) := by
    intro s hs t ht hst
    have hd := g.edist_le_intrinsicEDist N.carrier (γ s) (γ t)
    rw [hmin s (hsub hs) t (hsub ht), abs_sub_comm s t,
      abs_of_nonneg (sub_nonneg.mpr hst)] at hd
    exact hd
  have hsign : ∃ σ : ℝ, |σ| = 1 ∧
      σ * (N.coordinate_inverse (γ 0)).2 < σ * (N.coordinate_inverse (γ T)).2 := by
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ N.epsilon⁻¹ / 2)).mp hexit with he | he
    · refine ⟨1, by norm_num, ?_⟩
      simp only [one_mul, h0, he]
      linarith [(abs_le.mp haxis).2]
    · refine ⟨-1, by norm_num, ?_⟩
      simp only [neg_one_mul, h0, he]
      linarith [(abs_le.mp haxis).1]
  obtain ⟨σ, hσ, horient⟩ := hsign
  refine ⟨L, γ, hL, h0, hLend, hγ, hspeed, hmin,
    T, hT, hlong, hcarrier, σ, hσ, horient, ?_⟩
  exact haxial N (hN.trans (min_le_left _ _)) hlong
    (fun t ht => hγ t (hsub ht)) (fun t ht => hcarrier ht)
    (fun t ht => hspeed t (hsub ht)) hintrinsic hσ horient

end PoincareConjecture.EpsilonNeck
