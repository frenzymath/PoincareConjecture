import PoincareConjecture.Proofs.M47.LimitFiniteNeckDistances
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Triangle










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47



theorem limitFinite_neck_opposite_exits
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (hcomplete : MetricComplete g) (hsec : N.connection.NonnegativeSectionalCurvature)
    (hepsilon : N.epsilon ≤ 1 / 100)
    {gamma sigma : ℝ → M} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hgamma : g.IsGeodesicOn gamma (Icc 0 a))
    (hsigma : g.IsGeodesicOn sigma (Icc 0 b))
    (hgamma0 : gamma 0 = N.center) (hsigma0 : sigma 0 = N.center)
    (hgammaSpeed : ∀ s ∈ Icc 0 a,
      g.tangentNorm (gamma s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma s 1) = 1)
    (hsigmaSpeed : ∀ s ∈ Icc 0 b,
      g.tangentNorm (sigma s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) sigma s 1) = 1)
    (hgammaMin : ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 a,
      g.edist (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    (hsigmaMin : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      g.edist (sigma s) (sigma t) = ENNReal.ofReal |s - t|)
    (hgammaOut : gamma a ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)))
    (hsigmaOut : sigma b ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)))
    (hwide : a ^ 2 + b ^ 2 ≤ (g.edist (gamma a) (sigma b)).toReal ^ 2) :
    ∃ s ∈ Ioc 0 a, ∃ t ∈ Ioc 0 b,
      25 * N.scale ≤ s ∧ 25 * N.scale ≤ t ∧
      MapsTo gamma (Icc 0 s) N.carrier ∧ MapsTo sigma (Icc 0 t) N.carrier ∧
      |(N.coordinate_inverse (gamma s)).2| = N.epsilon⁻¹ / 2 ∧
      |(N.coordinate_inverse (sigma t)).2| = N.epsilon⁻¹ / 2 ∧
      (N.coordinate_inverse (gamma s)).2 * (N.coordinate_inverse (sigma t)).2 < 0 := by
  have hscale := N.scale_pos
  have hcenter := N.central_sphere_subset N.center_on_central_sphere
  have haxis0 := ((N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere).2
  have hquarter : N.epsilon ≤ 1 / 4 := by linarith
  obtain ⟨s, hs, hscarrier, hsheight, _⟩ :=
    N.exists_initial_segment_to_half_neck ha.le hquarter hgamma.contMDiffOn.continuousOn
      (hgamma0.symm ▸ hcenter) (by rw [hgamma0, haxis0]; norm_num) hgammaOut
  obtain ⟨t, ht, htcarrier, htheight, _⟩ :=
    N.exists_initial_segment_to_half_neck hb.le hquarter hsigma.contMDiffOn.continuousOn
      (hsigma0.symm ▸ hcenter) (by rw [hsigma0, haxis0]; norm_num) hsigmaOut
  have hspos := hs.1
  have htpos := ht.1
  have hsubS : Icc 0 s ⊆ Icc 0 a := fun _ hr => ⟨hr.1, hr.2.trans hs.2⟩
  have hsubT : Icc 0 t ⊆ Icc 0 b := fun _ hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hsbound := limitFinite_half_neck_time_lower N hepsilon hs.1.le
    (fun r hr => hgamma r (hsubS hr)) hscarrier
    (fun r hr => hgammaSpeed r (hsubS hr)) hgamma0 hsheight
  have htbound := limitFinite_half_neck_time_lower N hepsilon ht.1.le
    (fun r hr => hsigma r (hsubT hr)) htcarrier
    (fun r hr => hsigmaSpeed r (hsubT hr)) hsigma0 htheight
  have hcompare := g.toponogov_corresponding_side N.connection hcomplete hsec ha hb
    hgamma hsigma hgamma0 hsigma0 hgammaSpeed hsigmaSpeed hgammaMin hsigmaMin
    s ⟨hs.1.le, hs.2⟩ t ⟨ht.1.le, ht.2⟩
  have hquotient : (a ^ 2 + b ^ 2 - (g.edist (gamma a) (sigma b)).toReal ^ 2) /
      (2 * a * b) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hwide) (by positivity)
  have hterm := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 2 * s * t by positivity) hquotient
  have hsum : s ^ 2 + t ^ 2 ≤ (g.edist (gamma s) (sigma t)).toReal ^ 2 := by
    linarith
  have hheights : (N.coordinate_inverse (gamma s)).2 ≠
      (N.coordinate_inverse (sigma t)).2 := by
    intro heq
    have hshort := limitFinite_same_height_distance N
      (hscarrier ⟨hs.1.le, le_rfl⟩) (htcarrier ⟨ht.1.le, le_rfl⟩) heq
    have hsquare := (sq_le_sq₀ (show 0 ≤ 25 * N.scale by positivity) hs.1.le).mpr hsbound
    have htsquare := (sq_le_sq₀ (show 0 ≤ 25 * N.scale by positivity) ht.1.le).mpr htbound
    have hdsquare := (sq_le_sq₀ ENNReal.toReal_nonneg
      (show 0 ≤ 20 * N.scale by positivity)).mpr hshort
    nlinarith [sq_pos_of_pos N.scale_pos]
  refine ⟨s, hs, t, ht, hsbound, htbound, hscarrier, htcarrier, hsheight, htheight, ?_⟩
  rcases abs_eq_abs.mp (hsheight.trans htheight.symm) with heq | heq
  · exact False.elim (hheights heq)
  · have hnonzero : (N.coordinate_inverse (sigma t)).2 ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at htheight
      have hpos : 0 < N.epsilon⁻¹ / 2 := div_pos (inv_pos.mpr N.epsilon_pos) two_pos
      linarith
    rw [heq]
    nlinarith [sq_pos_of_ne_zero hnonzero]

end PoincareConjecture.M47
