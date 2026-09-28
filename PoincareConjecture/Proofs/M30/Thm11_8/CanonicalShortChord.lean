import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ray













set_option autoImplicit false

open Set
open Poincare.Riemannian.Soul
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M30

private theorem match_minimizing_exit_times
    {M : Type u} [MetricSpace M] {gamma sigma : ℝ → M} {a b s t r K : ℝ}
    (hgamma : IsMinimizingOn gamma (Icc 0 a))
    (hsigma : IsMinimizingOn sigma (Icc 0 b))
    (hbase : gamma 0 = sigma 0) (hs : s ∈ Ioc 0 a) (ht : t ∈ Ioc 0 b)
    (hrs : r ≤ s) (hrt : r ≤ t) (hnear : dist (gamma s) (sigma t) ≤ K) :
    ∃ ell : ℝ, 0 < ell ∧ ell ≤ a ∧ ell ≤ b ∧ r ≤ ell ∧
      dist (gamma ell) (sigma ell) ≤ 2 * K := by
  have hsI : s ∈ Icc 0 a := ⟨hs.1.le, hs.2⟩
  have htI : t ∈ Icc 0 b := ⟨ht.1.le, ht.2⟩
  have hgs : dist (gamma s) (gamma 0) = s := by
    rw [hgamma hsI ⟨le_rfl, hs.1.le.trans hs.2⟩, sub_zero, abs_of_pos hs.1]
  have hst : dist (sigma t) (gamma 0) = t := by
    rw [hbase, hsigma htI ⟨le_rfl, ht.1.le.trans ht.2⟩,
      sub_zero, abs_of_pos ht.1]
  rcases le_total s t with hle | hle
  · refine ⟨s, hs.1, hs.2, hle.trans ht.2, hrs, ?_⟩
    have hgap := dist_triangle (sigma t) (gamma s) (gamma 0)
    rw [hst, hgs, dist_comm (sigma t) (gamma s)] at hgap
    have hmatch := dist_triangle (gamma s) (sigma t) (sigma s)
    rw [hsigma htI ⟨hs.1.le, hle.trans ht.2⟩,
      abs_of_nonneg (sub_nonneg.mpr hle)] at hmatch
    linarith
  · refine ⟨t, ht.1, hle.trans hs.2, ht.2, hrt, ?_⟩
    have hgap := dist_triangle (gamma s) (sigma t) (gamma 0)
    rw [hgs, hst] at hgap
    have hmatch := dist_triangle (gamma t) (gamma s) (sigma t)
    rw [hgamma ⟨ht.1.le, hle.trans hs.2⟩ hsI,
      abs_of_nonpos (sub_nonpos.mpr hle)] at hmatch
    linarith

private theorem half_axis_sign {epsilon z : ℝ} (hepsilon : 0 < epsilon)
    (haxis : |z| = epsilon⁻¹ / 2) :
    ∃ sign : ℝ, |sign| = 1 ∧ z = sign / (2 * epsilon) := by
  rcases eq_or_eq_neg_of_abs_eq haxis with h | h
  · refine ⟨1, by norm_num, ?_⟩
    rw [h]
    field_simp [ne_of_gt hepsilon]
  · refine ⟨-1, by norm_num, ?_⟩
    rw [h]
    field_simp [ne_of_gt hepsilon]

section Neck

variable {M : Type u} [MetricSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]

private theorem half_neck_radial_bound
    (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hepsilon : N.epsilon ≤ 1 / 4) {x y : M} (hx : x ∈ N.carrier)
    (haxis : |(N.coordinate_inverse x).2| = N.epsilon⁻¹ / 2)
    (hy : y ∈ N.central_sphere) :
    N.scale / (2 * neckDepthConstant * N.epsilon) ≤ dist x y := by
  obtain ⟨sign, hsign, haxis'⟩ := half_axis_sign N.epsilon_pos haxis
  have hdepth := N.half_neck_depth_lower_bound hx hsign haxis' hy
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  rw [hdist]
  calc
    N.scale / (2 * neckDepthConstant * N.epsilon) =
        (N.scale * (1 / 2)) / (neckDepthConstant * N.epsilon) := by ring
    _ ≤ N.scale * Real.sqrt (1 - N.epsilon) /
        (neckDepthConstant * N.epsilon) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot N.scale_pos.le)
        (mul_pos neckDepthConstant_pos N.epsilon_pos).le
    _ ≤ _ := hdepth

omit [ConnectedSpace M] in
private theorem same_neck_slice_distance_bound
    (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier)
    (haxis : (N.coordinate_inverse x).2 = (N.coordinate_inverse y).2) :
    dist x y ≤ (2 * Real.pi) * N.scale := by
  have h := N.edist_coordinate_map_slice_le
    (N.coordinate_inverse x).1 (N.coordinate_inverse y).1
    (N.coordinate_inverse_mem x hx).2
  have hxmap : N.coordinate_map
      ((N.coordinate_inverse x).1, (N.coordinate_inverse x).2) = x :=
    N.coordinate_map_coordinate_inverse hx
  have hymap : N.coordinate_map
      ((N.coordinate_inverse y).1, (N.coordinate_inverse x).2) = y := by
    rw [haxis]
    exact N.coordinate_map_coordinate_inverse hy
  rw [hxmap, hymap] at h
  have hs : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + N.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + N.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [N.epsilon_lt_half, mul_nonneg (Real.sqrt_nonneg (1 + N.epsilon))
      (Real.sqrt_nonneg 2)]
  have hupper : N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi ≤
      (2 * Real.pi) * N.scale := by
    have hm := mul_le_mul_of_nonneg_left hs N.scale_pos.le
    nlinarith [mul_le_mul_of_nonneg_right hm Real.pi_pos.le]
  rw [hdist]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) N.scale_pos.le)
    (h.trans (ENNReal.ofReal_le_ofReal hupper))

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem relative_neck_chord_bound
    (g : RiemannianMetric 3 M) (N : EpsilonNeck g) {x y : M} {ell : ℝ}
    (hdepth : N.scale / (2 * neckDepthConstant * N.epsilon) ≤ ell)
    (hchord : dist x y ≤ (4 * Real.pi) * N.scale) :
    dist x y ≤ (8 * Real.pi * neckDepthConstant * N.epsilon) * ell := by
  have hscale := (div_le_iff₀ (show 0 <
    2 * neckDepthConstant * N.epsilon from
    mul_pos (mul_pos (by norm_num) neckDepthConstant_pos) N.epsilon_pos)).mp hdepth
  calc
    dist x y ≤ (4 * Real.pi) * N.scale := hchord
    _ ≤ (4 * Real.pi) * (ell * (2 * neckDepthConstant * N.epsilon)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring



theorem exists_equal_radius_short_chord_of_neck_side
    (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hepsilon : N.epsilon ≤ 1 / 4)
    (hsmall : N.epsilon ≤
      1 / (4 * neckDepthConstant * (2 * Real.pi + 2)))
    {A : Set M} (hA : IsOpen A)
    (hfront : frontier A = N.central_sphere)
    (hhalf : N.region (-N.epsilon⁻¹) 0 ⊆ A ∨
      N.region 0 N.epsilon⁻¹ ⊆ A)
    {gamma sigma : ℝ → M} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hgamma : IsMinimizingOn gamma (Icc 0 a))
    (hsigma : IsMinimizingOn sigma (Icc 0 b))
    (hgamma0 : gamma 0 = N.center)
    (hsigma0 : sigma 0 = N.center)
    (hgammaA : gamma a ∉ A) (hsigmaA : sigma b ∉ A)
    (hgammaOut : gamma a ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)))
    (hsigmaOut : sigma b ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))) :
    ∃ ell : ℝ, 0 < ell ∧ ell ≤ a ∧ ell ≤ b ∧
      N.scale / (2 * neckDepthConstant * N.epsilon) ≤ ell ∧
      dist (gamma ell) (sigma ell) ≤ (4 * Real.pi) * N.scale ∧
      dist (gamma ell) (sigma ell) ≤
        (8 * Real.pi * neckDepthConstant * N.epsilon) * ell := by
  have hcenter := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
  have hgammaStart : gamma 0 ∈ N.carrier := by simpa only [hgamma0] using hcenter.1
  have hsigmaStart : sigma 0 ∈ N.carrier := by simpa only [hsigma0] using hcenter.1
  have hgammaAxis : |(N.coordinate_inverse (gamma 0)).2| ≤ 1 := by
    rw [hgamma0, hcenter.2]
    norm_num
  have hsigmaAxis : |(N.coordinate_inverse (sigma 0)).2| ≤ 1 := by
    rw [hsigma0, hcenter.2]
    norm_num
  obtain ⟨s, hs, hgs, haxisS, _⟩ := N.exists_initial_segment_to_half_neck
    ha.le hepsilon hgamma.continuousOn hgammaStart hgammaAxis hgammaOut
  obtain ⟨t, ht, hst, haxisT, _⟩ := N.exists_initial_segment_to_half_neck
    hb.le hepsilon hsigma.continuousOn hsigmaStart hsigmaAxis hsigmaOut
  have hsMem := hgs ⟨hs.1.le, le_rfl⟩
  have htMem := hst ⟨ht.1.le, le_rfl⟩
  obtain ⟨signS, hsignS, hsignAxisS⟩ := half_axis_sign N.epsilon_pos haxisS
  obtain ⟨signT, hsignT, hsignAxisT⟩ := half_axis_sign N.epsilon_pos haxisT
  have hsOut := N.minimizing_half_neck_not_mem_compact_side hdist hsmall hA hfront
    hgamma hgammaA hgammaStart hgammaAxis ⟨hs.1.le, hs.2⟩ hsMem hsignS hsignAxisS
  have htOut := N.minimizing_half_neck_not_mem_compact_side hdist hsmall hA hfront
    hsigma hsigmaA hsigmaStart hsigmaAxis ⟨ht.1.le, ht.2⟩ htMem hsignT hsignAxisT
  have hsame : (N.coordinate_inverse (gamma s)).2 =
      (N.coordinate_inverse (sigma t)).2 := by
    rcases hhalf with hneg | hpos
    · have hsNonneg : 0 ≤ (N.coordinate_inverse (gamma s)).2 := by
        by_contra h
        exact hsOut (hneg ⟨hsMem, (N.coordinate_inverse_mem _ hsMem).2.1,
          lt_of_not_ge h⟩)
      have htNonneg : 0 ≤ (N.coordinate_inverse (sigma t)).2 := by
        by_contra h
        exact htOut (hneg ⟨htMem, (N.coordinate_inverse_mem _ htMem).2.1,
          lt_of_not_ge h⟩)
      rw [abs_of_nonneg hsNonneg] at haxisS
      rw [abs_of_nonneg htNonneg] at haxisT
      exact haxisS.trans haxisT.symm
    · have hsNonpos : (N.coordinate_inverse (gamma s)).2 ≤ 0 := by
        by_contra h
        exact hsOut (hpos ⟨hsMem, lt_of_not_ge h,
          (N.coordinate_inverse_mem _ hsMem).2.2⟩)
      have htNonpos : (N.coordinate_inverse (sigma t)).2 ≤ 0 := by
        by_contra h
        exact htOut (hpos ⟨htMem, lt_of_not_ge h,
          (N.coordinate_inverse_mem _ htMem).2.2⟩)
      rw [abs_of_nonpos hsNonpos] at haxisS
      rw [abs_of_nonpos htNonpos] at haxisT
      linarith
  have hsDepth : N.scale / (2 * neckDepthConstant * N.epsilon) ≤ s := by
    have h := half_neck_radial_bound g N hdist hepsilon hsMem haxisS
      N.center_on_central_sphere
    rw [← hgamma0, hgamma ⟨hs.1.le, hs.2⟩ ⟨le_rfl, ha.le⟩,
      sub_zero, abs_of_pos hs.1] at h
    exact h
  have htDepth : N.scale / (2 * neckDepthConstant * N.epsilon) ≤ t := by
    have h := half_neck_radial_bound g N hdist hepsilon htMem haxisT
      N.center_on_central_sphere
    rw [← hsigma0, hsigma ⟨ht.1.le, ht.2⟩ ⟨le_rfl, hb.le⟩,
      sub_zero, abs_of_pos ht.1] at h
    exact h
  obtain ⟨ell, hell, hellA, hellB, hdepth, hchord⟩ := match_minimizing_exit_times
    hgamma hsigma (hgamma0.trans hsigma0.symm) hs ht hsDepth htDepth
    (same_neck_slice_distance_bound g N hdist hsMem htMem hsame)
  have hchord' : dist (gamma ell) (sigma ell) ≤ (4 * Real.pi) * N.scale := by
    nlinarith [hchord]
  exact ⟨ell, hell, hellA, hellB, hdepth, hchord',
    relative_neck_chord_bound g N hdepth hchord'⟩

omit [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] in
private theorem exists_positive_frontier_time
    {gamma : ℝ → M} {a : ℝ} (ha : 0 < a)
    (hgamma : ContinuousOn gamma (Icc 0 a))
    {W : Set M} (hW : IsOpen W) (hstart : gamma 0 ∈ W) (hout : gamma a ∉ W) :
    ∃ s ∈ Ioc 0 a, gamma s ∈ frontier W := by
  have hhit : ∃ s ∈ Icc 0 a, gamma s ∈ frontier W := by
    by_contra h
    push Not at h
    have hdisj : Disjoint (gamma '' Icc 0 a) (frontier W) := by
      apply disjoint_left.mpr
      rintro y ⟨s, hs, rfl⟩ hy
      exact h s hs hy
    have hsub := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      (isPreconnected_Icc.image gamma hgamma) hdisj
      ⟨gamma 0, ⟨0, ⟨le_rfl, ha.le⟩, rfl⟩, hW.interior_eq.symm ▸ hstart⟩
    exact hout (interior_subset (hsub ⟨a, ⟨ha.le, le_rfl⟩, rfl⟩))
  obtain ⟨s, hs, hfront⟩ := hhit
  refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, hs.2⟩, hfront⟩
  intro hzero
  subst s
  exact hfront.2 (hW.interior_eq.symm ▸ hstart)

private theorem cap_frontier_time_depth
    (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hepsilon : N.epsilon ≤ 1 / 4)
    {W : Set M} (hW : IsOpen W) (hfront : frontier W = N.central_sphere)
    {y : M} (hy : y ∈ W) (hyNeck : y ∉ N.carrier)
    {gamma : ℝ → M} {a : ℝ} (ha : 0 < a)
    (hgamma : IsMinimizingOn gamma (Icc 0 a)) (hgamma0 : gamma 0 = y)
    (hout : gamma a ∉ W) :
    ∃ s ∈ Ioc 0 a, gamma s ∈ N.central_sphere ∧
      N.scale / (2 * neckDepthConstant * N.epsilon) ≤ s := by
  obtain ⟨s, hs, hsFront⟩ := exists_positive_frontier_time ha hgamma.continuousOn hW
    (by simpa only [hgamma0] using hy) hout
  have hsCentral : gamma s ∈ N.central_sphere := hfront ▸ hsFront
  let beta : ℝ → M := fun v => gamma (s - v)
  have hbeta : ContinuousOn beta (Icc 0 s) :=
    hgamma.continuousOn.comp (continuous_const.sub continuous_id).continuousOn
      (fun v hv => ⟨by linarith [hv.2], by linarith [hv.1, hs.2]⟩)
  have hbeta0 : beta 0 = gamma s := by simp [beta]
  have hbetas : beta s = y := by simp [beta, hgamma0]
  have hcentral := (N.mem_central_sphere_iff (gamma s)).mp hsCentral
  have hstart : beta 0 ∈ N.carrier := by simpa only [hbeta0] using hcentral.1
  have haxis : |(N.coordinate_inverse (beta 0)).2| ≤ 1 := by
    rw [hbeta0, hcentral.2]
    norm_num
  have hi : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hbetaOut : beta s ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) := by
    intro h
    have hmem := ((N.mem_coordinate_slab_iff (by linarith) (by linarith)).mp h).1
    exact hyNeck (hbetas ▸ hmem)
  obtain ⟨v, hv, hcarrier, haxisV, _⟩ := N.exists_initial_segment_to_half_neck
    hs.1.le hepsilon hbeta hstart haxis hbetaOut
  have hdepth := half_neck_radial_bound g N hdist hepsilon
    (hcarrier ⟨hv.1.le, le_rfl⟩) haxisV hsCentral
  have hradial : dist (beta v) (gamma s) = v := by
    dsimp only [beta]
    rw [hgamma ⟨by linarith [hv.2], by linarith [hv.1, hs.2]⟩
      ⟨hs.1.le, hs.2⟩, show s - v - s = -v by ring,
      abs_neg, abs_of_pos hv.1]
  rw [hradial] at hdepth
  exact ⟨s, hs, hsCentral, hdepth.trans hv.2⟩



theorem exists_equal_radius_short_chord_of_cap_side
    (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hepsilon : N.epsilon ≤ 1 / 4)
    {W : Set M} (hW : IsOpen W)
    (hfront : frontier W = N.central_sphere)
    {y : M} (hy : y ∈ W) (hyNeck : y ∉ N.carrier)
    {gamma sigma : ℝ → M} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hgamma : IsMinimizingOn gamma (Icc 0 a))
    (hsigma : IsMinimizingOn sigma (Icc 0 b))
    (hgamma0 : gamma 0 = y) (hsigma0 : sigma 0 = y)
    (hgammaOut : gamma a ∉ W) (hsigmaOut : sigma b ∉ W) :
    ∃ ell : ℝ, 0 < ell ∧ ell ≤ a ∧ ell ≤ b ∧
      N.scale / (2 * neckDepthConstant * N.epsilon) ≤ ell ∧
      dist (gamma ell) (sigma ell) ≤ (4 * Real.pi) * N.scale ∧
      dist (gamma ell) (sigma ell) ≤
        (8 * Real.pi * neckDepthConstant * N.epsilon) * ell := by
  obtain ⟨s, hs, hsCentral, hsDepth⟩ := cap_frontier_time_depth g N hdist hepsilon
    hW hfront hy hyNeck ha hgamma hgamma0 hgammaOut
  obtain ⟨t, ht, htCentral, htDepth⟩ := cap_frontier_time_depth g N hdist hepsilon
    hW hfront hy hyNeck hb hsigma hsigma0 hsigmaOut
  have hnear : dist (gamma s) (sigma t) ≤ (2 * Real.pi) * N.scale := by
    rw [hdist]
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) N.scale_pos.le)
      (N.edist_central_sphere_le_two_pi_mul_scale hsCentral htCentral)
  obtain ⟨ell, hell, hellA, hellB, hdepth, hchord⟩ := match_minimizing_exit_times
    hgamma hsigma (hgamma0.trans hsigma0.symm) hs ht hsDepth htDepth hnear
  have hchord' : dist (gamma ell) (sigma ell) ≤ (4 * Real.pi) * N.scale := by
    nlinarith [hchord]
  exact ⟨ell, hell, hellA, hellB, hdepth, hchord',
    relative_neck_chord_bound g N hdepth hchord'⟩

end Neck

end PoincareConjecture.M30
