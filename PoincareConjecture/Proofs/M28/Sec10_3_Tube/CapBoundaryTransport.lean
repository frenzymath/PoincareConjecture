import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

private theorem edist_lower_of_axis_le_of_not_mem_carrier_local
    (N : EpsilonNeck g) {p x : M} {a : ℝ}
    (hp : p ∈ N.carrier) (ha : 0 ≤ a) (haL : a < N.epsilon⁻¹)
    (haxis : |(N.coordinate_inverse p).2| ≤ a) (hx : x ∉ N.carrier) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
      (N.epsilon⁻¹ - a)) ≤ g.edist p x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfactor : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  have hbound (s : ℝ) (hs : s ∈ Ioo a N.epsilon⁻¹) :
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - a)) ≤
        g.edist p x := by
    by_contra h
    have hdist : Manifold.riemannianEDist (𝓡 3) p x <
        ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - a)) :=
      lt_of_not_ge h
    obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hdist
    have hleft : -N.epsilon⁻¹ < -s := neg_lt_neg hs.2
    have hstart : γ 0 ∈ N.region (-s) s := by
      rw [hγ0]
      exact ⟨hp, by linarith [(abs_le.mp haxis).1, hs.1],
        by linarith [(abs_le.mp haxis).2, hs.1]⟩
    have hout : γ 1 ∉ N.coordinate_map '' (univ ×ˢ Icc (-s) s) := by
      rw [hγ1]
      exact fun hmem => hx ((N.mem_coordinate_slab_iff hleft hs.2).mp hmem).1
    obtain ⟨t, ht, hcarrier, hboundary, -⟩ :=
      N.exists_initial_segment_to_slab_boundary
        (show (0 : ℝ) ≤ 1 by norm_num) hleft hs.2
        hγ.continuousOn hstart hout
    have hvalue : s - a ≤ |(N.coordinate_inverse (γ t)).2 -
        (N.coordinate_inverse (γ 0)).2| := by
      rw [hγ0]
      have hb : |(N.coordinate_inverse (γ t)).2| = s := by
        rcases hboundary with hneg | hpos
        · rw [hneg, abs_neg, abs_of_nonneg (ha.trans hs.1.le)]
        · rw [hpos, abs_of_nonneg (ha.trans hs.1.le)]
      have htriangle := abs_sub_abs_le_abs_sub
        (N.coordinate_inverse (γ t)).2 (N.coordinate_inverse p).2
      rw [hb] at htriangle
      linarith
    have hax := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hvalue hfactor)).trans
      (N.path_axial_displacement_le_sharp ht.1.le
        (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hcarrier)
    have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    exact (not_lt_of_ge (hax.trans hmono)) hlength
  have hclosed : IsClosed {s : ℝ |
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - a)) ≤
        g.edist p x} :=
    isClosed_le (ENNReal.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.sub continuous_const))) continuous_const
  have hclosure := hclosed.closure_subset_iff.mpr (show Ioo a N.epsilon⁻¹ ⊆
      {s : ℝ | ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - a)) ≤
        g.edist p x} from hbound)
  rw [closure_Ioo haL.ne] at hclosure
  exact hclosure ⟨haL.le, le_rfl⟩

theorem mem_carrier_of_edist_lt_escape (N : EpsilonNeck g) {x y : M}
    (hx : x ∈ N.carrier) {r : ℝ} (_hr : 0 < r)
    (hrA : r < N.epsilon⁻¹ - |(N.coordinate_inverse x).2|)
    (hxy : g.edist x y <
      ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) * r)) :
    y ∈ N.carrier := by
  by_contra hy
  have hcoord := (N.coordinate_inverse_mem x hx).2
  have hheight : |(N.coordinate_inverse x).2| < N.epsilon⁻¹ := by
    rw [abs_lt]
    constructor <;> linarith [hcoord.1, hcoord.2]
  have hlower := edist_lower_of_axis_le_of_not_mem_carrier_local N
    hx (abs_nonneg _) hheight (le_rfl) hy
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) := by
    exact mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  have hmul : (N.scale * Real.sqrt (1 - N.epsilon)) * r <
      (N.scale * Real.sqrt (1 - N.epsilon)) *
        (N.epsilon⁻¹ - |(N.coordinate_inverse x).2|) := by
    exact mul_lt_mul_of_pos_left hrA hfactor
  have hreal : ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) * r) <
      ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) *
        (N.epsilon⁻¹ - |(N.coordinate_inverse x).2|)) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hmul
  exact (not_lt_of_ge hreal.le) (hlower.trans_lt hxy)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem edist_le_intrinsicEDist_local (g : RiemannianMetric 3 M)
    (U : Set M) (x y : M) : g.edist x y ≤ intrinsicEDist g U x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_sInf
  rintro L ⟨γ, hγ, h0, h1, _, rfl⟩
  exact Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one

omit [T2Space M] in
private theorem cap_scalar_le_sup (K : CapCertificate g) {x : M}
    (hx : x ∈ K.carrier) :
    K.connection.scalarCurvature x ≤
      scalarCurvatureSupOn g K.connection K.carrier := by
  obtain ⟨bound, _, hratio⟩ := K.scalar_ratio
  have hbounded : BddAbove (range (fun z : K.carrier =>
      K.connection.scalarCurvature z.1)) := by
    refine ⟨bound * K.connection.scalarCurvature x, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hratio x hx z.1 z.2
  exact le_csSup hbounded ⟨⟨x, hx⟩, rfl⟩

theorem scalar_rpow_neg_half_le_of_normalized_error
    {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    (herr : |s ^ 2 * R - 1| < 1 / 100) :
    R ^ (-1 / 2 : ℝ) ≤ (1.006 : ℝ) * s := by
  have hprod : (0.99 : ℝ) < s ^ 2 * R := by
    nlinarith [abs_lt.mp herr |>.1]
  have hpowpos : 0 < R ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hR _
  have hscale : 0 < (1.006 : ℝ) * s := mul_pos (by norm_num) hs
  by_contra hnot
  have hlt : (1.006 : ℝ) * s < R ^ (-1 / 2 : ℝ) := lt_of_not_ge hnot
  have hsq : ((1.006 : ℝ) * s) ^ 2 <
      (R ^ (-1 / 2 : ℝ)) ^ 2 := by
    nlinarith [hscale, hpowpos]
  have hrpow : (R ^ (-1 / 2 : ℝ)) ^ 2 = R⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num [Real.rpow_neg_one]
  rw [hrpow] at hsq
  have hsqmul := mul_lt_mul_of_pos_right hsq hR
  rw [inv_mul_cancel₀ hR.ne'] at hsqmul
  nlinarith [hprod]

theorem exists_cap_core_normalized_scalar_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (K : CapCertificate g)
        (N : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → ∀ x ∈ K.core, x ∈ N.carrier →
          |N.scale ^ 2 * K.connection.scalarCurvature x - 1| < 1 / 100 := by
  obtain ⟨epsilon₀, hpos, hsmall, haccuracy⟩ :=
    tube.exists_cylinder_scalar_accuracy.{u} (delta := 1 / 100) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g K N hN x hxK hxN
  exact haccuracy M g K.connection N hN x hxN

theorem exists_cap_core_scalar_radius_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (K : CapCertificate g)
        (N : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → ∀ x ∈ K.core, x ∈ N.carrier →
          K.connection.scalarCurvature x ^ (-1 / 2 : ℝ) ≤
            (1.006 : ℝ) * N.scale := by
  obtain ⟨epsilon₀, hpos, hsmall, haccuracy⟩ :=
    exists_cap_core_normalized_scalar_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g K N hN x hxK hxN
  have hxinterior : x ∈ interior K.closed_core := by
    rw [← K.core_eq_interior_closed_core]
    exact hxK
  have hxclosed : x ∈ K.closed_core := interior_subset hxinterior
  have hxKcar : x ∈ K.carrier := by
    rw [K.closed_core_eq_complement_end] at hxclosed
    exact hxclosed.1
  exact scalar_rpow_neg_half_le_of_normalized_error N.scale_pos
    (K.scalar_pos x hxKcar) (haccuracy M g K N hN x hxK hxN)

theorem edist_le_of_mem_closure_tail (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x : M} (hx : x ∈ N.carrier)
    {A : ℝ}
    (hxupper : (N.coordinate_inverse x).2 ≤ A)
    {p : M} (hp : p ∈ closure (N.region ((255 : ℝ) * A / 256) A))
    :
    g.edist x p ≤ ENNReal.ofReal
      ((1.0005 : ℝ) * N.scale *
        (A - (N.coordinate_inverse x).2 + A / 256 + 7.1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hpoint (y : M) (hy : y ∈ N.region ((255 : ℝ) * A / 256) A) :
      g.edist x y ≤ ENNReal.ofReal
        ((1.0005 : ℝ) * N.scale *
          (A - (N.coordinate_inverse x).2 + A / 256 + 7.1)) := by
    have hycar : y ∈ N.carrier := hy.1
    have hax := N.intrinsicEDist_le_axial_add hx hycar
    have hed := (edist_le_intrinsicEDist_local g N.carrier x y).trans hax
    have hyheight : (N.coordinate_inverse y).2 < A := hy.2.2
    have hyheight' : (255 : ℝ) * A / 256 <
        (N.coordinate_inverse y).2 := hy.2.1
    have hdiff : |(N.coordinate_inverse y).2 -
        (N.coordinate_inverse x).2| ≤
        A - (N.coordinate_inverse x).2 + A / 256 := by
      by_cases hxy : (N.coordinate_inverse x).2 ≤
          (N.coordinate_inverse y).2
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_neg (by linarith [hxy])]
        have hgap : (N.coordinate_inverse x).2 -
            (N.coordinate_inverse y).2 ≤ A / 256 := by
          linarith [hyheight', hxupper]
        linarith [hgap, hxupper]
    have hsqrt : Real.sqrt (1 + N.epsilon) ≤ (1.0005 : ℝ) := by
      have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by
        linarith [N.epsilon_pos])
      nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
    have hconst : Real.sqrt 2 * (Real.pi + 1) ≤ (7.1 : ℝ) := by
      have hs2 : Real.sqrt 2 ≤ (1.415 : ℝ) := by
        have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        have hs22 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
        nlinarith
      have hpi : Real.pi + 1 ≤ (5 : ℝ) := by
        nlinarith [Real.pi_le_four]
      have hnonneg : 0 ≤ Real.pi + 1 := by
        nlinarith [Real.pi_pos]
      nlinarith [mul_le_mul hs2 hpi hnonneg (by norm_num : (0 : ℝ) ≤ 1.415)]
    have hinner : |(N.coordinate_inverse y).2 -
          (N.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1) ≤
        A - (N.coordinate_inverse x).2 + A / 256 + 7.1 := by
      linarith [hdiff, hconst]
    have hnonneg : 0 ≤ |(N.coordinate_inverse y).2 -
          (N.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1) := by
      positivity
    have hscale := mul_le_mul_of_nonneg_left hinner N.scale_pos.le
    have hroot := mul_le_mul_of_nonneg_right hsqrt hnonneg
    have hfactor : N.scale * Real.sqrt (1 + N.epsilon) *
          (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
            Real.sqrt 2 * (Real.pi + 1)) ≤
        (1.0005 : ℝ) * N.scale *
          (A - (N.coordinate_inverse x).2 + A / 256 + 7.1) := by
      calc
        N.scale * Real.sqrt (1 + N.epsilon) *
            (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
              Real.sqrt 2 * (Real.pi + 1)) ≤
            N.scale * ((1.0005 : ℝ) *
              (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
                Real.sqrt 2 * (Real.pi + 1))) := by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left hroot N.scale_pos.le)
        _ ≤ N.scale * ((1.0005 : ℝ) *
            (A - (N.coordinate_inverse x).2 + A / 256 + 7.1)) := by
          have hscale' := mul_le_mul_of_nonneg_left hscale
            (by norm_num : (0 : ℝ) ≤ 1.0005)
          calc
            N.scale * ((1.0005 : ℝ) *
                (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
                  Real.sqrt 2 * (Real.pi + 1))) =
                (1.0005 : ℝ) * (N.scale *
                  (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
                    Real.sqrt 2 * (Real.pi + 1))) := by ring
            _ ≤ (1.0005 : ℝ) * (N.scale *
                (A - (N.coordinate_inverse x).2 + A / 256 + 7.1)) := hscale'
            _ = N.scale * ((1.0005 : ℝ) *
                (A - (N.coordinate_inverse x).2 + A / 256 + 7.1)) := by ring
        _ = (1.0005 : ℝ) * N.scale *
            (A - (N.coordinate_inverse x).2 + A / 256 + 7.1) := by ring
    exact hed.trans (ENNReal.ofReal_le_ofReal hfactor)
  exact closure_minimal hpoint
    (isClosed_le (continuous_const.edist continuous_id) continuous_const) hp

theorem successor_middle_margin_of_positive_end (K : CapCertificate g)
    (N Q : EpsilonNeck g) {A : ℝ} (hε : N.epsilon ≤ 1 / 1000)
    (hQε : Q.epsilon = N.epsilon) (hAeq : N.epsilon⁻¹ = A)
    (hA : 4 * K.cap_constant < A)
    (hA₀ : (1000 : ℝ) ≤ A)
    (hQs : (0.999 : ℝ) * N.scale < Q.scale)
    (hQc : Q.center ∈ closure (N.region ((255 : ℝ) * A / 256) A))
    {x : M} (hxN : x ∈ N.carrier)
    (hxend : A - (1.009 : ℝ) * K.cap_constant <
      (N.coordinate_inverse x).2)
    (hforward : N.region (A / 2) A ⊆ Q.carrier) :
    x ∈ Q.carrier ∧
      |(Q.coordinate_inverse x).2| ≤
        Q.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hApos : 0 < A := by nlinarith [K.cap_constant_pos]
  have hCpos : 0 < K.cap_constant := K.cap_constant_pos
  have hquarter : (1.009 : ℝ) * K.cap_constant < A / 2 := by
    nlinarith
  have hxcoord : (N.coordinate_inverse x).2 < A := by
    rw [← hAeq]
    exact (N.coordinate_inverse_mem x hxN).2.2
  have hxregion : x ∈ N.region (A / 2) A := by
    refine ⟨hxN, ?_, hxcoord⟩
    nlinarith
  have hxQ : x ∈ Q.carrier := hforward hxregion
  have hxpos : 0 ≤ (N.coordinate_inverse x).2 := by
    nlinarith [hA, hCpos]
  have hdist := edist_le_of_mem_closure_tail N hε hxN hxcoord.le hQc
  have hdist' : g.edist x Q.center ≤ ENNReal.ofReal
      ((1.0005 : ℝ) * N.scale *
        ((1.009 : ℝ) * K.cap_constant + A / 256 + 7.1)) := by
    apply hdist.trans
    apply ENNReal.ofReal_le_ofReal
    have harg : A - (N.coordinate_inverse x).2 + A / 256 + 7.1 ≤
        (1.009 : ℝ) * K.cap_constant + A / 256 + 7.1 := by
      linarith [hxend]
    exact mul_le_mul_of_nonneg_left harg
      (mul_nonneg (by norm_num) N.scale_pos.le)
  have hradpos : 0 < A - (1.009 : ℝ) * K.cap_constant := by
    nlinarith
  have hradQ : A - (1.009 : ℝ) * K.cap_constant < Q.epsilon⁻¹ := by
    rw [hQε]
    have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hε
        (inv_pos.mpr N.epsilon_pos).le
      rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
      nlinarith
    rw [← hAeq]
    nlinarith [hA, hCpos, hinv]
  have hQeq : Q.epsilon⁻¹ = A := by
    rw [hQε, ← hAeq]
  by_contra hbad
  have hnot : x ∉ Q.region (-(A - (1.009 : ℝ) * K.cap_constant))
      (A - (1.009 : ℝ) * K.cap_constant) := by
    intro hxreg
    have hboundQ : A - (1.009 : ℝ) * K.cap_constant ≤
        Q.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant := by
      rw [hQeq]
    exact hbad ⟨hxQ,
      abs_le.mpr ⟨by linarith [hxreg.2.1, hboundQ],
        by linarith [hxreg.2.2, hboundQ]⟩⟩
  have hlow := Q.edist_central_lower_of_not_mem_region hradpos hradQ
    Q.center_on_central_sphere hnot
  have hroot : (0.998 : ℝ) < Real.sqrt (1 - Q.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - Q.epsilon by
      linarith [Q.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 - Q.epsilon)]
  have hscale : (0.997 : ℝ) * N.scale <
      Q.scale * Real.sqrt (1 - Q.epsilon) := by
    have hprod := mul_lt_mul_of_pos_right hroot Q.scale_pos
    have hq' := mul_lt_mul_of_pos_left hQs
      (by norm_num : (0 : ℝ) < 0.998)
    have hq : (0.997 : ℝ) * N.scale < (0.998 : ℝ) * Q.scale := by
      nlinarith [hq', N.scale_pos]
    nlinarith [hprod, hq]
  have hlow' : ENNReal.ofReal ((0.997 : ℝ) * N.scale *
      (A - (1.009 : ℝ) * K.cap_constant)) ≤ g.edist x Q.center := by
    have hfactor : 0 ≤ (0.997 : ℝ) * N.scale *
        (A - (1.009 : ℝ) * K.cap_constant) :=
      mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hradpos.le
    have hmul := mul_le_mul_of_nonneg_right hscale.le hradpos.le
    have hmulE : ENNReal.ofReal ((0.997 : ℝ) * N.scale *
        (A - (1.009 : ℝ) * K.cap_constant)) ≤
        ENNReal.ofReal (Q.scale * Real.sqrt (1 - Q.epsilon) *
          (A - (1.009 : ℝ) * K.cap_constant)) := by
      have hright : 0 ≤ Q.scale * Real.sqrt (1 - Q.epsilon) *
          (A - (1.009 : ℝ) * K.cap_constant) :=
        mul_nonneg (mul_nonneg Q.scale_pos.le (Real.sqrt_nonneg _)) hradpos.le
      apply (ENNReal.ofReal_le_ofReal_iff hright).mpr
      exact hmul
    have hlowcenter : ENNReal.ofReal (Q.scale * Real.sqrt (1 - Q.epsilon) *
        (A - (1.009 : ℝ) * K.cap_constant)) ≤ g.edist x Q.center := by
      have heq : g.edist x Q.center = g.edist Q.center x :=
        edist_comm x Q.center
      rw [heq]
      exact hlow
    exact hmulE.trans hlowcenter
  have hupper : (0.997 : ℝ) * N.scale *
      (A - (1.009 : ℝ) * K.cap_constant) ≤
      (1.0005 : ℝ) * N.scale *
        ((1.009 : ℝ) * K.cap_constant + A / 256 + 7.1) := by
    have hchain := hlow'.trans hdist'
    have htail : 0 ≤ (1.009 : ℝ) * K.cap_constant + A / 256 + 7.1 := by
      nlinarith [hApos, hCpos]
    have hright : 0 ≤ (1.0005 : ℝ) * N.scale *
        ((1.009 : ℝ) * K.cap_constant + A / 256 + 7.1) :=
      mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) htail
    have hreal := (ENNReal.ofReal_le_ofReal_iff hright).mp hchain
    nlinarith [hreal]
  have hupper' : N.scale * ((0.997 : ℝ) *
      (A - (1.009 : ℝ) * K.cap_constant)) ≤
      N.scale * ((1.0005 : ℝ) *
        ((1.009 : ℝ) * K.cap_constant + A / 256 + 7.1)) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hupper
  have hupper'' : ((0.997 : ℝ) *
      (A - (1.009 : ℝ) * K.cap_constant)) * N.scale ≤
      ((1.0005 : ℝ) *
        ((1.009 : ℝ) * K.cap_constant + A / 256 + 7.1)) * N.scale := by
    simpa only [mul_comm] using hupper'
  have hscalar := (mul_le_mul_iff_left₀ N.scale_pos).mp hupper''
  nlinarith [hscalar, hA, hA₀, hCpos]

omit [T2Space M] in

theorem predecessor_middle_margin_of_negative_end (K : CapCertificate g)
    (N P : EpsilonNeck g) {A : ℝ} (hPε : P.epsilon = N.epsilon)
    (hAeq : N.epsilon⁻¹ = A)
    (hA : 4 * K.cap_constant < A)
    (hrecip : N.region (-A) (-A / 2) ⊆
      P.region (-(0.2 : ℝ) * A) ((0.6 : ℝ) * A))
    {x : M} (hxN : x ∈ N.carrier)
    (hxend : (N.coordinate_inverse x).2 <
      -(A - (1.009 : ℝ) * K.cap_constant)) :
    x ∈ P.carrier ∧
      |(P.coordinate_inverse x).2| ≤
        P.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant := by
  have hCpos : 0 < K.cap_constant := K.cap_constant_pos
  have hneg : x ∈ N.region (-A) (-A / 2) := by
    refine ⟨hxN, ?_, ?_⟩
    · have hcoord := (N.coordinate_inverse_mem x hxN).2.1
      rw [← hAeq]
      exact hcoord
    · have hcoord := (N.coordinate_inverse_mem x hxN).2.2
      rw [← hAeq]
      nlinarith [hcoord]
  have hP := hrecip hneg
  refine ⟨hP.1, ?_⟩
  have hrad : (0.6 : ℝ) * A ≤
      P.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant := by
    rw [hPε, ← hAeq]
    have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    have hApos : 0 < A := by nlinarith
    nlinarith
  exact abs_le.mpr ⟨by linarith [hP.2.1], by linarith [hP.2.2, hrad]⟩

omit [T2Space M] in

theorem cap_carrier_edist_le_of_core_hit (K : CapCertificate g)
    (N : EpsilonNeck g) {x : M} (hxK : x ∈ K.core)
    (hscale : K.connection.scalarCurvature x ^ (-1 / 2 : ℝ) ≤
      (1.006 : ℝ) * N.scale) :
    ∀ y ∈ K.carrier,
      g.edist x y ≤ ENNReal.ofReal ((1.006 : ℝ) * K.cap_constant * N.scale) := by
  have hxinterior : x ∈ interior K.closed_core := by
    rw [← K.core_eq_interior_closed_core]
    exact hxK
  have hxclosed : x ∈ K.closed_core := interior_subset hxinterior
  have hxKcar : x ∈ K.carrier := by
    rw [K.closed_core_eq_complement_end] at hxclosed
    exact hxclosed.1
  have hsup := cap_scalar_le_sup K hxKcar
  have hpow := Real.rpow_le_rpow_of_nonpos (K.scalar_pos x hxKcar) hsup
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have hdiam : intrinsicDiameter g K.carrier <
      ENNReal.ofReal (K.cap_constant *
        K.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
    apply K.intrinsic_diameter_bound.trans_le
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hpow K.cap_constant_pos.le
  intro y hy
  have hpair : intrinsicEDist g K.carrier x y ≤ intrinsicDiameter g K.carrier :=
    le_sSup ⟨(⟨x, hxKcar⟩, ⟨y, hy⟩), rfl⟩
  have hed : g.edist x y < ENNReal.ofReal (K.cap_constant *
      K.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) :=
    (edist_le_intrinsicEDist_local g K.carrier x y).trans hpair |>.trans_lt hdiam
  have htarget : ENNReal.ofReal (K.cap_constant *
      K.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) ≤
      ENNReal.ofReal ((1.006 : ℝ) * K.cap_constant * N.scale) := by
    apply ENNReal.ofReal_le_ofReal
    calc
      K.cap_constant * K.connection.scalarCurvature x ^ (-1 / 2 : ℝ) ≤
          K.cap_constant * ((1.006 : ℝ) * N.scale) :=
        mul_le_mul_of_nonneg_left hscale K.cap_constant_pos.le
      _ = (1.006 : ℝ) * K.cap_constant * N.scale := by ring
  exact hed.le.trans htarget

omit [T2Space M] in

theorem cap_carrier_edist_le_of_core_hit_of_normalized_error
    (K : CapCertificate g) (N : EpsilonNeck g) {x : M}
    (hxK : x ∈ K.core)
    (hscalar : |N.scale ^ 2 * K.connection.scalarCurvature x - 1| < 1 / 100) :
    ∀ y ∈ K.carrier,
      g.edist x y ≤ ENNReal.ofReal ((1.006 : ℝ) * K.cap_constant * N.scale) := by
  have hxinterior : x ∈ interior K.closed_core := by
    rw [← K.core_eq_interior_closed_core]
    exact hxK
  have hxclosed : x ∈ K.closed_core := interior_subset hxinterior
  have hxKcar : x ∈ K.carrier := by
    rw [K.closed_core_eq_complement_end] at hxclosed
    exact hxclosed.1
  exact cap_carrier_edist_le_of_core_hit K N hxK
    (scalar_rpow_neg_half_le_of_normalized_error N.scale_pos
      (K.scalar_pos x hxKcar) hscalar)

theorem cap_carrier_subset_of_middle_escape (K : CapCertificate g)
    (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000) {x : M}
    (hxK : x ∈ K.core) (hxN : x ∈ N.carrier)
    (hscale : K.connection.scalarCurvature x ^ (-1 / 2 : ℝ) ≤
      (1.006 : ℝ) * N.scale)
    (hmargin : |(N.coordinate_inverse x).2| ≤
      N.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant) :
    K.carrier ⊆ N.carrier := by
  have hroot : (0.999 : ℝ) < Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hnum : (1.006 : ℝ) * K.cap_constant <
      Real.sqrt (1 - N.epsilon) * (1.008 : ℝ) * K.cap_constant := by
    have hstep := mul_lt_mul_of_pos_right hroot
      (mul_pos (by norm_num : (0 : ℝ) < 1.008) K.cap_constant_pos)
    nlinarith [hstep]
  have hcost : (1.006 : ℝ) * K.cap_constant * N.scale <
      (N.scale * Real.sqrt (1 - N.epsilon)) *
        ((1.008 : ℝ) * K.cap_constant) := by
    have hstep := mul_lt_mul_of_pos_right hnum N.scale_pos
    nlinarith [hstep]
  have hcostE : ENNReal.ofReal ((1.006 : ℝ) * K.cap_constant * N.scale) <
      ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) *
        ((1.008 : ℝ) * K.cap_constant)) := by
    have htargetPos : 0 < (N.scale * Real.sqrt (1 - N.epsilon)) *
        ((1.008 : ℝ) * K.cap_constant) := by
      exact mul_pos (mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith)))
        (mul_pos (by norm_num) K.cap_constant_pos)
    apply (ENNReal.ofReal_lt_ofReal_iff htargetPos).mpr
    exact hcost
  have hrad : (1.008 : ℝ) * K.cap_constant <
      N.epsilon⁻¹ - |(N.coordinate_inverse x).2| := by
    nlinarith [hmargin, K.cap_constant_pos]
  have hxy (y : M) (hy : y ∈ K.carrier) :
      g.edist x y < ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) *
        ((1.008 : ℝ) * K.cap_constant)) := by
    exact (cap_carrier_edist_le_of_core_hit K N hxK hscale y hy).trans_lt hcostE
  intro y hy
  exact mem_carrier_of_edist_lt_escape N hxN
    (mul_pos (by norm_num) K.cap_constant_pos) hrad (hxy y hy)

theorem cap_carrier_subset_union_of_middle_margin
    (K : CapCertificate g) (N Q : EpsilonNeck g)
    (hNε : N.epsilon ≤ 1 / 1000) (hQε : Q.epsilon ≤ 1 / 1000)
    {x : M} (hxK : x ∈ K.core) (hxN : x ∈ N.carrier) (hxQ : x ∈ Q.carrier)
    (hscaleN : K.connection.scalarCurvature x ^ (-1 / 2 : ℝ) ≤
      (1.006 : ℝ) * N.scale)
    (hscaleQ : K.connection.scalarCurvature x ^ (-1 / 2 : ℝ) ≤
      (1.006 : ℝ) * Q.scale)
    (hmargin :
      |(N.coordinate_inverse x).2| ≤
          N.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant ∨
      |(Q.coordinate_inverse x).2| ≤
          Q.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant) :
    K.carrier ⊆ N.carrier ∪ Q.carrier := by
  rcases hmargin with hN | hQ
  · exact fun y hy => Or.inl
      (cap_carrier_subset_of_middle_escape K N hNε hxK hxN hscaleN hN hy)
  · exact fun y hy => Or.inr
      (cap_carrier_subset_of_middle_escape K Q hQε hxK hxQ hscaleQ hQ hy)

theorem cap_carrier_subset_three_necks (K : CapCertificate g)
    (P N Q : EpsilonNeck g) {A : ℝ}
    (hε : N.epsilon ≤ 1 / 1000) (hPε : P.epsilon = N.epsilon)
    (hQε : Q.epsilon = N.epsilon) (hAeq : N.epsilon⁻¹ = A)
    (hA : 4 * K.cap_constant < A) (hA₀ : (1000 : ℝ) ≤ A)
    (hQs : (0.999 : ℝ) * N.scale < Q.scale)
    (hQc : Q.center ∈ closure (N.region ((255 : ℝ) * A / 256) A))
    (hforward : N.region (A / 2) A ⊆ Q.carrier)
    (hrecip : N.region (-A) (-A / 2) ⊆
      P.region (-(0.2 : ℝ) * A) ((0.6 : ℝ) * A))
    {x : M} (hxK : x ∈ K.core) (hxN : x ∈ N.carrier)
    (hscaleP : ∀ {z : M}, z ∈ K.core → z ∈ P.carrier →
      K.connection.scalarCurvature z ^ (-1 / 2 : ℝ) ≤
        (1.006 : ℝ) * P.scale)
    (hscaleN : ∀ {z : M}, z ∈ K.core → z ∈ N.carrier →
      K.connection.scalarCurvature z ^ (-1 / 2 : ℝ) ≤
        (1.006 : ℝ) * N.scale)
    (hscaleQ : ∀ {z : M}, z ∈ K.core → z ∈ Q.carrier →
      K.connection.scalarCurvature z ^ (-1 / 2 : ℝ) ≤
        (1.006 : ℝ) * Q.scale) :
    K.carrier ⊆ P.carrier ∪ N.carrier ∪ Q.carrier := by
  have hPsmall : P.epsilon ≤ 1 / 1000 := by
    rw [hPε]
    exact hε
  have hQsmall : Q.epsilon ≤ 1 / 1000 := by
    rw [hQε]
    exact hε
  by_cases hpos : A - (1.009 : ℝ) * K.cap_constant <
      (N.coordinate_inverse x).2
  · have hQmargin := successor_middle_margin_of_positive_end K N Q hε
      hQε hAeq hA hA₀ hQs hQc hxN hpos hforward
    have hNQ := cap_carrier_subset_union_of_middle_margin K N Q hε hQsmall
      hxK hxN hQmargin.1 (hscaleN hxK hxN) (hscaleQ hxK hQmargin.1)
      (Or.inr hQmargin.2)
    intro y hy
    rcases hNQ hy with hyN | hyQ
    · exact Or.inl (Or.inr hyN)
    · exact Or.inr hyQ
  · by_cases hneg : (N.coordinate_inverse x).2 <
        -(A - (1.009 : ℝ) * K.cap_constant)
    · have hPmargin := predecessor_middle_margin_of_negative_end K N P
        hPε hAeq hA hrecip hxN hneg
      have hPN := cap_carrier_subset_union_of_middle_margin K P N hPsmall hε
        hxK hPmargin.1 hxN (hscaleP hxK hPmargin.1) (hscaleN hxK hxN)
        (Or.inl hPmargin.2)
      intro y hy
      rcases hPN hy with hyP | hyN
      · exact Or.inl (Or.inl hyP)
      · exact Or.inl (Or.inr hyN)
    · have hNmargin :
          |(N.coordinate_inverse x).2| ≤
            N.epsilon⁻¹ - (1.009 : ℝ) * K.cap_constant := by
        have hupper : (N.coordinate_inverse x).2 ≤
            A - (1.009 : ℝ) * K.cap_constant := le_of_not_gt hpos
        have hlower : -(A - (1.009 : ℝ) * K.cap_constant) ≤
            (N.coordinate_inverse x).2 := le_of_not_gt hneg
        rw [abs_le]
        constructor <;> linarith [hAeq]
      exact fun y hy => Or.inl (Or.inr
        (cap_carrier_subset_of_middle_escape K N hε hxK hxN
          (hscaleN hxK hxN) hNmargin hy))

end PoincareConjecture.M28
