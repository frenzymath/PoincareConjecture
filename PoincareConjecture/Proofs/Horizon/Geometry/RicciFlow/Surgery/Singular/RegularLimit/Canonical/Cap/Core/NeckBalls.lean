import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Radius
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.CollarDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem edist_lower_between_closedCollars (N : EpsilonNeck g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < N.epsilon⁻¹)
    {p x : M} (hp : p ∈ N.closedCollar a) (hx : x ∉ N.closedCollar b) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (b - a)) ≤
      g.edist p x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpa := (N.mem_coordinate_slab_iff (neg_lt_neg (hab.trans hb))
    (hab.trans hb)).mp hp
  have haxis : |(N.coordinate_inverse p).2| ≤ a := abs_le.mpr hpa.2
  have hfactor : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  by_contra h
  have hdist : Manifold.riemannianEDist (𝓡 3) p x <
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (b - a)) :=
    lt_of_not_ge h
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hdist (by norm_num : (0 : ℝ) < 1)
  have hstart : γ 0 ∈ N.region (-b) b := by
    rw [hγ0]
    exact ⟨hpa.1, by linarith [hpa.2.1], hpa.2.2.trans_lt hab⟩
  have hout : γ 1 ∉ N.coordinate_map '' (univ ×ˢ Icc (-b) b) := by
    rwa [hγ1]
  obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
    (by norm_num : (0 : ℝ) ≤ 1) (neg_lt_neg hb) hb
    hγ.continuous.continuousOn hstart hout
  have hvalue : b - a ≤ |(N.coordinate_inverse (γ t)).2 -
      (N.coordinate_inverse (γ 0)).2| := by
    rw [hγ0]
    have hbabs : |(N.coordinate_inverse (γ t)).2| = b := by
      rcases hboundary with hneg | hpos
      · rw [hneg, abs_neg, abs_of_pos (ha.trans_lt hab)]
      · rw [hpos, abs_of_pos (ha.trans_lt hab)]
    have htriangle := abs_sub_abs_le_abs_sub
      (N.coordinate_inverse (γ t)).2 (N.coordinate_inverse p).2
    rw [hbabs] at htriangle
    linarith
  have hax := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hvalue hfactor)).trans
    (N.axial_displacement_le_pathELength ht.1.le hγ hcarrier)
  exact (not_lt_of_ge (hax.trans (Manifold.pathELength_mono le_rfl ht.2))) hlength

theorem precompact_ball_of_mem_closedCollar (N : EpsilonNeck g)
    {a b r : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < N.epsilon⁻¹)
    {p : M} (hp : p ∈ N.closedCollar a) (hr : 0 < r)
    (hclear : r < N.scale * Real.sqrt (1 - N.epsilon) * (b - a)) :
    closure (g.ball p r) ⊆ N.closedCollar b ∧
      IsCompact (closure (g.ball p r)) := by
  have hsub : closure (g.ball p r) ⊆ N.closedCollar b := by
    rw [g.closure_ball_eq_edist_le p hr]
    intro x hx
    by_contra hout
    have hlow := N.edist_lower_between_closedCollars ha hab hb hp hout
    exact (not_lt_of_ge (hlow.trans hx))
      ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hclear)).mpr hclear)
  exact ⟨hsub, (N.isCompact_closedCollar hb).of_isClosed_subset isClosed_closure hsub⟩

theorem precompact_three_scale_ball (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 200) {p : M}
    (hp : p ∈ N.closedCollar ((0.75 : ℝ) * N.epsilon⁻¹)) :
    closure (g.ball p (3 * N.scale)) ⊆ N.carrier ∧
      IsCompact (closure (g.ball p (3 * N.scale))) := by
  have hs := N.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hinv : 200 ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hgap : 3 < Real.sqrt (1 - N.epsilon) *
      ((0.875 : ℝ) * N.epsilon⁻¹ - (0.75 : ℝ) * N.epsilon⁻¹) := by
    have h := mul_le_mul_of_nonneg_right hroot hi.le
    nlinarith
  have hb : (0.875 : ℝ) * N.epsilon⁻¹ < N.epsilon⁻¹ := by linarith
  have hclear : 3 * N.scale < N.scale * Real.sqrt (1 - N.epsilon) *
      ((0.875 : ℝ) * N.epsilon⁻¹ - (0.75 : ℝ) * N.epsilon⁻¹) := by
    nlinarith [mul_lt_mul_of_pos_left hgap N.scale_pos]
  obtain ⟨hsub, hcompact⟩ := N.precompact_ball_of_mem_closedCollar
    (by positivity) (by linarith : (0.75 : ℝ) * N.epsilon⁻¹ < (0.875 : ℝ) * N.epsilon⁻¹)
    hb hp (by positivity : 0 < 3 * N.scale) hclear
  exact ⟨hsub.trans (N.closedCollar_subset_carrier hb), hcompact⟩

theorem exists_calibrated_radius_of_scalar_bounds (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 200)
    (hscalar : ∀ x ∈ N.carrier,
      (1 / 2 : ℝ) < N.scale ^ 2 * N.connection.scalarCurvature x ∧
        N.scale ^ 2 * N.connection.scalarCurvature x < 2)
    {p : M} (hp : p ∈ N.closedCollar ((0.75 : ℝ) * N.epsilon⁻¹)) :
    ∃ r ∈ Icc (N.scale / 2) (2 * N.scale),
      scalarCurvatureSupOn g N.connection (g.ball p r) = r⁻¹ ^ 2 ∧
      closure (g.ball p r) ⊆ N.carrier ∧ IsCompact (closure (g.ball p r)) := by
  have hs := N.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hpN := N.closedCollar_subset_carrier
    (show (0.75 : ℝ) * N.epsilon⁻¹ < N.epsilon⁻¹ by linarith) hp
  obtain ⟨hsub, hcompact⟩ := N.precompact_three_scale_ball hε hp
  have hball {r : ℝ} (hr : r ≤ 3 * N.scale) : g.ball p r ⊆ g.ball p (3 * N.scale) :=
    fun x hx => hx.trans_le (ENNReal.ofReal_le_ofReal hr)
  have hbdd {r : ℝ} (hr : r ≤ 3 * N.scale) : BddAbove
      (range (fun x : g.ball p r => N.connection.scalarCurvature x)) := by
    have h := (hcompact.image N.connection.continuous_scalarCurvature).bddAbove
    apply h.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, subset_closure (hball hr x.property), rfl⟩
  have hmem {r : ℝ} (hr : 0 < r) : p ∈ g.ball p r := by
    change g.edist p p < ENNReal.ofReal r
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hr
  have hleft : scalarCurvatureSupOn g N.connection (g.ball p (N.scale / 2)) ≤
      (N.scale / 2)⁻¹ ^ 2 := by
    apply csSup_le
    · exact ⟨_, ⟨⟨p, hmem (by positivity)⟩, rfl⟩⟩
    · rintro _ ⟨x, rfl⟩
      have hxN := hsub (subset_closure (hball (by linarith) x.property))
      have hh := (hscalar x hxN).2
      have hpow : (N.scale / 2)⁻¹ ^ 2 * N.scale ^ 2 = 4 := by field_simp; ring
      nlinarith [sq_pos_of_pos hs]
  have hright : (2 * N.scale)⁻¹ ^ 2 ≤
      scalarCurvatureSupOn g N.connection (g.ball p (2 * N.scale)) := by
    have hpoint : (2 * N.scale)⁻¹ ^ 2 ≤ N.connection.scalarCurvature p := by
      have hh := (hscalar p hpN).1
      have hpow : (2 * N.scale)⁻¹ ^ 2 * N.scale ^ 2 = 1 / 4 := by field_simp; ring
      nlinarith [sq_pos_of_pos hs]
    exact hpoint.trans (le_csSup (hbdd (by linarith))
      ⟨⟨p, hmem (by positivity)⟩, rfl⟩)
  obtain ⟨r, hr, hcal⟩ := exists_scalar_calibrated_radius g N.connection
    N.connection.continuous_scalarCurvature p (by positivity : 0 < N.scale / 2)
    (by linarith : N.scale / 2 ≤ 2 * N.scale)
    (by linarith : 2 * N.scale < 3 * N.scale) hcompact hleft hright
  have hclosure : closure (g.ball p r) ⊆ closure (g.ball p (3 * N.scale)) :=
    closure_mono (hball (by linarith [hr.2]))
  exact ⟨r, hr, hcal, hclosure.trans hsub,
    hcompact.of_isClosed_subset isClosed_closure hclosure⟩

theorem exists_deep_collar_calibration_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ N : EpsilonNeck g, N.epsilon ≤ ε₀ →
      ∀ p ∈ N.closedCollar ((0.75 : ℝ) * N.epsilon⁻¹),
        ∃ r ∈ Icc (N.scale / 2) (2 * N.scale),
          scalarCurvatureSupOn g N.connection (g.ball p r) = r⁻¹ ^ 2 ∧
          closure (g.ball p r) ⊆ N.carrier ∧ IsCompact (closure (g.ball p r)) := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε p hp
  apply N.exists_calibrated_radius_of_scalar_bounds (hε.trans hsmall) ?_ hp
  intro x hx
  have hcoord := N.coordinate_inverse_mem x hx
  have hb := (hcontrol N N.connection hε (N.coordinate_inverse x).1 hcoord.2).1
  rw [Prod.eta, N.coordinate_map_coordinate_inverse hx] at hb
  constructor <;> linarith [(abs_lt.mp hb).1, (abs_lt.mp hb).2]

end PoincareConjecture.EpsilonNeck
