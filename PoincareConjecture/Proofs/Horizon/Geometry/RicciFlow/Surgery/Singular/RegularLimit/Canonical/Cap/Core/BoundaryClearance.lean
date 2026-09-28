import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.RadiusBound
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.BoundaryDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem core_radius_lt_two_mul_of_scalar_in_ball (N : CapCertificate g)
    {p z : M} (hp : p ∈ N.core) {s : ℝ} (hs : 0 < s)
    (hz : z ∈ g.ball p (N.core_radius p))
    (hscalar : (1 / 2 : ℝ) < s ^ 2 * N.connection.scalarCurvature z) :
    N.core_radius p < 2 * s := by
  have hr := N.core_radius_pos p hp
  have hball : g.ball p (N.core_radius p) ⊆ N.carrier :=
    fun _ hx => N.core_ball_subset p hp (subset_closure hx)
  have hbdd : BddAbove (range (fun x : g.ball p (N.core_radius p) =>
      N.connection.scalarCurvature x)) := by
    apply N.scalar_range_bddAbove.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, hball x.property⟩, rfl⟩
  have hle : N.connection.scalarCurvature z ≤ (N.core_radius p)⁻¹ ^ 2 := by
    rw [← N.core_radius_eq p hp]
    exact le_csSup hbdd ⟨⟨z, hz⟩, rfl⟩
  have hmul := mul_le_mul_of_nonneg_left hle (sq_nonneg s)
  have hmul' := mul_lt_mul_of_pos_right (hscalar.trans_le hmul) (sq_pos_of_pos hr)
  have hcancel : s ^ 2 * (N.core_radius p)⁻¹ ^ 2 * N.core_radius p ^ 2 = s ^ 2 := by
    field_simp
  rw [hcancel] at hmul'
  nlinarith

theorem core_ball_clearance_of_boundary_scalar (N : CapCertificate g)
    (hscalar : ∀ z ∈ N.boundary_sphere,
      (1 / 2 : ℝ) < N.boundary_neck.scale ^ 2 * N.connection.scalarCurvature z)
    {p y : M} (hp : p ∈ N.core) (hy : y ∉ N.carrier) :
    ENNReal.ofReal (N.core_radius p +
      (0.8 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹) ≤ g.edist p y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := N.boundary_neck.scale_pos
  have he := N.epsilon_pos
  have hr := N.core_radius_pos p hp
  have hinv : 200 ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ he).mpr
    linarith [N.epsilon_le_threshold]
  by_contra h
  have hshort : Manifold.riemannianEDist (𝓡 3) p y <
      ENNReal.ofReal (N.core_radius p +
        (0.8 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹) := lt_of_not_ge h
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hshort
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := N.boundary_inter_nonempty_of_crossing hconn
    ⟨p, ⟨0, by simp, h0⟩, hp⟩
    ⟨y, ⟨1, by simp, h1⟩, fun hc => hy (N.closed_core_subset_carrier hc)⟩
  have hright : ENNReal.ofReal ((0.9 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹) ≤
      Manifold.pathELength (𝓡 3) γ t 1 :=
    (N.boundary_edist_lower_of_not_mem_carrier hz hy).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2)
  by_cases hzball : γ t ∈ g.ball p (N.core_radius p)
  · have hsmall := N.core_radius_lt_two_mul_of_scalar_in_ball hp hs hzball (hscalar _ hz)
    have hnum : N.core_radius p + (0.8 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹ ≤
        (0.9 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹ := by
      have hm := mul_le_mul_of_nonneg_left hinv hs.le
      nlinarith
    exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal hnum).trans
      (hright.trans (Manifold.pathELength_mono ht.1 le_rfl)))) hlength
  · have hleft : ENNReal.ofReal (N.core_radius p) ≤
        Manifold.pathELength (𝓡 3) γ 0 t :=
      (le_of_not_gt hzball).trans
        (Manifold.riemannianEDist_le_pathELength
          (hγ.mono (Icc_subset_Icc_right ht.2)) h0 rfl ht.1)
    have hbuffer : ENNReal.ofReal ((0.8 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹) ≤
        Manifold.pathELength (𝓡 3) γ t 1 := by
      apply (ENNReal.ofReal_le_ofReal ?_).trans hright
      have hnonneg : 0 ≤ N.boundary_neck.scale * N.epsilon⁻¹ := by positivity
      nlinarith
    have htotal := (add_le_add hleft hbuffer).trans_eq (Manifold.pathELength_add ht.1 ht.2)
    rw [← ENNReal.ofReal_add hr.le (by positivity)] at htotal
    exact (not_lt_of_ge htotal) hlength

theorem exists_core_ball_clearance_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ N : CapCertificate g, N.epsilon ≤ ε₀ →
      ∀ p ∈ N.core, ∀ y ∉ N.carrier,
        ENNReal.ofReal (N.core_radius p +
          (0.8 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹) ≤ g.edist p y := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε p hp y hy
  apply N.core_ball_clearance_of_boundary_scalar ?_ hp hy
  intro z hz
  obtain ⟨w, hw, rfl⟩ := N.boundary_neck.central_sphere_eq ▸ (N.boundary_eq_neck_sphere ▸ hz)
  have hwzero : w.2 = 0 := hw.2
  have hwdom : w.2 ∈ Ioo (-N.boundary_neck.epsilon⁻¹) N.boundary_neck.epsilon⁻¹ := by
    rw [hwzero]
    exact ⟨neg_neg_of_pos (inv_pos.mpr N.boundary_neck.epsilon_pos),
      inv_pos.mpr N.boundary_neck.epsilon_pos⟩
  have hb := (hcontrol N.boundary_neck N.connection
    (N.boundary_neck_epsilon.trans_le hε) w.1 hwdom).1
  linarith [(abs_lt.mp hb).1]

noncomputable def coreBallClearanceThreshold : ℝ :=
  Classical.choose exists_core_ball_clearance_threshold.{u}

theorem coreBallClearanceThreshold_pos : 0 < coreBallClearanceThreshold.{u} :=
  (Classical.choose_spec exists_core_ball_clearance_threshold.{u}).1

theorem coreBallClearanceThreshold_le : coreBallClearanceThreshold.{u} ≤ 1 / 200 :=
  (Classical.choose_spec exists_core_ball_clearance_threshold.{u}).2.1

theorem core_ball_clearance (N : CapCertificate g)
    (hε : N.epsilon ≤ coreBallClearanceThreshold.{u})
    {p y : M} (hp : p ∈ N.core) (hy : y ∉ N.carrier) :
    ENNReal.ofReal (N.core_radius p +
      (0.8 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹) ≤ g.edist p y :=
  (Classical.choose_spec exists_core_ball_clearance_threshold.{u}).2.2 N hε p hp y hy

end PoincareConjecture.CapCertificate
