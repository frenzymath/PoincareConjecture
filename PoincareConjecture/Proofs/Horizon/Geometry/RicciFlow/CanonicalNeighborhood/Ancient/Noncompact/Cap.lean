import PoincareConjecture.Definitions.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Ch01.ScalarOperators
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds














set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem CapCertificate.one_lt_cap_constant (cap : CapCertificate g) :
    1 < cap.cap_constant := by
  obtain ⟨p, hp⟩ := cap.core_nonempty
  have hmem := cap.core_subset_carrier hp
  have hpos := cap.scalar_pos p hmem
  have hlt := cap.scalar_lt_constant_mul hmem hmem
  nlinarith

namespace NoncompactKappa

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem scalar_function_eq (D D' : LeviCivitaData g) :
    D.scalarCurvature = D'.scalarCurvature :=
  funext (D.scalarCurvature_eq D')

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem evolution_expression_eq (D D' : LeviCivitaData g) (x : M) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      D'.laplacian D'.scalarCurvature x + 2 * D'.ricciNormSq x := by
  rw [scalar_function_eq D D', D.laplacian_eq D']
  simp only [LeviCivitaData.ricciNormSq, LeviCivitaData.ricci, D.horizon_curvatureTensor_eq D']


noncomputable def neckWithConnection (N : EpsilonNeck g) (D : LeviCivitaData g) :
    EpsilonNeck g :=
  { N with
    connection := D
    scalar_center_pos := by rw [← N.connection.scalarCurvature_eq D]; exact N.scalar_center_pos
    scale_eq_scalar := by rw [← N.connection.scalarCurvature_eq D]; exact N.scale_eq_scalar }



noncomputable def capWithConnection (cap : CapCertificate g) (D : LeviCivitaData g) :
    CapCertificate g := by
  have hscalar := scalar_function_eq cap.connection D
  have hsup (X : Set M) : scalarCurvatureSupOn g cap.connection X =
      scalarCurvatureSupOn g D X := by simp only [scalarCurvatureSupOn, hscalar]
  refine { cap with
    connection := D
    end_neck := neckWithConnection cap.end_neck D
    end_neck_connection := rfl
    boundary_neck := neckWithConnection cap.boundary_neck D
    boundary_neck_connection := rfl
    scalar_pos := ?_
    intrinsic_diameter_bound := ?_
    scalar_ratio := ?_
    volume_bound := ?_
    core_radius_eq := ?_
    gradient_bound := ?_
    laplacian_bound := ?_ }
  · simpa only [hscalar] using cap.scalar_pos
  · simpa only [hsup] using cap.intrinsic_diameter_bound
  · simpa only [hscalar] using cap.scalar_ratio
  · simpa only [hsup] using cap.volume_bound
  · simpa only [hsup] using cap.core_radius_eq
  · simpa only [scalarGradientNorm, hscalar] using cap.gradient_bound
  · obtain ⟨b, hb, hbound⟩ := cap.laplacian_bound
    refine ⟨b, hb, fun x hx => ?_⟩
    have h := hbound x hx
    rw [evolution_expression_eq cap.connection D] at h
    simpa only [hscalar] using h

variable [SecondCountableTopology M] [ConnectedSpace M]



noncomputable def strongCapOfCap (K : AncientKappaSolution 3 M) {t epsilon C : ℝ}
    (ht : t ≤ 0) (cap : CapCertificate (K.flow.metric t))
    (hepsilon : cap.epsilon = epsilon) (hconstant : cap.cap_constant ≤ C) :
    StrongCapCertificate K t epsilon C := by
  let cap' := capWithConnection cap (K.flow.connection t)
  have hC : 0 < C := cap.cap_constant_pos.trans_le hconstant
  let p := cap'.core_nonempty.choose
  have hp : p ∈ cap'.core := cap'.core_nonempty.choose_spec
  refine {
    time_mem := ht
    epsilon_pos := hepsilon ▸ cap.epsilon_pos
    constant_pos := hC
    cap := cap'
    cap_epsilon := hepsilon
    cap_constant := hconstant
    center := p
    center_in_core := hp
    scalar_pos := cap'.scalar_pos
    intrinsic_diameter_scale := ?_
    scalar_ratio := ?_
    volume_bound := ?_
    gradient_bound := ?_
    laplacian_bound := ?_
    core_ball_scale := ?_ }
  · exact cap'.intrinsic_diameter_bound.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hconstant
        (Real.rpow_nonneg cap'.scalar_sup_pos.le _)))
  · intro x hx y hy
    exact (cap'.scalar_lt_constant_mul hx hy).le.trans
      (mul_le_mul_of_nonneg_right hconstant (cap'.scalar_pos x hx).le)
  · apply cap'.volume_bound.le.trans
    rw [← ENNReal.ofReal_rpow_of_pos cap'.scalar_sup_pos]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hconstant) le_rfl
  · obtain ⟨b, hb, hbound⟩ := cap'.gradient_bound
    intro x hx
    exact (hbound x hx).trans (mul_le_mul_of_nonneg_right
      (hb.le.trans hconstant) (Real.rpow_nonneg (cap'.scalar_pos x hx).le _))
  · obtain ⟨b, hb, hbound⟩ := cap'.laplacian_bound
    intro x hx
    exact (hbound x hx).trans
      (mul_le_mul_of_nonneg_right (hb.le.trans hconstant) (sq_nonneg _))
  · intro y hy
    refine ⟨cap'.core_radius y, cap'.core_radius_pos y hy,
      cap'.core_radius_eq y hy,
      Set.Subset.trans subset_closure (cap'.core_ball_subset y hy),
      cap'.core_ball_compact y hy, ?_⟩
    obtain ⟨b, hb, hbound⟩ := cap'.core_ball_volume_lower
    apply le_trans (b := ENNReal.ofReal (b * cap'.core_radius y ^ 3)) ?_ (hbound y hy)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (cap'.core_radius_pos y hy).le _)
    exact ((inv_le_inv₀ hC cap'.cap_constant_pos).2 hconstant).trans hb.le



noncomputable def strongCappedTubeOfCappedTube (K : AncientKappaSolution 3 M)
    {t epsilon C : ℝ} (ht : t ≤ 0)
    (tube : CappedTubeCertificate (K.flow.metric t))
    (hcap : tube.cap.epsilon = epsilon) (htube : tube.tube.epsilon = epsilon)
    (hconstant : tube.cap.cap_constant ≤ C)
    (hstrong : ∀ x ∈ tube.tube.carrier,
      ∃ N : StrongEvolvingNeck K t epsilon, N.center = x)
    (hwhole : tube.carrier = Set.univ) :
    M26StrongCappedTube K t epsilon C :=
  { time_mem := ht
    epsilon_pos := hcap ▸ tube.cap.epsilon_pos
    constant_pos := tube.cap.cap_constant_pos.trans_le hconstant
    carrier := tube.carrier
    cap := strongCapOfCap K ht tube.cap hcap hconstant
    tube := tube.tube
    cap_carrier := tube.cap_subset
    tube_carrier := tube.tube_subset
    carrier_eq_union := tube.carrier_eq_union
    connected := tube.connected
    attachment_side := tube.attachment_side
    attachment := {
      overlap_model := tube.attachment.overlap_model
      tube_tail := tube.attachment.tube_tail
      cap_tail := tube.attachment.cap_tail }
    tube_epsilon := htube
    strong_at := hstrong
    cap_connection := rfl
    carrier_eq_univ := hwhole }

end NoncompactKappa

end PoincareConjecture
