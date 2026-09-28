import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Twisted.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.Twisted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientKappaCapServices

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution 3 M}

noncomputable def bufferedUniformSlabCap
    (P : AncientKappaCapServices.{u}) (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
      (K.flow.connection t).scalarCurvature (C.cover (q, 0)) *
        (C.sphere.metric t).inner (a x)
          (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
            2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w) :
    CapCertificate (K.flow.metric t) := by
  let L := C.neckSpacing (t := t) (epsilon := epsilon) q
  let D := P.twistedCapConstant (epsilon / 2)
  have hL : 0 < L := C.neckSpacing_pos ht hε q
  have h2L : 0 < 2 * L := mul_pos (by norm_num) hL
  have h4L : 0 < 4 * L := mul_pos (by norm_num) hL
  have hhalf : epsilon < 1 / 2 := by linarith
  have hD := P.twistedCapConstant_bounds (half_pos hε)
  have hDpos : 0 < D := P.twistedCapConstant_pos (half_pos hε)
  let E := C.neckAtHeight ht hε hhalf q a ha (3 * L) (by change L ≤ 3 * L; linarith)
  let B := C.neckAtHeight ht hε hhalf q a ha (2 * L) (by change L ≤ 2 * L; linarith)
  have hE : E.terminal_neck.carrier = C.cover '' (univ ×ˢ Ioo (2 * L) (4 * L)) := by
    dsimp only [E]
    rw [C.neckAtHeight_carrier]
    congr 3 <;> dsimp [L, M27TwistedSphereLineFlowCertificate.neckSpacing] <;> ring
  have hB : B.terminal_neck.carrier = C.cover '' (univ ×ˢ Ioo L (3 * L)) := by
    dsimp only [B]
    rw [C.neckAtHeight_carrier]
    congr 3 <;> dsimp [L, M27TwistedSphereLineFlowCertificate.neckSpacing] <;> ring
  have hregion : E.terminal_neck.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) =
      C.cover '' (univ ×ˢ Ioo (2 * L) (5 * L / 2)) := by
    dsimp only [E]
    rw [C.neckAtHeight_region _ _ _ _ _ _ _ _ le_rfl (by
      have hi := inv_pos.mpr hε
      linarith)]
    congr 3 <;> dsimp [L, M27TwistedSphereLineFlowCertificate.neckSpacing] <;> ring
  have hboundary : frontier (C.slabCore (2 * L)) ⊆ interior (C.slabCore (4 * L)) :=
    (frontier_subset_iff_isClosed.mpr (C.isCompact_slabCore (2 * L)).isClosed).trans
      (C.slabCore_subset_interior_slabCore (by linarith))
  refine {
    epsilon := epsilon
    epsilon_pos := hε
    epsilon_le_threshold := hsmall
    cap_constant := D
    cap_constant_pos := hDpos
    carrier := interior (C.slabCore (4 * L))
    carrier_open := isOpen_interior
    closed_core := C.slabCore (2 * L)
    closed_core_compact := C.isCompact_slabCore (2 * L)
    core := interior (C.slabCore (2 * L))
    core_nonempty := C.nonempty_interior_slabCore h2L
    core_eq_interior_closed_core := rfl
    puncture := C.puncture
    model_kind := .puncturedProjective
    model_equivalence := ?_
    connection := K.flow.connection t
    end_neck := E.terminal_neck
    end_neck_epsilon := rfl
    end_neck_subset := ?_
    end_neck_connection := E.terminal_connection
    closed_core_eq_complement_end := ?_
    boundary_sphere := frontier (C.slabCore (2 * L))
    boundary_neck := B.terminal_neck
    boundary_neck_epsilon := rfl
    boundary_neck_subset := ?_
    boundary_neck_connection := B.terminal_connection
    boundary_eq_neck_sphere := ?_
    boundary_eq_end_frontier := ?_
    boundary_subset_negative_end_closure := ?_
    boundary_subset := hboundary
    core_frontier_eq_boundary := rfl
    boundary_local_defining_function := fun x hx =>
      C.slabCore_boundary_local_defining_function h2L isOpen_interior hx (hboundary hx)
    scalar_pos := fun x _ => C.scalarCurvature_pos ht x
    intrinsic_diameter_bound := C.bufferedCarrier_intrinsicDiameter_lt ht hε q hD.2.1
    scalar_ratio := ?_
    volume_bound := P.bufferedCarrier_volume_lt C ht hε q hD.2.2.1
    core_radius := fun y => (K.flow.connection t).scalarCurvature y ^ (-1 / 2 : ℝ)
    core_radius_pos := fun y _ => C.scalarRadius_pos ht y
    core_radius_eq := fun y _ => C.scalarRadius_ball_sup ht y
    core_ball_subset := fun _ hy =>
      C.buffered_core_scalarRadius_ball_subset_carrier ht hε hsmall q hy
    core_ball_compact := fun y _ => C.isCompact_closure_scalarRadius_ball ht y
    core_ball_volume_lower := ?_
    gradient_bound := ?_
    laplacian_bound := ?_ }
  · simpa only [C.interior_slabCore] using C.slabCapModel h4L
  · rw [hE]
    exact C.buffered_endNeck_subset_carrier hL
  · rw [hE]
    exact C.buffered_core_eq_carrier_diff_endNeck hL
  · rw [hB]
    exact C.buffered_boundaryNeck_subset_carrier hL
  · rw [C.frontier_slabCore h2L.le]
    exact (C.neckAtHeight_central_sphere ht hε hhalf q a ha (2 * L)
      (by change L ≤ 2 * L; linarith)).symm
  · rw [hE]
    exact (C.buffered_carrier_inter_frontier_endNeck hL).symm
  · rw [hregion]
    exact C.buffered_frontier_subset_negativeEnd_closure hL
  · refine ⟨1, by linarith [hD.1], fun x _ y _ => ?_⟩
    rw [one_mul, C.scalarCurvature_eq ht y x]
  · have hkappa := P.universal_noncollapsing.choose_spec.1
    have hnc := P.universal_noncollapsing.choose_spec.2 K
      (K.not_isRound_of_noncompact C.not_isCompact_univ)
    exact ⟨P.universal_noncollapsing.choose,
      (inv_lt_comm₀ hDpos hkappa).mpr hD.2.2.2,
      fun y _ => P.scalarRadius_volume_lower_bound_of_noncollapsed C hnc ht y⟩
  · refine ⟨0, hDpos, fun x _ => ?_⟩
    rw [C.scalarGradientNorm_eq_zero ht x, zero_mul]
  · exact ⟨2, by linarith [hD.1], fun x _ => P.scalarEvolution_bound C ht x⟩

theorem exists_buffered_cap_core_or_strong_neck
    (P : AncientKappaCapServices.{u}) (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) :
    ∃ A : CapCertificate (K.flow.metric t),
      A.epsilon = epsilon ∧ A.cap_constant = P.twistedCapConstant (epsilon / 2) ∧
      A.connection = K.flow.connection t ∧ IsCompact (closure A.carrier) ∧
      IsCompact (closure A.carrier \ A.core) ∧
      ∀ x : M, x ∉ A.core →
        ∃ N : StrongEvolvingNeck K t (epsilon / 2), N.center = x := by
  classical
  let q : UnitTwoSphere := Classical.arbitrary _
  obtain ⟨_, a, ha⟩ := C.exists_scalarNormalized_sphere ht (q, 0)
  let A := P.bufferedUniformSlabCap C ht hε hsmall q a ha
  have hcompact : IsCompact (closure A.carrier) :=
    C.isCompact_closure_interior_slabCore _
  refine ⟨A, rfl, rfl, rfl, hcompact, hcompact.diff isOpen_interior, ?_⟩
  intro x hx
  apply C.strong_necks_outside_interior_slabCore ht (half_pos hε) (by linarith)
    (C.cover (q, 0)) x
  change x ∉ interior (C.slabCore (C.neckSpacing (t := t) (epsilon := epsilon / 2) q))
  rw [C.neckSpacing_half]
  exact hx

end PoincareConjecture.AncientKappaCapServices
