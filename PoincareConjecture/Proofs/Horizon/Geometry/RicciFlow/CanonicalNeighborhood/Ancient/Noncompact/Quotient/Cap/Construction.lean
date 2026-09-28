import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Compression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  (C : M27TwistedSphereLineFlowCertificate K)
  (P : M26CanonicalNeighborhoodPredecessors.{u})
  {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
  (q : UnitTwoSphere)
  (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
  (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
    (K.flow.connection t).scalarCurvature (C.cover (q, 0)) *
      (C.sphere.metric t).inner (a x)
        (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
          2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)

noncomputable def slabCap {kappa D : ℝ} (hkappa : 0 < kappa)
    (hnc : AncientKappaNoncollapsed K.flow kappa)
    (hD : 3 < D ∧ twistedCapRadiusFactor epsilon < D ∧
      RiemannianMetric.euclideanUnitBallVolume 3 * twistedCapRadiusFactor epsilon ^ (3 : ℕ) < D ∧
      kappa⁻¹ < D) : CapCertificate (K.flow.metric t) := by
  let L := C.neckSpacing (t := t) (epsilon := epsilon) q
  have hL : 0 < L := C.neckSpacing_pos ht hε q
  have h3L : 0 < 3 * L := mul_pos (by norm_num) hL
  have hhalf : epsilon < 1 / 2 := by linarith
  have hDpos : 0 < D := by linarith [hD.1]
  let E := C.neckAtHeight ht hε hhalf q a ha (2 * L) (by change L ≤ 2 * L; linarith)
  let B := C.neckAtHeight ht hε hhalf q a ha L le_rfl
  have hE : E.terminal_neck.carrier = C.cover '' (univ ×ˢ Ioo L (3 * L)) := by
    dsimp only [E]
    rw [C.neckAtHeight_carrier]
    congr 3 <;> dsimp [L, neckSpacing] <;> ring
  have hB : B.terminal_neck.carrier = C.cover '' (univ ×ˢ Ioo 0 (2 * L)) := by
    dsimp only [B]
    rw [C.neckAtHeight_carrier]
    congr 3 <;> dsimp [L, neckSpacing] <;> ring
  have hregion : E.terminal_neck.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) =
      C.cover '' (univ ×ˢ Ioo L (3 * L / 2)) := by
    dsimp only [E]
    rw [C.neckAtHeight_region _ _ _ _ _ _ _ _ le_rfl (by
      have hi := inv_pos.mpr hε
      linarith)]
    congr 3 <;> dsimp [L, neckSpacing] <;> ring
  have hboundary : frontier (C.slabCore L) ⊆ interior (C.slabCore (3 * L)) :=
    ((frontier_subset_iff_isClosed.mpr (C.isCompact_slabCore L).isClosed).trans
      (C.slabCore_subset_capCarrier hL))
  refine {
    epsilon := epsilon
    epsilon_pos := hε
    epsilon_le_threshold := hsmall
    cap_constant := D
    cap_constant_pos := hDpos
    carrier := interior (C.slabCore (3 * L))
    carrier_open := isOpen_interior
    closed_core := C.slabCore L
    closed_core_compact := C.isCompact_slabCore L
    core := interior (C.slabCore L)
    core_nonempty := C.nonempty_interior_slabCore hL
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
    boundary_sphere := frontier (C.slabCore L)
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
      C.slabCore_boundary_local_defining_function hL isOpen_interior hx (hboundary hx)
    scalar_pos := fun x _ => C.scalarCurvature_pos ht x
    intrinsic_diameter_bound := C.capCarrier_intrinsicDiameter_lt ht hε q hD.2.1
    scalar_ratio := ?_
    volume_bound := C.capCarrier_volume_lt P ht hε q hD.2.2.1
    core_radius := fun y => (K.flow.connection t).scalarCurvature y ^ (-1 / 2 : ℝ)
    core_radius_pos := fun y _ => C.scalarRadius_pos ht y
    core_radius_eq := fun y _ => C.scalarRadius_ball_sup ht y
    core_ball_subset := fun _ hy => C.core_scalarRadius_ball_subset_capCarrier ht hε hsmall q hy
    core_ball_compact := fun y _ => C.isCompact_closure_scalarRadius_ball ht y
    core_ball_volume_lower := ?_
    gradient_bound := ?_
    laplacian_bound := ?_ }
  · simpa only [C.interior_slabCore] using C.slabCapModel h3L
  · rw [hE]
    exact C.endNeck_subset_capCarrier hL
  · rw [hE]
    exact C.slabCore_eq_capCarrier_diff_endNeck hL
  · rw [hB]
    exact C.boundaryNeck_subset_capCarrier hL
  · rw [C.frontier_slabCore hL.le]
    exact (C.neckAtHeight_central_sphere ht hε hhalf q a ha L le_rfl).symm
  · rw [hE]
    exact (C.capCarrier_inter_frontier_endNeck hL).symm
  · rw [hregion]
    exact C.frontier_slabCore_subset_negativeEnd_closure hL
  · refine ⟨1, by linarith [hD.1], fun x _ y _ => ?_⟩
    rw [one_mul, C.scalarCurvature_eq ht y x]
  · exact ⟨kappa, (inv_lt_comm₀ hDpos hkappa).mpr hD.2.2.2,
      fun y _ => C.scalarRadius_volume_lower_bound_of_noncollapsed P hnc ht y⟩
  · refine ⟨0, hDpos, fun x _ => ?_⟩
    rw [C.scalarGradientNorm_eq_zero ht x, zero_mul]
  · exact ⟨2, by linarith [hD.1], fun x _ => C.scalarEvolution_bound P ht x⟩

noncomputable def uniformSlabCap : CapCertificate (K.flow.metric t) :=
  C.slabCap P ht hε hsmall q a ha P.universal_noncollapsing.choose_spec.1
    (P.universal_noncollapsing.choose_spec.2 K
      (K.not_isRound_of_noncompact C.not_isCompact_univ))
    (twistedCapConstant_bounds P hε)

@[simp] theorem uniformSlabCap_epsilon :
    (C.uniformSlabCap P ht hε hsmall q a ha).epsilon = epsilon := rfl

@[simp] theorem uniformSlabCap_constant :
    (C.uniformSlabCap P ht hε hsmall q a ha).cap_constant = twistedCapConstant P epsilon := rfl

@[simp] theorem uniformSlabCap_carrier :
    (C.uniformSlabCap P ht hε hsmall q a ha).carrier =
      interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q)) := rfl

@[simp] theorem uniformSlabCap_closed_core :
    (C.uniformSlabCap P ht hε hsmall q a ha).closed_core =
      C.slabCore (C.neckSpacing (t := t) (epsilon := epsilon) q) := rfl

@[simp] theorem uniformSlabCap_core :
    (C.uniformSlabCap P ht hε hsmall q a ha).core =
      interior (C.slabCore (C.neckSpacing (t := t) (epsilon := epsilon) q)) := rfl

@[simp] theorem uniformSlabCap_connection :
    (C.uniformSlabCap P ht hε hsmall q a ha).connection = K.flow.connection t := rfl

theorem uniformSlabCap_end_neck :
    (C.uniformSlabCap P ht hε hsmall q a ha).end_neck =
      (C.neckAtHeight ht hε (by linarith) q a ha
        (2 * C.neckSpacing (t := t) (epsilon := epsilon) q)
        (by
          change C.neckSpacing (t := t) (epsilon := epsilon) q ≤ _
          have hL := C.neckSpacing_pos ht hε q
          linarith)).terminal_neck := rfl

theorem uniformSlabCap_end_neck_carrier :
    (C.uniformSlabCap P ht hε hsmall q a ha).end_neck.carrier =
      C.cover '' (univ ×ˢ Ioo (C.neckSpacing (t := t) (epsilon := epsilon) q)
        (3 * C.neckSpacing (t := t) (epsilon := epsilon) q)) := by
  rw [C.uniformSlabCap_end_neck, C.neckAtHeight_carrier]
  congr 3 <;> dsimp [neckSpacing] <;> ring

theorem uniformSlabCap_end_neck_region {l u : ℝ}
    (hl : -epsilon⁻¹ ≤ l) (hu : u ≤ epsilon⁻¹) :
    (C.uniformSlabCap P ht hε hsmall q a ha).end_neck.region l u =
      C.cover '' (univ ×ˢ Ioo
        (2 * C.neckSpacing (t := t) (epsilon := epsilon) q + l /
          Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))))
        (2 * C.neckSpacing (t := t) (epsilon := epsilon) q + u /
          Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))))) := by
  rw [C.uniformSlabCap_end_neck]
  exact C.neckAtHeight_region _ _ _ _ _ _ _ _ hl hu

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
