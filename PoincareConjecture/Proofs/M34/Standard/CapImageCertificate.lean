import PoincareConjecture.Proofs.M34.Standard.CapImageCertificateModel
import PoincareConjecture.Proofs.M34.Standard.CapImageCertificateBalls
import PoincareConjecture.Proofs.M34.Standard.CapImageTopologyBoundary
import PoincareConjecture.Proofs.M34.Standard.CapQuantitativeBoundsWitnesses
import PoincareConjecture.Proofs.M34.Standard.CapBoundaryNeckConfinement











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [MeasurableSpace X] [BorelSpace M] [BorelSpace X]
  [T3Space M] [T3Space X] [SecondCountableTopology M] [SecondCountableTopology X]
  [ConnectedSpace M] [ConnectedSpace X]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)





theorem exists_image_recut_cap
    {C : ℝ} (hC1 : 1 ≤ C) (hC : N.cap_constant ≤ C)
    (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x v v)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h) (hcomplete' : MetricComplete h)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (haccuracy : N.epsilon < epsilon)
    (hsource : N.carrier ⊆ e.source)
    (hcapture : closure (N.recutCarrier (2 / epsilon - N.epsilon⁻¹)) ⊆ e.source)
    (hupper : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 2 * g.tangentNorm x v)
    (hlower : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ 2 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v))
    (hscalar : ∀ x ∈ N.recutCarrier (2 / epsilon - N.epsilon⁻¹),
      |D.scalarCurvature (e x) - N.connection.scalarCurvature x| ≤ (2 * C)⁻¹)
    (hgradient : ∀ x ∈ N.recutCarrier (2 / epsilon - N.epsilon⁻¹),
      |scalarGradientNorm h D (e x) - scalarGradientNorm g N.connection x| ≤ 1)
    (hevolution : ∀ x ∈ N.recutCarrier (2 / epsilon - N.epsilon⁻¹),
      |(D.laplacian D.scalarCurvature (e x) + 2 * D.ricciNormSq (e x)) -
        (N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x)| ≤ 1)
    (hboundary : ∀ x ∈ N.boundary_sphere,
      (2 * N.end_neck.scale ^ 2)⁻¹ ≤ D.scalarCurvature (e x))
    (hscale : N.boundary_neck.scale ≤ (9 / 8 : ℝ) * N.end_neck.scale)
    (Eend Eboundary : EpsilonNeck h)
    (hend_epsilon : Eend.epsilon = epsilon)
    (hboundary_epsilon : Eboundary.epsilon = epsilon)
    (hend_connection : Eend.connection = D)
    (hboundary_connection : Eboundary.connection = D)
    (hend_carrier : Eend.carrier =
      e '' N.end_neck.region (-N.epsilon⁻¹) (2 / epsilon - N.epsilon⁻¹))
    (hboundary_carrier : Eboundary.carrier =
      e '' N.boundary_neck.region (-epsilon⁻¹) epsilon⁻¹)
    (hboundary_sphere : Eboundary.central_sphere = e '' N.boundary_sphere)
    (hend_negative : Eend.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) =
      e '' N.end_neck.region (-N.epsilon⁻¹) (1 / (2 * epsilon) - N.epsilon⁻¹)) :
    ∃ H : CapCertificate h, H.epsilon = epsilon ∧
      H.cap_constant = M34.capPersistenceConstant C (M34.capBallVolumeCoefficient C) ∧
      H.connection = D ∧ H.core = e '' N.core ∧
      H.carrier = e '' N.recutCarrier (2 / epsilon - N.epsilon⁻¹) ∧
      H.model_kind = N.model_kind := by
  classical
  let b := 2 / epsilon - N.epsilon⁻¹
  let K := M34.capPersistenceConstant C (M34.capBallVolumeCoefficient C)
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hK := M34.capPersistenceConstant_bounds hCpos.le
    (M34.capBallVolumeCoefficient_pos hCpos)
  have he8 : epsilon ≤ 1 / 8 := hsmall.trans (by norm_num)
  have hd8 : N.epsilon ≤ 1 / 8 := haccuracy.le.trans he8
  have hinv : epsilon⁻¹ < N.epsilon⁻¹ :=
    (inv_lt_inv₀ hepsilon N.epsilon_pos).mpr haccuracy
  have hb : -N.epsilon⁻¹ < b := by
    dsimp [b]
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hepsilon]
  have hb' : b < N.epsilon⁻¹ := by
    dsimp [b]
    rw [div_eq_mul_inv]
    linarith
  have hrecut : N.recutCarrier b ⊆ e.source :=
    (N.recutCarrier_subset_carrier b).trans hsource
  have hclosed : N.closed_core ⊆ e.source := fun x hx => hrecut (Or.inl hx)
  have hf1 : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source := hf.of_le (by simp)
  have hi1 : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target := hi.of_le (by simp)
  obtain ⟨hpositive, hdiameter, hratio, hvolume, hgrad, hevo⟩ :=
    N.image_recut_quantitative_bounds hC1 hC hK.2.1 ho hnormal h D e hb hb'
      hrecut hf1 hupper hscalar hgradient hevolution
  obtain ⟨r, hr⟩ := N.exists_image_recut_core_radii hC1 hC hcomplete hRic ho hnormal
    h D hcomplete' e hf1 hi1 hepsilon he8 haccuracy hsource hcapture hupper hlower
    hscalar hboundary
  obtain ⟨model⟩ := N.nonempty_image_recutModelEquivalence e hf hi hb hb' hrecut
  have hcore := N.image_core_compact_and_interior e hclosed
  have hboundary_subset : e '' N.boundary_sphere ⊆ e '' N.recutCarrier b := by
    apply image_mono
    exact fun _ hx => Or.inl (N.boundary_subset_closed_core hx)
  have hboundary_neck : Eboundary.carrier ⊆ e '' N.recutCarrier b := by
    rw [hboundary_carrier]
    exact image_mono (N.boundary_neck_region_subset_recutCarrier
      hepsilon haccuracy hd8 hscale)
  have hend_neck : Eend.carrier ⊆ e '' N.recutCarrier b := by
    rw [hend_carrier]
    exact image_mono (fun _ hx => Or.inr hx)
  have hnegative : e '' N.boundary_sphere ⊆
      closure (Eend.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
    rw [hend_negative]
    apply N.image_boundary_subset_inner_end_closure e (b := b)
    · linarith [div_pos (by norm_num : (0 : ℝ) < 1)
        (by positivity : 0 < 2 * epsilon)]
    · dsimp [b]
      have hid : 2 / epsilon = 4 * (1 / (2 * epsilon)) := by ring
      linarith [div_pos (by norm_num : (0 : ℝ) < 1)
        (by positivity : 0 < 2 * epsilon)]
    · exact hrecut
  let H : CapCertificate h := {
    epsilon := epsilon
    epsilon_pos := hepsilon
    epsilon_le_threshold := hsmall
    cap_constant := K
    cap_constant_pos := hK.1
    carrier := e '' N.recutCarrier b
    carrier_open := e.isOpen_image_of_subset_source (N.recutCarrier_isOpen hb hb') hrecut
    closed_core := e '' N.closed_core
    closed_core_compact := hcore.1
    core := e '' N.core
    core_nonempty := N.core_nonempty.image e
    core_eq_interior_closed_core := hcore.2
    puncture := N.puncture
    model_kind := N.model_kind
    model_equivalence := model
    connection := D
    end_neck := Eend
    end_neck_epsilon := hend_epsilon
    end_neck_subset := hend_neck
    end_neck_connection := hend_connection
    closed_core_eq_complement_end := by
      rw [hend_carrier]
      exact N.image_recut_complement_end_eq e hrecut
    boundary_sphere := e '' N.boundary_sphere
    boundary_neck := Eboundary
    boundary_neck_epsilon := hboundary_epsilon
    boundary_neck_subset := hboundary_neck
    boundary_neck_connection := hboundary_connection
    boundary_eq_neck_sphere := hboundary_sphere.symm
    boundary_eq_end_frontier := by
      rw [hend_carrier]
      exact N.image_boundary_eq_recut_end_frontier e hb hrecut
    boundary_subset_negative_end_closure := hnegative
    boundary_subset := hboundary_subset
    core_frontier_eq_boundary := N.image_core_frontier_eq e hclosed
    boundary_local_defining_function :=
      N.image_boundary_local_defining_function e hf hi hb hb' hrecut
    scalar_pos := hpositive
    intrinsic_diameter_bound := hdiameter
    scalar_ratio := hratio
    volume_bound := hvolume
    core_radius := r
    core_radius_pos := fun y hy => (hr y hy).1
    core_radius_eq := fun y hy => (hr y hy).2.1
    core_ball_subset := fun y hy => (hr y hy).2.2.2.1
    core_ball_compact := fun y hy => (hr y hy).2.2.1
    core_ball_volume_lower := ⟨M34.capBallVolumeCoefficient C, hK.2.2,
      fun y hy => (hr y hy).2.2.2.2⟩
    gradient_bound := hgrad
    laplacian_bound := hevo
  }
  exact ⟨H, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.CapCertificate
