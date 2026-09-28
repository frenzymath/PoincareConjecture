import PoincareConjecture.Proofs.M47.BlowupControlsCapModelImage
import PoincareConjecture.Proofs.M47.BlowupControlsCapBoundaryImage
import PoincareConjecture.Proofs.M47.BlowupControlsCapImageRadii
import PoincareConjecture.Proofs.M47.BlowupControlsCapImageGeometry
import PoincareConjecture.Proofs.M47.BlowupControlsCapStrictAnalytics

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_cap_image_certificate_tolerance {g : RiemannianMetric 3 M}
    (N : CapCertificate g) (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ w : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x w w) :
    ∃ Lambda : ℝ, 1 < Lambda ∧ ∃ nu : ℝ, 0 < nu ∧
      ∀ {X : Type (max u v)} [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
        [MeasurableSpace X] [BorelSpace X] [T3Space X]
        [SecondCountableTopology X] [CompactSpace X]
        (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
        (e : OpenPartialHomeomorph M X),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target → N.carrier ⊆ e.source →
      (∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
        h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
          Lambda * g.tangentNorm x w) →
      (∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
        g.tangentNorm x w ≤
          Lambda * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w)) →
      (∀ x ∈ N.carrier,
        |D.scalarCurvature (e x) - N.connection.scalarCurvature x| ≤ nu ∧
        |scalarGradientNorm h D (e x) - scalarGradientNorm g N.connection x| ≤ nu ∧
        |(D.laplacian D.scalarCurvature (e x) + 2 * D.ricciNormSq (e x)) -
          (N.connection.laplacian N.connection.scalarCurvature x +
            2 * N.connection.ricciNormSq x)| ≤ nu) →
      ∀ Eend Eboundary : EpsilonNeck h,
        Eend.epsilon = N.epsilon → Eboundary.epsilon = N.epsilon →
        Eend.connection = D → Eboundary.connection = D →
        Eend.carrier = e '' N.end_neck.carrier →
        Eboundary.carrier = e '' N.boundary_neck.carrier →
        Eboundary.central_sphere = e '' N.boundary_sphere →
        Eend.coordinate_inverse = N.end_neck.coordinate_inverse ∘ e.symm →
        Eend.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) =
          e '' N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) →
      ∃ H : CapCertificate h,
        H.epsilon = N.epsilon ∧ H.cap_constant = N.cap_constant ∧ H.connection = D ∧
        H.core = e '' N.core ∧ H.closed_core = e '' N.closed_core ∧
        H.carrier = e '' N.carrier ∧ H.boundary_sphere = e '' N.boundary_sphere ∧
        H.model_kind = N.model_kind ∧ H.end_neck = Eend ∧ H.boundary_neck = Eboundary := by
  classical
  obtain ⟨LG, hLG, nuG, hnuG, hgeometry⟩ := exists_cap_image_geometric_tolerance N
  obtain ⟨LC, hLC, nuC, hnuC, bV, hbV, hcoreData⟩ :=
    exists_cap_image_core_data_tolerance N hcomplete hRic
  obtain ⟨nuA, hnuA, bR, bG, bE, hbR, hbG, hbE, hanalytic⟩ :=
    exists_cap_strict_analytic_tolerance N
  let Lambda := min LG LC
  let nu := min nuA (min nuG nuC)
  have hLambda : 1 < Lambda := lt_min hLG hLC
  have hnu : 0 < nu := lt_min hnuA (lt_min hnuG hnuC)
  have hnA : nu ≤ nuA := min_le_left _ _
  have hnG : nu ≤ nuG := (min_le_right _ _).trans (min_le_left _ _)
  have hnC : nu ≤ nuC := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Lambda, hLambda, nu, hnu, ?_⟩
  intro X _ _ _ _ _ _ _ _ h D e hf hi hsource hupper hlower hcompare Eend Eboundary
    hendEpsilon hboundaryEpsilon hendConnection hboundaryConnection hendCarrier
    hboundaryCarrier hboundarySphere hendInverse hendNegative
  let : T25Space X := T3Space.t25Space
  let : T2Space X := T25Space.t2Space
  have hf1 : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source := hf.of_le (by simp)
  have hi1 : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target := hi.of_le (by simp)
  have hupperG (x : M) (hx : x ∈ e.source) (w : TangentSpace (𝓡 3) x) :
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤ LG * g.tangentNorm x w :=
    (hupper x hx w).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  have hupperC (x : M) (hx : x ∈ e.source) (w : TangentSpace (𝓡 3) x) :
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤ LC * g.tangentNorm x w :=
    (hupper x hx w).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
  have hlowerC (x : M) (hx : x ∈ e.source) (w : TangentSpace (𝓡 3) x) :
      g.tangentNorm x w ≤ LC * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) :=
    (hlower x hx w).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
  obtain ⟨_, hdiameter, hvolume⟩ := hgeometry X h D e hf1 hsource hupperG
    (fun x hx => (hcompare x hx).1.trans hnG)
  obtain ⟨hpositive, hratio, hgradient, hevolution⟩ := hanalytic
    (fun x => D.scalarCurvature (e x)) (fun x => scalarGradientNorm h D (e x))
    (fun x => D.laplacian D.scalarCurvature (e x) + 2 * D.ricciNormSq (e x))
    (fun x hx => ⟨(hcompare x hx).1.trans hnA,
      (hcompare x hx).2.1.trans hnA, (hcompare x hx).2.2.trans hnA⟩)
  obtain ⟨r, hr⟩ := hcoreData h D e hf1 hi1 hsource hupperC hlowerC
    (fun x hx => by have h := (abs_le.mp (hcompare x hx).1).1; linarith)
    Eend hendConnection hendCarrier hendInverse
  obtain ⟨model⟩ := nonempty_cap_image_model N e hf hi hsource
  have hclosedSource : N.closed_core ⊆ e.source := by
    intro x hx
    rw [N.closed_core_eq_complement_end] at hx
    exact hsource hx.1
  have hcore := N.image_core_compact_and_interior e hclosedSource
  have hendSource := N.end_neck_subset.trans hsource
  have hnegative : e '' N.boundary_sphere ⊆
      closure (Eend.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) := by
    rw [hendNegative]
    rintro _ ⟨x, hx, rfl⟩
    exact ((e.continuousOn x (hsource (N.boundary_subset hx))).mono
      (fun _ hz => hendSource hz.1)).mem_closure_image
      (N.boundary_subset_negative_end_closure hx)
  let H : CapCertificate h := {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_le_threshold := N.epsilon_le_threshold
    cap_constant := N.cap_constant
    cap_constant_pos := N.cap_constant_pos
    carrier := e '' N.carrier
    carrier_open := e.isOpen_image_of_subset_source N.carrier_open hsource
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
    end_neck_epsilon := hendEpsilon
    end_neck_subset := by rw [hendCarrier]; exact image_mono N.end_neck_subset
    end_neck_connection := hendConnection
    closed_core_eq_complement_end := by
      rw [hendCarrier, N.closed_core_eq_complement_end]
      exact e.image_sdiff_eq_of_subset_source hsource hendSource
    boundary_sphere := e '' N.boundary_sphere
    boundary_neck := Eboundary
    boundary_neck_epsilon := hboundaryEpsilon
    boundary_neck_subset := by rw [hboundaryCarrier]; exact image_mono N.boundary_neck_subset
    boundary_neck_connection := hboundaryConnection
    boundary_eq_neck_sphere := hboundarySphere.symm
    boundary_eq_end_frontier := by
      rw [hendCarrier, N.boundary_eq_end_frontier]
      exact e.image_inter_frontier_eq_of_subset_source hsource hendSource
    boundary_subset_negative_end_closure := hnegative
    boundary_subset := image_mono N.boundary_subset
    core_frontier_eq_boundary := N.image_core_frontier_eq e hclosedSource
    boundary_local_defining_function := cap_image_boundary_local_defining_function N e hf hi hsource
    scalar_pos := by
      rintro _ ⟨x, hx, rfl⟩
      exact hpositive x hx
    intrinsic_diameter_bound := hdiameter
    scalar_ratio := by
      refine ⟨bR, hbR, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hratio x hx y hy
    volume_bound := hvolume
    core_radius := r
    core_radius_pos := fun y hy => (hr y hy).1
    core_radius_eq := fun y hy => (hr y hy).2.1
    core_ball_compact := fun y hy => (hr y hy).2.2.1
    core_ball_subset := fun y hy => (hr y hy).2.2.2.1
    core_ball_volume_lower := ⟨bV, hbV, fun y hy => (hr y hy).2.2.2.2⟩
    gradient_bound := by
      refine ⟨bG, hbG, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hgradient x hx
    laplacian_bound := by
      refine ⟨bE, hbE, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hevolution x hx
  }
  exact ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.M47
