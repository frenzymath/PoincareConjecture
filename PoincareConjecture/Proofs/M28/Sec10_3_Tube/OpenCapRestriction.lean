import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenCapInvariants
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenCapModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricBalls
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricIntrinsicDiameter
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricVolume

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.CapCertificate

open M28

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] {g : RiemannianMetric 3 M}

def restrictOpen (N : CapCertificate g) (V : TopologicalSpace.Opens M)
    (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) :
    CapCertificate (intrinsicOpenMetric g V) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let i : V → M := Subtype.val
  have hopen : IsOpenMap i := V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hcont : Continuous i := continuous_subtype_val
  have hclosedN : N.closed_core ⊆ N.carrier := by
    rw [N.closed_core_eq_complement_end]
    exact sdiff_subset
  have hcoreN : N.core ⊆ N.carrier := by
    rw [N.core_eq_interior_closed_core]
    exact interior_subset.trans hclosedN
  have hballV (y : V) (hy : (y : M) ∈ N.core) :
      g.ball (y : M) (N.core_radius y) ⊆ (V : Set M) :=
    subset_closure.trans ((N.core_ball_subset y hy).trans hNV)
  have hvolume (S : Set M) (hS : IsOpen S) (hSV : S ⊆ (V : Set M)) :
      calibratedMetricVolume (intrinsicOpenMetric g V) (i ⁻¹' S) =
        calibratedMetricVolume g S := by
    rw [intrinsicOpenMetric_calibratedVolume_apply g V (hS.preimage hcont).measurableSet]
    congr 1
    apply image_preimage_eq_of_subset
    intro x hx
    exact ⟨⟨x, hSV hx⟩, rfl⟩
  have hballOpen (y : M) (r : ℝ) : IsOpen (g.ball y r) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  exact {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_le_threshold := N.epsilon_le_threshold
    cap_constant := N.cap_constant
    cap_constant_pos := N.cap_constant_pos
    carrier := i ⁻¹' N.carrier
    carrier_open := N.carrier_open.preimage hcont
    closed_core := i ⁻¹' N.closed_core
    closed_core_compact :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
        N.closed_core_compact (by
          intro x hx
          exact ⟨⟨x, hNV (hclosedN hx)⟩, rfl⟩)
    core := i ⁻¹' N.core
    core_nonempty := by
      obtain ⟨x, hx⟩ := N.core_nonempty
      exact ⟨⟨x, hNV (hcoreN hx)⟩, hx⟩
    core_eq_interior_closed_core := by
      rw [N.core_eq_interior_closed_core]
      exact hopen.preimage_interior_eq_interior_preimage hcont _
    puncture := N.puncture
    model_kind := N.model_kind
    model_equivalence := N.model_equivalence.restrictOpen V hNV
    connection := DV
    end_neck := N.end_neck.restrictOpen V (N.end_neck_subset.trans hNV) DV
    end_neck_epsilon := N.end_neck_epsilon
    end_neck_subset := preimage_mono N.end_neck_subset
    end_neck_connection := rfl
    closed_core_eq_complement_end := by
      change i ⁻¹' N.closed_core = (i ⁻¹' N.carrier) \ (i ⁻¹' N.end_neck.carrier)
      rw [N.closed_core_eq_complement_end, preimage_sdiff]
    boundary_sphere := i ⁻¹' N.boundary_sphere
    boundary_neck := N.boundary_neck.restrictOpen V (N.boundary_neck_subset.trans hNV) DV
    boundary_neck_epsilon := N.boundary_neck_epsilon
    boundary_neck_subset := preimage_mono N.boundary_neck_subset
    boundary_neck_connection := rfl
    boundary_eq_neck_sphere := congrArg (i ⁻¹' ·) N.boundary_eq_neck_sphere
    boundary_eq_end_frontier := by
      change i ⁻¹' N.boundary_sphere = (i ⁻¹' N.carrier) ∩
        frontier (i ⁻¹' N.end_neck.carrier)
      rw [← hopen.preimage_frontier_eq_frontier_preimage hcont,
        ← preimage_inter, N.boundary_eq_end_frontier]
    boundary_subset_negative_end_closure := by
      change i ⁻¹' N.boundary_sphere ⊆
        closure (i ⁻¹' N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2))
      rw [← hopen.preimage_closure_eq_closure_preimage hcont]
      exact preimage_mono N.boundary_subset_negative_end_closure
    boundary_subset := preimage_mono N.boundary_subset
    core_frontier_eq_boundary := by
      rw [← hopen.preimage_frontier_eq_frontier_preimage hcont,
        N.core_frontier_eq_boundary]
    boundary_local_defining_function := by
      intro x hx
      obtain ⟨W, f, hW, hxW, hWN, hcore, hfx, hf, d, hd, hdf⟩ :=
        N.boundary_local_defining_function (x : M) hx
      refine ⟨i ⁻¹' W, f ∘ i, hW.preimage hcont, hxW,
        (fun _ hy => hWN hy), (fun y hy => hcore y hy), hfx,
        hf.comp (contMDiff_subtype_val (I := 𝓡 3) (U := V)).contMDiffOn
          (fun _ hy => hy), ?_⟩
      let L : TangentSpace (𝓡 3) x ≃L[ℝ] TangentSpace (𝓡 3) (x : M) :=
        (openSubtype_isLocalDiffeomorph V).mfderivToContinuousLinearEquiv (by simp) x
      refine ⟨L.symm d, ?_, ?_⟩
      · intro heq
        exact hd (by simpa only [L.apply_symm_apply, map_zero] using congrArg L heq)
      · have hfdiff := (hf.contMDiffAt (hW.mem_nhds hxW)).mdifferentiableAt (by simp)
        rw [mvfderiv_comp x hfdiff
          ((openSubtype_isLocalDiffeomorph V).contMDiff.mdifferentiable (by simp) x)]
        change mvfderiv (𝓡 3) f (x : M) (L (L.symm d)) ≠ 0
        simpa only [L.apply_symm_apply] using hdf
    scalar_pos := by
      intro x hx
      rw [intrinsicOpenMetric_scalarCurvature g V DV N.connection]
      exact N.scalar_pos x hx
    intrinsic_diameter_bound := by
      rw [intrinsicOpenMetric_intrinsicDiameter g V hNV,
        intrinsicOpenMetric_scalarCurvatureSupOn g V DV N.connection hNV]
      exact N.intrinsic_diameter_bound
    scalar_ratio := by
      obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
      refine ⟨b, hb, ?_⟩
      intro x hx y hy
      rw [intrinsicOpenMetric_scalarCurvature g V DV N.connection,
        intrinsicOpenMetric_scalarCurvature g V DV N.connection]
      exact hratio x hx y hy
    volume_bound := by
      rw [hvolume N.carrier N.carrier_open hNV,
        intrinsicOpenMetric_scalarCurvatureSupOn g V DV N.connection hNV]
      exact N.volume_bound
    core_radius := N.core_radius ∘ i
    core_radius_pos := fun y hy => N.core_radius_pos y hy
    core_radius_eq := by
      intro y hy
      change scalarCurvatureSupOn (intrinsicOpenMetric g V) DV
        ((intrinsicOpenMetric g V).ball y (N.core_radius (y : M))) =
          (N.core_radius (y : M))⁻¹ ^ 2
      rw [intrinsicOpenMetric_ball_eq_preimage g V y (hballV y hy),
        intrinsicOpenMetric_scalarCurvatureSupOn g V DV N.connection (hballV y hy)]
      exact N.core_radius_eq y hy
    core_ball_subset := by
      intro y hy
      exact (M28.CapCertificate.core_ball_intrinsicOpenMetric N V hNV y hy).2.2.2
    core_ball_compact := by
      intro y hy
      exact (M28.CapCertificate.core_ball_intrinsicOpenMetric N V hNV y hy).2.2.1
    core_ball_volume_lower := by
      obtain ⟨b, hb, hvol⟩ := N.core_ball_volume_lower
      refine ⟨b, hb, ?_⟩
      intro y hy
      change ENNReal.ofReal (b * N.core_radius (y : M) ^ 3) ≤
        calibratedMetricVolume (intrinsicOpenMetric g V)
          ((intrinsicOpenMetric g V).ball y (N.core_radius (y : M)))
      rw [intrinsicOpenMetric_ball_eq_preimage g V y (hballV y hy),
        hvolume _ (hballOpen _ _) (hballV y hy)]
      exact hvol y hy
    gradient_bound := by
      obtain ⟨b, hb, hgrad⟩ := N.gradient_bound
      refine ⟨b, hb, ?_⟩
      intro x hx
      rw [intrinsicOpenMetric_scalarGradientNorm g V DV N.connection,
        intrinsicOpenMetric_scalarCurvature g V DV N.connection]
      exact hgrad x hx
    laplacian_bound := by
      obtain ⟨b, hb, hlap⟩ := N.laplacian_bound
      refine ⟨b, hb, ?_⟩
      intro x hx
      rw [intrinsicOpenMetric_scalarLaplacian g V DV N.connection,
        intrinsicOpenMetric_ricciNormSq g V DV N.connection,
        intrinsicOpenMetric_scalarCurvature g V DV N.connection]
      exact hlap x hx }

@[simp] theorem restrictOpen_epsilon (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DV).epsilon = N.epsilon := rfl

@[simp] theorem restrictOpen_cap_constant (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DV).cap_constant = N.cap_constant := rfl

@[simp] theorem restrictOpen_connection (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DV).connection = DV := rfl

@[simp] theorem restrictOpen_carrier (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DV).carrier = (Subtype.val : V → M) ⁻¹' N.carrier := rfl

@[simp] theorem restrictOpen_core (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DV).core = (Subtype.val : V → M) ⁻¹' N.core := rfl

@[simp] theorem restrictOpen_closed_core (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DV).closed_core =
      (Subtype.val : V → M) ⁻¹' N.closed_core := rfl

@[simp] theorem restrictOpen_core_radius (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DV : LeviCivitaData (intrinsicOpenMetric g V)) (y : V) :
    (N.restrictOpen V hNV DV).core_radius y = N.core_radius (y : M) := rfl

end PoincareConjecture.CapCertificate
