import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.SmoothNeck










set_option autoImplicit false

open Function Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M E : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E]
  [IsManifold (𝓡 3) ∞ E] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)


noncomputable def ofLiftedCoordinate {p : E → M}
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) (e : E) (he : p e = N.center)
    (F : C(NeckDomain N.epsilon, E)) (hopen : IsOpenEmbedding F)
    (hF : p ∘ F = (fun z => (N.coordinate z : M)))
    (hcenter : ∃ y : UnitTwoSphere,
      F (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩) = e) :
    EpsilonNeck (g.pullbackOfLocalDiffeomorph p hp) := by
  let D := (g.pullbackOfLocalDiffeomorph p hp).leviCivitaData
  have hscalar : D.scalarCurvature e = N.connection.scalarCurvature N.center := by
    rw [D.scalarCurvature_eq_of_local_isometry N.connection isOpen_univ
      hp.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ e), he]
  have hmem : MapsTo p (range F) N.carrier := by
    rintro _ ⟨z, rfl⟩
    rw [show p (F z) = (N.coordinate z : M) from congr_fun hF z]
    exact (N.coordinate z).property
  have hinv : ∀ z : NeckDomain N.epsilon,
      N.coordinate_inverse (p (F z)) = (z.1, (z.2 : ℝ)) := by
    intro z
    rw [show p (F z) = (N.coordinate z : M) from congr_fun hF z]
    exact N.coordinate_inverse_left z
  refine {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := N.scale
    scale_pos := N.scale_pos
    center := e
    connection := D
    scalar_center_pos := hscalar.symm ▸ N.scalar_center_pos
    scale_eq_scalar := hscalar.symm ▸ N.scale_eq_scalar
    carrier := range F
    carrier_open := hopen.isOpen_range
    coordinate := hopen.isEmbedding.toHomeomorph
    coordinate_map := N.liftedCoordinateMap F e
    coordinate_map_eq := fun z => (N.liftedCoordinateMap_apply F e z).symm
    coordinate_map_smooth := N.liftedCoordinateMap_contMDiffOn hp F e hF
    coordinate_inverse := N.coordinate_inverse ∘ p
    coordinate_inverse_mem := fun x hx => N.coordinate_inverse_mem (p x) (hmem hx)
    coordinate_inverse_left := hinv
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth :=
      N.coordinate_inverse_smooth.comp hp.contMDiff.contMDiffOn hmem
    central_sphere := range (fun y : UnitTwoSphere =>
      F (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩))
    central_sphere_eq := ?_
    center_on_central_sphere := hcenter
    central_sphere_subset := ?_
    metric_comparison := N.liftedCoordinateMap_metricComparison hp F e hF }
  · rintro _ ⟨z, rfl⟩
    apply Subtype.ext
    change F _ = F z
    apply congr_arg F
    apply Prod.ext
    · exact congr_arg (fun z : UnitTwoSphere × ℝ => z.1) (hinv z)
    · exact Subtype.ext (congr_arg (fun z : UnitTwoSphere × ℝ => z.2) (hinv z))
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(y, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      exact N.liftedCoordinateMap_apply F e
        (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩)
    · rintro ⟨⟨y, t⟩, ⟨_, ht⟩, rfl⟩
      have ht' : t = 0 := ht
      subst t
      exact ⟨y, (N.liftedCoordinateMap_apply F e _).symm⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.NeckOnlyCover

variable {M E : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E]
  [IsManifold (𝓡 3) ∞ E] {g : RiemannianMetric 3 M}



theorem exists_lifted_neck_with_coordinates (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) (e : E) :
    ∃ L : EpsilonNeck (g.pullbackOfLocalDiffeomorph p hp),
      L.epsilon = H.epsilon ∧ L.center = e ∧
        ∃ N ∈ H.necks, p '' L.central_sphere = N.central_sphere ∧
          p '' L.carrier = N.carrier ∧ InjOn p L.carrier ∧
            ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-L.epsilon⁻¹) L.epsilon⁻¹ →
              p (L.coordinate_map z) = N.coordinate_map z := by
  obtain ⟨N, hN, hc, F, hF, hopen, hcenter⟩ :=
    H.exists_lifted_centered_coordinate hwhole hcover e
  refine ⟨N.ofLiftedCoordinate hp e hc.symm F hopen hF hcenter,
    H.neck_epsilon N hN, rfl, N, hN, ?_⟩
  exact ⟨N.image_lifted_central_sphere hF, N.image_lifted_coordinate hF,
    N.injOn_projection_lifted_coordinate hF,
    fun _ hz => N.projection_liftedCoordinateMap F e hF hz⟩



theorem exists_lifted_neck_with_sheet (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) (e : E) :
    ∃ L : EpsilonNeck (g.pullbackOfLocalDiffeomorph p hp),
      L.epsilon = H.epsilon ∧ L.center = e ∧
        ∃ N ∈ H.necks, p '' L.central_sphere = N.central_sphere ∧
          p '' L.carrier = N.carrier ∧ InjOn p L.carrier := by
  obtain ⟨L, hε, hc, N, hN, hs, hu, hinj, _⟩ :=
    H.exists_lifted_neck_with_coordinates hwhole hcover hp e
  exact ⟨L, hε, hc, N, hN, hs, hu, hinj⟩



theorem exists_lifted_neck (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) (e : E) :
    ∃ L : EpsilonNeck (g.pullbackOfLocalDiffeomorph p hp),
      L.epsilon = H.epsilon ∧ L.center = e ∧
        ∃ N ∈ H.necks, p '' L.central_sphere = N.central_sphere := by
  obtain ⟨L, hε, hc, N, hN, hs, _⟩ :=
    H.exists_lifted_neck_with_sheet hwhole hcover hp e
  exact ⟨L, hε, hc, N, hN, hs⟩



theorem exists_lifted_cover_with_coordinate_sheets [ConnectedSpace E]
    (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) :
    ∃ H' : NeckOnlyCover (g.pullbackOfLocalDiffeomorph p hp),
      H'.X = univ ∧ H'.epsilon = H.epsilon ∧
        ∀ L ∈ H'.necks, ∃ N ∈ H.necks,
          p '' L.central_sphere = N.central_sphere ∧
            p '' L.carrier = N.carrier ∧ InjOn p L.carrier ∧
              ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-L.epsilon⁻¹) L.epsilon⁻¹ →
                p (L.coordinate_map z) = N.coordinate_map z := by
  classical
  choose L hε hc hs using H.exists_lifted_neck_with_coordinates hwhole hcover hp
  exact ⟨{
    epsilon := H.epsilon
    epsilon_pos := H.epsilon_pos
    epsilon_threshold := H.epsilon_threshold
    epsilon_threshold_pos := H.epsilon_threshold_pos
    epsilon_threshold_le_one_two_hundred := H.epsilon_threshold_le_one_two_hundred
    epsilon_le_threshold := H.epsilon_le_threshold
    X := univ
    connected_X := isConnected_univ
    necks := range L
    pointwise_center_cover := fun e _ => ⟨L e, mem_range_self e, hc e⟩
    neck_epsilon := by rintro _ ⟨e, rfl⟩; exact hε e }, rfl, rfl,
    by rintro _ ⟨e, rfl⟩; exact hs e⟩



theorem exists_lifted_cover_with_sheets [ConnectedSpace E]
    (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) :
    ∃ H' : NeckOnlyCover (g.pullbackOfLocalDiffeomorph p hp),
      H'.X = univ ∧ H'.epsilon = H.epsilon ∧
        ∀ L ∈ H'.necks, ∃ N ∈ H.necks,
          p '' L.central_sphere = N.central_sphere ∧
            p '' L.carrier = N.carrier ∧ InjOn p L.carrier := by
  obtain ⟨H', hX, hε, hsheet⟩ :=
    H.exists_lifted_cover_with_coordinate_sheets hwhole hcover hp
  refine ⟨H', hX, hε, fun L hL => ?_⟩
  obtain ⟨N, hN, hs, hu, hinj, _⟩ := hsheet L hL
  exact ⟨N, hN, hs, hu, hinj⟩


theorem exists_lifted_cover [ConnectedSpace E]
    (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) :
    ∃ H' : NeckOnlyCover (g.pullbackOfLocalDiffeomorph p hp),
      H'.X = univ ∧ H'.epsilon = H.epsilon ∧
        ∀ L ∈ H'.necks, ∃ N ∈ H.necks, p '' L.central_sphere = N.central_sphere := by
  obtain ⟨H', hX, hε, hsheet⟩ := H.exists_lifted_cover_with_sheets hwhole hcover hp
  refine ⟨H', hX, hε, fun L hL => ?_⟩
  obtain ⟨N, hN, hs, _⟩ := hsheet L hL
  exact ⟨N, hN, hs⟩



theorem exists_separating_lifted_cover_with_sheets [SimplyConnectedSpace E] [T2Space E]
    [T3Space E] [MeasurableSpace E] [BorelSpace E]
    (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) :
    ∃ H' : NeckOnlyCover (g.pullbackOfLocalDiffeomorph p hp),
      H'.X = univ ∧ H'.epsilon = H.epsilon ∧
        (∀ L ∈ H'.necks, L.IsSeparating) ∧
        ∀ L ∈ H'.necks, ∃ N ∈ H.necks,
          p '' L.central_sphere = N.central_sphere ∧
            p '' L.carrier = N.carrier ∧ InjOn p L.carrier := by
  obtain ⟨H', hwhole', hε, hs⟩ := H.exists_lifted_cover_with_sheets hwhole hcover hp
  refine ⟨H', hwhole', hε, ?_, hs⟩
  intro L _
  exact L.isSeparating_iff_not_isNonseparating.mpr
    (fun hL => L.not_simplyConnectedSpace_of_isNonseparating hL inferInstance)


theorem exists_separating_lifted_cover [SimplyConnectedSpace E] [T2Space E]
    [T3Space E] [MeasurableSpace E] [BorelSpace E]
    (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) :
    ∃ H' : NeckOnlyCover (g.pullbackOfLocalDiffeomorph p hp),
      H'.X = univ ∧ H'.epsilon = H.epsilon ∧
        (∀ L ∈ H'.necks, L.IsSeparating) ∧
        ∀ L ∈ H'.necks, ∃ N ∈ H.necks, p '' L.central_sphere = N.central_sphere := by
  obtain ⟨H', hX, hε, hsep, hsheet⟩ :=
    H.exists_separating_lifted_cover_with_sheets hwhole hcover hp
  refine ⟨H', hX, hε, hsep, fun L hL => ?_⟩
  obtain ⟨N, hN, hs, _⟩ := hsheet L hL
  exact ⟨N, hN, hs⟩

end PoincareConjecture.NeckOnlyCover
