import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Expansion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Placement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Restriction











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {delta D R : ℝ}


structure SoulCapGeometry (G : SoulNeckRegion K S delta D R) (epsilon : ℝ) where
  epsilon_pos : 0 < epsilon
  source : EpsilonNeck (K.flow.metric 0)
  source_epsilon : source.epsilon = delta
  source_carrier : source.carrier = G.neck.terminal_neck.carrier
  source_sphere : source.central_sphere = G.neck.terminal_neck.central_sphere
  source_connection : source.connection = K.flow.connection 0
  source_scale : source.scale = G.neck.terminal_neck.scale
  source_height : ∀ y ∈ source.carrier,
    y ∈ closure G.inside ↔ (source.coordinate_inverse y).2 ≤ 0
  a : ℝ
  b : ℝ
  a_bounds : a ∈ Icc (4 / 5) (6 / 5)
  b_bounds : b ∈ Icc (4 / 5) (6 / 5)
  outer_height_lt : 2 * a * epsilon⁻¹ < source.epsilon⁻¹
  boundary : EpsilonNeck (K.flow.metric 0)
  endNeck : EpsilonNeck (K.flow.metric 0)
  boundary_epsilon : boundary.epsilon = epsilon
  end_epsilon : endNeck.epsilon = epsilon
  boundary_connection : boundary.connection = K.flow.connection 0
  end_connection : endNeck.connection = K.flow.connection 0
  boundary_carrier : boundary.carrier = source.region (-b * epsilon⁻¹) (b * epsilon⁻¹)
  end_carrier : endNeck.carrier = source.region 0 (2 * a * epsilon⁻¹)
  boundary_sphere : boundary.central_sphere = source.central_sphere
  end_coordinate_inverse : endNeck.coordinate_inverse =
    RoundCylinderAffine.inverseSpace a (a * epsilon⁻¹) ∘ source.coordinate_inverse

namespace SoulCapGeometry

variable {G : SoulNeckRegion K S delta D R} {epsilon : ℝ} (H : SoulCapGeometry G epsilon)

def carrier : Set M := G.inside ∪ H.source.region (-H.source.epsilon⁻¹) (2 * H.a * epsilon⁻¹)

theorem outer_height_pos : 0 < 2 * H.a * epsilon⁻¹ := by
  have ha : 0 < H.a := by linarith [H.a_bounds.1]
  exact mul_pos (mul_pos (by norm_num) ha) (inv_pos.mpr H.epsilon_pos)

theorem carrier_subset : H.carrier ⊆ G.inside ∪ G.neck.terminal_neck.carrier := by
  rintro x (hx | hx)
  · exact Or.inl hx
  · exact Or.inr (H.source_carrier ▸ hx.1)

theorem carrier_open : IsOpen H.carrier := G.inside_open.union (H.source.isOpen_region _ _)

theorem closure_inside_subset : closure G.inside ⊆ H.carrier := by
  obtain ⟨F, hF, hsub, _⟩ := G.exists_side_expansion H.source H.source_sphere
    H.source_height H.outer_height_pos H.outer_height_lt
  change closure G.inside ⊆ G.inside ∪ H.source.region _ _
  exact hF ▸ hsub

theorem carrier_closure_compact : IsCompact (closure H.carrier) := by
  obtain ⟨F, hF, _, _⟩ := G.exists_side_expansion H.source H.source_sphere
    H.source_height H.outer_height_pos H.outer_height_lt
  change IsCompact (closure (G.inside ∪ H.source.region _ _))
  rw [← hF]
  have hcl : F '' closure G.inside = closure (F '' G.inside) :=
    F.toHomeomorph.image_closure _
  rw [← hcl]
  exact G.compact_side.image F.continuous

theorem boundary_subset : H.boundary.carrier ⊆ H.carrier := by
  intro x hx
  have hxN := H.boundary_carrier ▸ hx
  apply Or.inr
  refine ⟨hxN.1, (H.source.coordinate_inverse_mem x hxN.1).2.1, ?_⟩
  have hb : H.b < 2 * H.a := by linarith [H.a_bounds.1, H.b_bounds.2]
  exact hxN.2.2.trans (mul_lt_mul_of_pos_right hb (inv_pos.mpr H.epsilon_pos))

theorem end_subset : H.endNeck.carrier ⊆ H.carrier := by
  intro x hx
  have hxN := H.end_carrier ▸ hx
  exact Or.inr ⟨hxN.1, (H.source.coordinate_inverse_mem x hxN.1).2.1, hxN.2.2⟩

theorem nonempty_model (p : RealProjectiveThree) :
    Nonempty (CapModelEquivalence .euclidean p H.carrier) :=
  G.nonempty_expanded_side_capModel H.source H.source_sphere H.source_height
    H.outer_height_pos H.outer_height_lt p

theorem strong_outside_core (hle : delta ≤ epsilon) (hhalf : epsilon < 1 / 2)
    (x : M) (hx : x ∉ G.inside) : ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  obtain ⟨N, hN⟩ := G.strong_outside_core x (fun hi => hx (interior_subset hi).1)
  exact ⟨restrictStrongNeck N hle hhalf, hN⟩

end SoulCapGeometry



theorem exists_soulCapGeometry_threshold {epsilon : ℝ}
    (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 200) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ epsilon / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        {K : AncientKappaSolution 3 M}
        {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {delta D R : ℝ},
        (G : SoulNeckRegion K S delta D R) → delta ≤ delta₀ →
          Nonempty (SoulCapGeometry G epsilon) := by
  obtain ⟨delta₀, hd, hde, hnecks⟩ := exists_attaching_necks_threshold.{u} he hesmall
  refine ⟨delta₀, hd, hde, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S delta D R G hdelta
  obtain ⟨N, hNe, hNc, hNs, hND, hNscale, hheight⟩ := G.exists_outward_height_neck
  obtain ⟨q⟩ : Nonempty UnitTwoSphere := inferInstance
  obtain ⟨a, b, B, E, ha, hb, hBe, hEe, hBD, hED, _, _, hBc, hEc, hBs, _, hEi⟩ :=
    hnecks N (hNe.trans_le hdelta) q
  have hi : (epsilon / 4)⁻¹ = 4 * epsilon⁻¹ := by field_simp
  have hNinv : 4 * epsilon⁻¹ ≤ N.epsilon⁻¹ := by
    rw [← hi]
    exact (inv_le_inv₀ (by positivity) N.epsilon_pos).mpr
      (hNe.trans_le (hdelta.trans hde))
  have houter : 2 * a * epsilon⁻¹ < N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right ha.2 (inv_pos.mpr he).le
    linarith [inv_pos.mpr he]
  exact ⟨{ epsilon_pos := he
           source := N
           source_epsilon := hNe
           source_carrier := hNc
           source_sphere := hNs
           source_connection := hND
           source_scale := hNscale
           source_height := hheight
           a := a
           b := b
           a_bounds := ha
           b_bounds := hb
           outer_height_lt := houter
           boundary := B
           endNeck := E
           boundary_epsilon := hBe
           end_epsilon := hEe
           boundary_connection := hBD.trans hND
           end_connection := hED.trans hND
           boundary_carrier := hBc
           end_carrier := hEc
           boundary_sphere := hBs
           end_coordinate_inverse := hEi }⟩

end PoincareConjecture.NoncompactKappa.Positive
