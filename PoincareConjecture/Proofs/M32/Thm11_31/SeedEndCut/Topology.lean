import PoincareConjecture.Proofs.M32.Thm11_31.SeedEndCut.Escaping
import PoincareConjecture.Proofs.M32.Thm11_31.Topology
import PoincareConjecture.Proofs.M32.Neck.Spatial
import PoincareConjecture.Proofs.M32.Mathlib.ComponentFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32




private theorem neck_exists_component_avoiding_set
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (hN : N.IsSeparating)
    {P : Set M} (hP : IsPreconnected P) (havoid : Disjoint N.carrier P) :
    ∃ v ∈ N.carrier, v ∉ N.central_sphere ∧
      Disjoint (connectedComponentIn N.central_sphereᶜ v) P := by
  classical
  have hwide : (1 : ℝ) < N.epsilon⁻¹ :=
    (one_lt_inv₀ N.epsilon_pos).mpr (N.epsilon_lt_half.trans (by norm_num))
  let q := (N.coordinate_inverse N.center).1
  have hpoint (a : ℝ) (ha : |a| = 1) :
      N.coordinate_map (q, a) ∈ N.carrier ∧
        (N.coordinate_inverse (N.coordinate_map (q, a))).2 = a := by
    have habound := abs_le.mp ha.le
    have hdom : (q, a) ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨mem_univ _, by constructor <;> linarith [habound.1, habound.2]⟩
    let w : NeckDomain N.epsilon := (q, ⟨a, hdom.2⟩)
    have hw := (N.coordinate w).property
    rw [N.coordinate_map_eq] at hw
    have hi := N.coordinate_inverse_left w
    rw [N.coordinate_map_eq] at hi
    exact ⟨hw, congrArg Prod.snd hi⟩
  let vMinus := N.coordinate_map (q, (-1 : ℝ))
  let vPlus := N.coordinate_map (q, (1 : ℝ))
  have hm := hpoint (-1) (by norm_num)
  have hp := hpoint 1 (by norm_num)
  have hmregion : vMinus ∈ N.region (-N.epsilon⁻¹) 0 := by
    refine ⟨hm.1, ?_⟩
    rw [hm.2]
    constructor <;> linarith
  have hpregion : vPlus ∈ N.region 0 N.epsilon⁻¹ := by
    refine ⟨hp.1, ?_⟩
    rw [hp.2]
    exact ⟨zero_lt_one, hwide⟩
  have hmS : vMinus ∉ N.central_sphere := fun h => disjoint_left.mp
    (N.central_sphere_disjoint_region (-N.epsilon⁻¹) 0 (Or.inl le_rfl)) h hmregion
  have hpS : vPlus ∉ N.central_sphere := fun h => disjoint_left.mp
    (N.central_sphere_disjoint_region 0 N.epsilon⁻¹ (Or.inr le_rfl)) h hpregion
  let BMinus := connectedComponentIn N.central_sphereᶜ vMinus
  let BPlus := connectedComponentIn N.central_sphereᶜ vPlus
  have hnot : ¬ ((BMinus ∩ P).Nonempty ∧ (BPlus ∩ P).Nonempty) := by
    rintro ⟨hmP, hpP⟩
    let W := (BMinus ∪ P) ∪ BPlus
    have hW : IsPreconnected W := by
      have hleft : IsPreconnected (BMinus ∪ P) :=
        isPreconnected_connectedComponentIn.union' hmP hP
      apply hleft.union' ?_ isPreconnected_connectedComponentIn
      obtain ⟨x, hxB, hxP⟩ := hpP
      exact ⟨x, Or.inr hxP, hxB⟩
    have hvmW : vMinus ∈ W := Or.inl (Or.inl (mem_connectedComponentIn hmS))
    have hvpW : vPlus ∈ W := Or.inr (mem_connectedComponentIn hpS)
    have hcomponent : W ⊆ connectedComponent N.center := by
      rw [connectedComponent_eq (N.carrier_subset_connectedComponent hm.1)]
      exact hW.subset_connectedComponent hvmW
    have hWS : Disjoint W N.central_sphere := by
      apply disjoint_left.mpr
      rintro x ((hx | hx) | hx) hxS
      · exact connectedComponentIn_subset N.central_sphereᶜ vMinus hx hxS
      · exact disjoint_left.mp havoid (N.central_sphere_subset hxS) hx
      · exact connectedComponentIn_subset N.central_sphereᶜ vPlus hx hxS
    exact N.not_meets_both_halves_of_isSeparating hN hW hcomponent hWS
      ⟨⟨vMinus, hvmW, hmregion⟩, ⟨vPlus, hvpW, hpregion⟩⟩
  by_cases hmP : Disjoint BMinus P
  · exact ⟨vMinus, hm.1, hmS, hmP⟩
  · refine ⟨vPlus, hp.1, hpS, ?_⟩
    by_contra hpP
    exact hnot ⟨not_disjoint_iff_nonempty_inter.mp hmP,
      not_disjoint_iff_nonempty_inter.mp hpP⟩





theorem hornEndCut_exists_of_separating_neck_avoiding_prefix
    {F : GeneralizedRicciFlowData.{u}} {T epsilon delta : ℝ}
    {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)
    (N : TerminalStrongNeck E delta) (hhalf : delta < 1 / 2) (rho : ℝ)
    (hsep : (spatialNeck N hhalf).IsSeparating)
    {P : Set (E.extended.slice T).carrier} (hP : IsPreconnected P)
    (hboundary : horn.boundary_sphere ⊆ P)
    (hlow : horn.carrier ∩ {x | (E.extended.connection T).scalarCurvature x ≤
      rho⁻¹ ^ 2} ⊆ P)
    (hN : N.carrier ⊆ horn.carrier) (havoid : Disjoint N.carrier P)
    (hfill : ∀ K₀ : Set (E.extended.slice T).carrier, K₀ ⊆ horn.carrier →
      (interior K₀).Nonempty → frontier K₀ ⊆ N.central_sphere → ¬ IsCompact K₀) :
    ∃ cut : HornEndCut horn N rho, Disjoint cut.carrier P := by
  let : LocallyConnectedSpace (E.extended.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  let V := spatialNeck N hhalf
  obtain ⟨v, hvN, hvS, hvP⟩ := neck_exists_component_avoiding_set V hsep hP havoid
  let B := connectedComponentIn N.central_sphereᶜ v
  have hvB : v ∈ B := mem_connectedComponentIn hvS
  have hBhorn : B ⊆ horn.carrier := by
    apply horn_subset_carrier_of_isPreconnected horn isPreconnected_connectedComponentIn
      ⟨v, hvB, hN hvN⟩
    exact disjoint_left.mpr (fun x hx hxb => disjoint_left.mp hvP hx (hboundary hxb))
  have hrel : B = connectedComponentIn (horn.carrier \ N.central_sphere) v := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hvB
        (fun x hx => ⟨hBhorn hx, connectedComponentIn_subset N.central_sphereᶜ v hx⟩)
    · exact connectedComponentIn_mono v (fun _ hx => hx.2)
  have hescape (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) : ¬ B ⊆ K := by
    have hcompact : IsCompact (K ∩ horn.carrier) :=
      hK.inter_right (horn_isClosed_carrier horn)
    obtain ⟨y, hy, hyout⟩ := exists_connectedComponentIn_mem_not_mem_of_no_filling
      V.isClosed_central_sphere hfill hcompact inter_subset_right hvS
    intro hcontain
    exact hyout ⟨hcontain hy, hBhorn hy⟩
  obtain ⟨x, _hx, b, hb0, hb1, htail, _hescape, hunique⟩ :=
    horn_exists_unique_escaping_component horn N.central_sphere V.isCompact_central_sphere
  have hBeq : B = connectedComponentIn (horn.carrier \ N.central_sphere) x := by
    apply hrel.trans
    apply hunique v
    intro K hK
    rw [← hrel]
    exact hescape K hK
  let cut : HornEndCut horn N rho := {
    point := v
    point_mem := ⟨hN hvN, hvS⟩
    carrier := B
    component_eq := hrel
    tail_level := b
    tail_level_nonneg := hb0
    tail_level_lt_one := hb1
    contains_tail := by rw [hBeq]; exact htail
    escapes_compact := hescape
    disjoint_low_curvature := disjoint_left.mpr (fun y hy hR =>
      disjoint_left.mp hvP hy (hlow ⟨hBhorn hy, hR⟩)) }
  exact ⟨cut, hvP⟩

end PoincareConjecture.M32
