import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.AnchoredChain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.ChainTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.CylinderFilling








set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain



theorem exists_no_compact_filling_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ i ∈ C.shape.active, ∀ K : Set M, K ⊆ C.unionOpen →
          frontier K = (C.neck i).central_sphere → (interior K).Nonempty → ¬ IsCompact K := by
  obtain ⟨ε₁, hε₁, hsmall, hcylinder⟩ := exists_cylinder_with_middle_threshold.{u}
  obtain ⟨ε₂, hε₂, _, htransport⟩ := exists_central_sphere_transport_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε hsep i hi K hKU hfront hint hK
  obtain ⟨D, j, hj, c, hc, hD⟩ := hcylinder C (hε.trans (min_le_left _ _)) hsep
  obtain ⟨e, L, _, hLU, hefix, heU, heS⟩ :=
    htransport C (hε.trans (min_le_right _ _)) i hi j hj
  have hc' : c ∈ Ioo (-(C.neck j).epsilon⁻¹) (C.neck j).epsilon⁻¹ := by
    simpa only [C.epsilon_eq j hj] using hc
  obtain ⟨r, hr, hrN, hbound⟩ :=
    (C.neck j).exists_graph_collar (fun _ => c) continuous_const (fun _ => hc')
  let f := (C.neck j).graphTransport hr hrN (fun _ => c) continuous_const hbound
  have hsubj : (C.neck j).carrier ⊆ (C.unionOpen : Set M) :=
    fun _ hx => mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩
  have hfU : f '' (C.unionOpen : Set M) = C.unionOpen := by
    apply DeepHorn.image_eq_self_of_fixed_compl
    intro x hx
    exact (C.neck j).graphTransport_fixed hr hrN (fun _ => c) continuous_const hbound
      (fun h => hx (hsubj ((C.neck j).closedCollar_subset_carrier hrN h)))
  have hfS : f '' (C.neck j).central_sphere =
      range (fun q : UnitTwoSphere => (D (q, 0) : M)) := by
    rw [hD]
    exact (C.neck j).graphTransport_image_central_sphere hr hrN
      (fun _ => c) continuous_const hbound
  let a := e.trans f
  have haU : a '' (C.unionOpen : Set M) = C.unionOpen := by
    change (f ∘ e) '' (C.unionOpen : Set M) = _
    rw [image_comp, heU, hfU]
  have haS : a '' (C.neck i).central_sphere =
      (fun z : RoundCylinderSpace => (D z : M)) '' (univ ×ˢ {0}) := by
    change (f ∘ e) '' (C.neck i).central_sphere = _
    rw [image_comp, heS, hfS]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      exact ⟨q, by rw [show t = 0 from ht]⟩
  have haK : a '' K ⊆ (C.unionOpen : Set M) := by
    rw [← haU]
    exact image_mono hKU
  have haFront : frontier (a '' K) =
      (fun z : RoundCylinderSpace => (D z : M)) '' (univ ×ˢ {0}) := by
    rw [← a.image_frontier, hfront, haS]
  have haInt : (interior (a '' K)).Nonempty := by
    rw [← a.image_interior]
    exact hint.image a
  exact DeepHorn.not_isCompact_of_frontier_eq_cylinder_slice D.toHomeomorph
    haK haFront haInt (hK.image a.continuous)

end PoincareConjecture.BalancedNeckChain

namespace PoincareConjecture.StrongHorn



theorem exists_no_compact_filling_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T ε : ℝ}
        (E : GeneralizedFlowExtension F T),
        ∀ (A : RepairedNeckCapTopologyTheory.{u}) (hεpos : 0 < ε),
          ε ≤ ε₀ → ε ≤ A.epsilon₀ → ∀ (horn : StrongHorn E ε)
          (N : TerminalStrongNeck E ε), N.center ∈ horn.carrier →
          ∀ K : Set (E.extended.slice T).carrier, K ⊆ horn.carrier →
            frontier K = N.central_sphere → (interior K).Nonempty → ¬ IsCompact K := by
  obtain ⟨ε₁, hε₁, hsmall, hchain⟩ := exists_anchored_covering_chain.{u}
  obtain ⟨ε₂, hε₂, _, hno⟩ := BalancedNeckChain.exists_no_compact_filling_threshold.{u}
  obtain ⟨ε₃, hε₃, _, hsep⟩ := exists_boundary_sphere_transport.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro F T ε E A hεpos hε hA horn N hN K hKH hfront hint
  have hb : ε ≤ ε₁ ∧ ε ≤ ε₂ ∧ ε ≤ ε₃ := by simpa only [le_min_iff] using hε
  obtain ⟨hhalf, C, hCs, _, hzero, hCN, hcover⟩ :=
    hchain E A hεpos hb.1 hA horn N hN
  have hseparating : ∀ i ∈ C.shape.active, (C.neck i).IsSeparating := by
    intro i hi
    exact hCs.isSeparating
      (fun P hP => by
        obtain ⟨_, _, _, _, _, h⟩ := hsep E hεpos hb.2.2 horn P hP.1 hP.2
        exact h) hi
  apply hno C hb.2.1 hseparating 0 hzero K (hKH.trans hcover) ?_ hint
  rw [hCN]
  exact hfront

end PoincareConjecture.StrongHorn
