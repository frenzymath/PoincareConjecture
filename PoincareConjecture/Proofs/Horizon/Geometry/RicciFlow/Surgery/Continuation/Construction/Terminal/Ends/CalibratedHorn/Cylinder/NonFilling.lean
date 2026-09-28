import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Balanced
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.ChainTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.AnchoredChain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.ChainTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.CylinderFilling








set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain



theorem no_compact_filling_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ 1 / 200 → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ i ∈ C.shape.active, ∀ K : Set M, K ⊆ C.unionOpen →
          frontier K = (C.neck i).central_sphere → (interior K).Nonempty → ¬ IsCompact K := by
  intro M _ _ _ _ _ _ _ g ε C hε hsep i hi K hKU hfront hint hK
  obtain ⟨D, j, hj, c, hc, hD⟩ := cylinder_with_middle_of_epsilon_le C hε hsep
  obtain ⟨D₀, L, _, hLU, hefix, heU, heS⟩ :=
    C.central_sphere_smooth_transport_of_epsilon_le hε i hi j hj
  let e := D₀.toHomeomorph
  change e '' (C.unionOpen : Set M) = C.unionOpen at heU
  change e '' (C.neck i).central_sphere = (C.neck j).central_sphere at heS
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
