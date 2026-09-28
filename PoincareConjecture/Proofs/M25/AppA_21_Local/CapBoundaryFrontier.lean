import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedChainFrontier

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.boundary_subset_or_positive_chain_frontier
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C C' : CapCertificate g) (D : BalancedNeckChain g C.epsilon)
    {a b : ℤ} (hshape : D.shape = ChainShape.finite a b)
    (hstart : D.neck a = C.end_neck)
    (hquarters : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
      closure ((D.neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
          (D.neck (i + 1)).carrier ∧
        closure ((D.neck (i + 1)).region
            (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier)
    (hmeet : ((C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)) ∩
      C'.boundary_sphere).Nonempty) :
    C'.boundary_sphere ⊆ C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∨
      ∃ z ∈ C'.boundary_neck.central_sphere,
        z ∈ frontier (C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)) ∧
        z ∉ C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
        z ∈ closure ((D.neck b).region 0 C.epsilon⁻¹) ∧
        z ∉ (D.neck b).carrier := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let V : Set M := C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)
  have hopen : IsOpen V := C.carrier_open.union
    (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)
  by_cases hsub : C'.boundary_sphere ⊆ V
  · exact Or.inl hsub
  · apply Or.inr
    have hS : IsPreconnected C'.boundary_sphere := by
      rw [C'.boundary_eq_neck_sphere]
      exact C'.boundary_neck.isConnected_central_sphere.isPreconnected
    have hmeet' : (C'.boundary_sphere ∩ V).Nonempty := by
      obtain ⟨x, hxV, hxS⟩ := hmeet
      exact ⟨x, hxS, hxV⟩
    have hescape : ¬ closure V ∩ C'.boundary_sphere ⊆ V := by
      intro hclose
      exact hsub (hS.subset_of_closure_inter_subset hopen hmeet' hclose)
    obtain ⟨z, hz, hzout⟩ := Set.not_subset.mp hescape
    have hzfront : z ∈ frontier V := by
      rw [hopen.frontier_eq]
      exact ⟨hz.1, hzout⟩
    have hactive (i : ℤ) : i ∈ D.shape.active ↔ i ∈ Icc a b := by
      rw [hshape]
      rfl
    have hab : a ≤ b := by
      obtain ⟨i, hi⟩ := D.active_nonempty
      have hiab := (hactive i).mp hi
      exact hiab.1.trans hiab.2
    have hb : b ∈ D.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
    refine ⟨z, ?_, hzfront, hzout, ?_, ?_⟩
    · simpa only [C'.boundary_eq_neck_sphere] using hz.2
    · exact C.frontier_union_finite_chain_subset_positive_closure
        D hshape hstart hquarters hzfront
    · intro hzlast
      exact hzout (Or.inr (mem_iUnion₂.mpr ⟨b, hb, hzlast⟩))

end PoincareConjecture
