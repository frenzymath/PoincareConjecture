import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCuts
import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainFrontier

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem CapCertificate.frontier_union_finite_chain_subset_positive_closure
    (C : CapCertificate g) (D : BalancedNeckChain g C.epsilon)
    {a b : ℤ} (hshape : D.shape = ChainShape.finite a b)
    (hstart : D.neck a = C.end_neck)
    (hquarters : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
      closure ((D.neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
          (D.neck (i + 1)).carrier ∧
        closure ((D.neck (i + 1)).region
            (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) :
    frontier (C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)) ⊆
      closure ((D.neck b).region 0 C.epsilon⁻¹) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let U : Set M := ⋃ i ∈ D.shape.active, (D.neck i).carrier
  have hactive (i : ℤ) : i ∈ D.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    have hiab := (hactive i).mp hi
    exact hiab.1.trans hiab.2
  have ha : a ∈ D.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hNU : C.end_neck.carrier ⊆ U := by
    intro x hx
    refine mem_iUnion₂.mpr ⟨a, ha, ?_⟩
    simpa only [hstart] using hx
  have hL : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hzero : (0 : ℝ) ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr hL, hL⟩
  let K := C.carrier \ C.end_neck.region 0 C.epsilon⁻¹
  have hKclosed : IsClosed K := (C.isCompact_end_neck_lower_cut hzero).isClosed
  have hnegK : C.end_neck.region (-C.epsilon⁻¹) 0 ⊆ K := by
    intro x hx
    refine ⟨C.end_neck_subset hx.1, ?_⟩
    intro hxpos
    exact lt_asymm hx.2.2 hxpos.2.1
  have hneg : closure (C.end_neck.region (-C.epsilon⁻¹) 0) ⊆ C.carrier :=
    (closure_minimal hnegK hKclosed).trans (show K ⊆ C.carrier from sdiff_subset)
  have hcapfront : frontier C.carrier ⊆
      closure (C.end_neck.region 0 C.epsilon⁻¹) :=
    (C.end_neck_lower_cut_topology hzero).2.2.2.2.2.2
  have hpositiveU : C.end_neck.region 0 C.epsilon⁻¹ ⊆ U :=
    fun _ hx => hNU hx.1
  have hopenU : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open
  have hopenV : IsOpen (C.carrier ∪ U) := C.carrier_open.union hopenU
  change frontier (C.carrier ∪ U) ⊆ closure ((D.neck b).region 0 C.epsilon⁻¹)
  intro x hx
  rw [hopenV.frontier_eq] at hx
  have hxC : x ∉ C.carrier := fun hxC => hx.2 (Or.inl hxC)
  have hxU : x ∉ U := fun hxU => hx.2 (Or.inr hxU)
  have hxclosureU : x ∈ closure U := by
    have hxparts : x ∈ closure C.carrier ∪ closure U := by
      simpa only [closure_union] using hx.1
    rcases hxparts with hxcap | hxchain
    · have hxcapfront : x ∈ frontier C.carrier := by
        rw [C.carrier_open.frontier_eq]
        exact ⟨hxcap, hxC⟩
      exact closure_mono hpositiveU (hcapfront hxcapfront)
    · exact hxchain
  have hxfrontU : x ∈ frontier U := by
    rw [hopenU.frontier_eq]
    exact ⟨hxclosureU, hxU⟩
  rcases D.frontier_finite_union_subset_end_closures hshape hquarters hxfrontU with
      hxneg | hxpos
  · exact False.elim (hxC (hneg (by simpa only [hstart] using hxneg)))
  · exact hxpos

theorem CapCertificate.exists_positive_chain_frontier
    (C : CapCertificate g) (D : BalancedNeckChain g C.epsilon)
    {a b : ℤ} (hshape : D.shape = ChainShape.finite a b)
    (hstart : D.neck a = C.end_neck)
    (hquarters : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
      closure ((D.neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
          (D.neck (i + 1)).carrier ∧
        closure ((D.neck (i + 1)).region
            (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier)
    {X : Set M} (hX : IsPreconnected X)
    (hmeet : (X ∩ (C.carrier ∪
      (⋃ i ∈ D.shape.active, (D.neck i).carrier))).Nonempty)
    (hnot : ¬ X ⊆ C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)) :
    ∃ y ∈ X,
      y ∉ C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
      y ∈ closure ((D.neck b).region 0 C.epsilon⁻¹) := by
  classical
  let V : Set M := C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)
  have hopen : IsOpen V := C.carrier_open.union
    (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)
  have hescape : ¬ closure V ∩ X ⊆ V := by
    intro hsub
    exact hnot (hX.subset_of_closure_inter_subset hopen hmeet hsub)
  obtain ⟨y, hy, hyout⟩ := Set.not_subset.mp hescape
  have hyfront : y ∈ frontier V := by
    rw [hopen.frontier_eq]
    exact ⟨hy.1, hyout⟩
  exact ⟨y, hy.2, hyout,
    C.frontier_union_finite_chain_subset_positive_closure D hshape hstart hquarters hyfront⟩

end PoincareConjecture
