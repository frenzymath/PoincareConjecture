import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.ContainedCollar
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30




theorem exists_precompact_neck_side_of_central_sphere_subset_chart
    {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {U : Set M} (hU : IsOpen U)
    (h : U ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hS : N.central_sphere ⊆ U) :
    ∃ A : Set M,
      IsOpen A ∧ IsCompact (closure A) ∧ closure A ⊆ U ∧
      frontier A = N.central_sphere ∧
      (N.region (-N.epsilon⁻¹) 0 ⊆ A ∨
        N.region 0 N.epsilon⁻¹ ⊆ A) := by
  classical
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have heps : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  obtain ⟨r, hr, hcollar⟩ := N.exists_slice_collar_in_open
    (s := 0) ⟨neg_lt_zero.mpr heps, heps⟩ U hU (by
      intro q
      apply hS
      rw [N.central_sphere_eq]
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩)
  have hcollar' (q : UnitTwoSphere) (t : ℝ) (ht : |t| < r) :
      t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
        N.coordinate_map (q, t) ∈ U := by
    simpa only [zero_add] using hcollar q t ht
  let D : Set RoundCylinderSpace := univ ×ˢ Ioo (-r) r
  have hD : D ⊆ N.coordinatePartialHomeomorph.source := by
    intro z hz
    exact ⟨mem_univ _, (hcollar' z.1 z.2 (abs_lt.mpr hz.2)).1⟩
  let V : Set M := N.coordinate_map '' D
  have hV : IsOpen V :=
    N.coordinatePartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) hD
  have hVU : V ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact (hcollar' z.1 z.2 (abs_lt.mpr hz.2)).2
  let eD : (UnitTwoSphere × Ioo (-r) r) ≃ₜ D :=
    ((Homeomorph.Set.univ UnitTwoSphere).symm.prodCongr
      (Homeomorph.refl (Ioo (-r) r))).trans
        (Homeomorph.Set.prod (univ : Set UnitTwoSphere) (Ioo (-r) r)).symm
  let eM : (UnitTwoSphere × Ioo (-r) r) ≃ₜ V :=
    eD.trans (N.coordinatePartialHomeomorph.homeomorphOfImageSubsetSource hD rfl)
  let fU : UnitTwoSphere × Ioo (-r) r → U :=
    fun z => ⟨(eM z : M), hVU (eM z).property⟩
  have hfUc : Continuous fU :=
    (continuous_subtype_val.comp eM.continuous).subtype_mk _
  have hfUo : IsOpenMap fU :=
    (hV.isOpenMap_subtype_val.comp eM.isOpenMap).subtype_mk _
  have hfUi : Function.Injective fU := by
    intro z w hzw
    apply eM.injective
    apply Subtype.ext
    exact congrArg (fun x : U => (x : M)) hzw
  let f : UnitTwoSphere × Ioo (-r) r → EuclideanSpace ℝ (Fin 3) := h ∘ fU
  have hf : Topology.IsOpenEmbedding f :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (h.continuous.comp hfUc) (h.injective.comp hfUi) (h.isOpenMap.comp hfUo)
  let e : (UnitTwoSphere × Ioo (-r) r) ≃ₜ range f := hf.isEmbedding.toHomeomorph
  let j : EuclideanSpace ℝ (Fin 3) → M := fun z => (h.symm z : M)
  have hjc : Continuous j := continuous_subtype_val.comp h.symm.continuous
  have hji : Function.Injective j := Subtype.val_injective.comp h.symm.injective
  have hjo : IsOpenMap j := hU.isOpenMap_subtype_val.comp h.symm.isOpenMap
  have hemap (z : UnitTwoSphere × Ioo (-r) r) :
      j (e z : EuclideanSpace ℝ (Fin 3)) = N.coordinate_map (z.1, (z.2 : ℝ)) := by
    change (h.symm (h (fU z)) : M) = _
    rw [h.symm_apply_apply]
    rfl
  let S : Set (EuclideanSpace ℝ (Fin 3)) :=
    range (fun q : UnitTwoSphere =>
      (e (q, ⟨0, neg_lt_zero.mpr hr, hr⟩) : EuclideanSpace ℝ (Fin 3)))
  have hSc : IsCompact S := isCompact_range
    ((continuous_subtype_val.comp e.continuous).comp
      (continuous_id.prodMk continuous_const))
  have hjS : j '' S = N.central_sphere := by
    rw [N.central_sphere_eq]
    ext x
    constructor
    · rintro ⟨z, ⟨q, rfl⟩, rfl⟩
      rw [hemap]
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨e (q, ⟨0, neg_lt_zero.mpr hr, hr⟩), ⟨q, rfl⟩, hemap _⟩
  obtain ⟨A₀, B₀, hA₀, hB₀, _hAc, _hBc, hdisj, hcover,
    hfrontA₀, hfrontB₀, hneg, hpos⟩ :=
    Poincare.Topology.exists_collar_complementary_regions hr hf.isOpen_range e
  have hbounded :=
    Poincare.Topology.bounded_side_of_compact_complement_partition_euclidean_three
      hSc hA₀ hB₀ hdisj hcover
  obtain ⟨C, hCopen, hCc, hCfront, hCside⟩ :
      ∃ C : Set (EuclideanSpace ℝ (Fin 3)),
        IsOpen C ∧ IsCompact (closure C) ∧ frontier C = S ∧
        ((fun z => (e z : EuclideanSpace ℝ (Fin 3))) ''
            {z | (z.2 : ℝ) < 0} ⊆ C ∨
          (fun z => (e z : EuclideanSpace ℝ (Fin 3))) ''
            {z | 0 < (z.2 : ℝ)} ⊆ C) := by
    rcases hbounded with ⟨hAb, _⟩ | ⟨hBb, _⟩
    · exact ⟨A₀, hA₀, hAb.isCompact_closure, hfrontA₀, Or.inl hneg⟩
    · exact ⟨B₀, hB₀, hBb.isCompact_closure, hfrontB₀, Or.inr hpos⟩
  let A : Set M := j '' C
  have hA : IsOpen A := hjo C hCopen
  have hclosure : j '' closure C = closure A :=
    image_closure_of_isCompact hCc hjc.continuousOn
  have hAc : IsCompact (closure A) := hclosure ▸ hCc.image hjc
  have hAU : closure A ⊆ U := by
    rw [← hclosure]
    rintro x ⟨z, _, rfl⟩
    exact (h.symm z).property
  have hpre : j ⁻¹' frontier A = frontier C := by
    rw [hjo.preimage_frontier_eq_frontier_preimage hjc,
      show j ⁻¹' A = C from preimage_image_eq C hji]
  have hfront : frontier A = N.central_sphere := by
    rw [← hjS, ← hCfront]
    apply Subset.antisymm
    · intro x hx
      have hxU : x ∈ U := hAU (frontier_subset_closure hx)
      let z := h ⟨x, hxU⟩
      have hz : j z = x := by
        change (h.symm (h ⟨x, hxU⟩) : M) = x
        rw [h.symm_apply_apply]
      refine ⟨z, ?_, hz⟩
      rw [← hpre]
      change j z ∈ frontier A
      rwa [hz]
    · rintro x ⟨z, hz, rfl⟩
      exact show z ∈ j ⁻¹' frontier A from hpre.symm ▸ hz
  refine ⟨A, hA, hAc, hAU, hfront, ?_⟩
  let q : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
  rcases hCside with hnegative | hpositive
  · left
    have hconn : IsPreconnected (N.region (-N.epsilon⁻¹) 0) := by
      rw [← N.coordinate_negative_image]
      exact (Poincare.Topology.isConnected_collar_negative heps N.coordinate).isPreconnected
    have havoid : Disjoint (N.region (-N.epsilon⁻¹) 0) (frontier A) := by
      rw [hfront]
      exact (N.central_sphere_disjoint_region _ _ (Or.inl le_rfl)).symm
    let z : UnitTwoSphere × Ioo (-r) r :=
      (q, ⟨-r / 2, by constructor <;> linarith⟩)
    have hzneg : (z.2 : ℝ) < 0 := by dsimp only [z]; linarith
    have hzD : (z.1, (z.2 : ℝ)) ∈ N.cylinderDomain := hD (eD z).property
    have hzregion : N.coordinate_map (z.1, (z.2 : ℝ)) ∈
        N.region (-N.epsilon⁻¹) 0 := by
      refine ⟨N.coordinate_map_mem hzD, ?_, ?_⟩
      · rw [N.coordinate_inverse_coordinate_map hzD]
        exact hzD.2.1
      · rw [N.coordinate_inverse_coordinate_map hzD]
        exact hzneg
    have hzA : N.coordinate_map (z.1, (z.2 : ℝ)) ∈ A := by
      rw [← hemap z]
      exact ⟨e z, hnegative ⟨z, hzneg, rfl⟩, rfl⟩
    have hmeet : (N.region (-N.epsilon⁻¹) 0 ∩ interior A).Nonempty := by
      rw [hA.interior_eq]
      exact ⟨_, hzregion, hzA⟩
    simpa only [hA.interior_eq] using
      Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hconn havoid hmeet
  · right
    have hconn : IsPreconnected (N.region 0 N.epsilon⁻¹) := by
      rw [← N.coordinate_positive_image]
      exact (Poincare.Topology.isConnected_collar_positive heps N.coordinate).isPreconnected
    have havoid : Disjoint (N.region 0 N.epsilon⁻¹) (frontier A) := by
      rw [hfront]
      exact (N.central_sphere_disjoint_region _ _ (Or.inr le_rfl)).symm
    let z : UnitTwoSphere × Ioo (-r) r :=
      (q, ⟨r / 2, by constructor <;> linarith⟩)
    have hzpos : 0 < (z.2 : ℝ) := by dsimp only [z]; linarith
    have hzD : (z.1, (z.2 : ℝ)) ∈ N.cylinderDomain := hD (eD z).property
    have hzregion : N.coordinate_map (z.1, (z.2 : ℝ)) ∈
        N.region 0 N.epsilon⁻¹ := by
      refine ⟨N.coordinate_map_mem hzD, ?_, ?_⟩
      · rw [N.coordinate_inverse_coordinate_map hzD]
        exact hzpos
      · rw [N.coordinate_inverse_coordinate_map hzD]
        exact hzD.2.2
    have hzA : N.coordinate_map (z.1, (z.2 : ℝ)) ∈ A := by
      rw [← hemap z]
      exact ⟨e z, hpositive ⟨z, hzpos, rfl⟩, rfl⟩
    have hmeet : (N.region 0 N.epsilon⁻¹ ∩ interior A).Nonempty := by
      rw [hA.interior_eq]
      exact ⟨_, hzregion, hzA⟩
    simpa only [hA.interior_eq] using
      Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hconn havoid hmeet

end PoincareConjecture.M30
