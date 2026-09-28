import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.FiniteComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.PhaseMap
import Mathlib.Topology.LocallyFinite



set_option autoImplicit false

open Set Geometry Topology

namespace Geometry


theorem PolyhedralPLInCharts.iUnion_of_closed_disjoint
    {E V X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] [Finite ι]
    {d : κ → OpenPartialHomeomorph X V} {f : E → X}
    (S : ι → Set E) (hclosed : ∀ i, IsClosed (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hf : ∀ i, PolyhedralPLInCharts d f (S i)) :
    PolyhedralPLInCharts d f (⋃ i, S i) := by
  classical
  refine ⟨(locallyFinite_of_finite S).continuousOn_iUnion hclosed
    (fun i => (hf i).continuousOn), ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := mem_iUnion.mp x.property
  obtain ⟨j, K, V, hK, hKS, hV, hxV, hVK, htarget, hformula⟩ :=
    (hf i).coordinates ⟨x, hxi⟩
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  let R : Set E := ⋃ k : {k : ι // k ≠ i}, S k
  have hR : IsClosed R := isClosed_iUnion_of_finite fun k => hclosed k
  have hxO : (x : E) ∈ O := by
    change (⟨x, hxi⟩ : S i) ∈ Subtype.val ⁻¹' O
    rw [hOV]
    exact hxV
  have hxR : (x : E) ∉ R := by
    intro hx
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hdisjoint k.property) hxk hxi
  refine ⟨j, K, (Subtype.val : (⋃ i, S i) → E) ⁻¹' (O ∩ Rᶜ),
    hK, hKS.trans (subset_iUnion S i),
    (hO.inter hR.isOpen_compl).preimage continuous_subtype_val, ⟨hxO, hxR⟩,
    ?_, htarget, hformula⟩
  rintro y ⟨z, hz, rfl⟩
  have hzi : (z : E) ∈ S i := by
    obtain ⟨k, hzk⟩ := mem_iUnion.mp z.property
    by_cases hki : k = i
    · simpa only [hki] using hzk
    · exact False.elim (hz.2 (mem_iUnion.mpr ⟨⟨k, hki⟩, hzk⟩))
  have hzV : (⟨z, hzi⟩ : S i) ∈ V := by
    rw [← hOV]
    exact hz.1
  exact hVK ⟨⟨z, hzi⟩, hzV, rfl⟩

end Geometry

namespace PoincareConjecture.M76.PhaseCovering

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Finite ι]
  (J : SimplicialComplex ℝ E) (K : ι → SimplicialComplex ℝ E)
  (hcover : (⋃ i, (K i).space) = J.space)


def componentCarrierInclusion (i : ι) : C((K i).space, J.space) :=
  ⟨fun x => ⟨x, hcover ▸ mem_iUnion.mpr ⟨i, x.property⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

omit [Finite ι] in
@[simp] theorem componentCarrierInclusion_coe (i : ι) (x : (K i).space) :
    (componentCarrierInclusion J K hcover i x : E) = x := rfl



theorem exists_coveringMap_with_phasePL
    (hJ : J.faces.Finite) (hK : ∀ i, (K i).faces.Finite)
    (hdisjoint : Pairwise fun i j => Disjoint (K i).space (K j).space)
    {κ : Type*} (d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ))
    (theta : C0) (f : C(J.space, C0 × C0))
    (g : ∀ i, C((K i).space, C0 × C0)) (hg : ∀ i, IsCoveringMap (g i))
    (H : ∀ i, (f.comp (componentCarrierInclusion J K hcover i)).Homotopy (g i))
    (hPL : ∀ i, PolyhedralPLInCharts d
      (hamiltonZeroCollarPhaseTarget (K i) (g i) theta) (K i).space) :
    ∃ G : C(J.space, C0 × C0), IsCoveringMap G ∧
      PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget J G theta) J.space ∧
      (∀ i (x : (K i).space), G (componentCarrierInclusion J K hcover i x) = g i x) ∧
      ∃ L : f.Homotopy G, ∀ t i (x : (K i).space),
        L (t, componentCarrierInclusion J K hcover i x) = H i (t, x) := by
  classical
  let : CompactSpace J.space := isCompact_iff_compactSpace.mp (J.isCompact_space_of_finite hJ)
  let S : ι → Set J.space := fun i => Subtype.val ⁻¹' (K i).space
  have hSclosed (i : ι) : IsClosed (S i) :=
    (K i).isCompact_space_of_finite (hK i) |>.isClosed.preimage continuous_subtype_val
  have hSdisjoint : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    exact (hdisjoint hij).preimage Subtype.val
  have hScover : (⋃ i, S i) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : (x : E) ∈ ⋃ i, (K i).space := hcover.symm ▸ x.property
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hi⟩
  let e (i : ι) : S i ≃ₜ (K i).space :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨componentCarrierInclusion J K hcover i x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let g' (i : ι) : C(S i, C0 × C0) := (g i).comp ⟨e i, (e i).continuous⟩
  have hg' (i : ι) : IsCoveringMap (g' i) := (hg i).comp_homeomorph (e i)
  let H' (i : ι) : (f.restrict (S i)).Homotopy (g' i) :=
    (H i).compContinuousMap ⟨e i, (e i).continuous⟩
  obtain ⟨G, hGcover, hG, L, hL⟩ :=
    exists_coveringMap_with_component_formulas S hSclosed hSdisjoint hScover f g' hg' H'
  have hGval (i : ι) (x : (K i).space) :
      G (componentCarrierInclusion J K hcover i x) = g i x := by
    have hv := hG i ((e i).symm x)
    change G (componentCarrierInclusion J K hcover i x) = g i (e i ((e i).symm x)) at hv
    simpa only [Homeomorph.apply_symm_apply] using hv
  have hwhole : PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget J G theta) J.space := by
    rw [← hcover]
    apply PolyhedralPLInCharts.iUnion_of_closed_disjoint (fun i => (K i).space)
      (fun i => (K i).isCompact_space_of_finite (hK i) |>.isClosed) hdisjoint
    intro i
    apply (hPL i).congr
    intro x hx
    have hxJ : x ∈ J.space := hcover ▸ mem_iUnion.mpr ⟨i, hx⟩
    simp only [hamiltonZeroCollarPhaseTarget, dif_pos hx, dif_pos hxJ]
    exact congrArg (fun z => (hamiltonZeroAmbientEquiv.trans
      hamiltonZeroHierarchyCoordinates).symm (z, theta)) (hGval i ⟨x, hx⟩).symm
  refine ⟨G, hGcover, hwhole, hGval, L, ?_⟩
  intro t i x
  have hv := hL t i ((e i).symm x)
  change L (t, componentCarrierInclusion J K hcover i x) = H i (t, e i ((e i).symm x)) at hv
  simpa only [Homeomorph.apply_symm_apply] using hv



theorem exists_coveringMap_of_component_phasePL
    (hJ : J.faces.Finite) (hK : ∀ i, (K i).faces.Finite)
    (hdisjoint : Pairwise fun i j => Disjoint (K i).space (K j).space)
    {κ : Type*} (d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ))
    (theta : C0) (f : C(J.space, C0 × C0))
    (h : ∀ i, ∃ g : C((K i).space, C0 × C0), IsCoveringMap g ∧
      Nonempty ((f.comp (componentCarrierInclusion J K hcover i)).Homotopy g) ∧
      PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget (K i) g theta) (K i).space) :
    ∃ G : C(J.space, C0 × C0), IsCoveringMap G ∧ Nonempty (f.Homotopy G) ∧
      PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget J G theta) J.space := by
  classical
  choose g hg H hPL using h
  obtain ⟨G, hG, hGPL, _, L, _⟩ := exists_coveringMap_with_phasePL J K hcover hJ hK hdisjoint
    d theta f g hg (fun i => (H i).some) hPL
  exact ⟨G, hG, ⟨L⟩, hGPL⟩

end PoincareConjecture.M76.PhaseCovering
