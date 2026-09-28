import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.FiniteComponentPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.RecognizedComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.ParametrizedPLSurface



set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.PhaseCovering

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]
  (J : SimplicialComplex ℝ E) (K : ι → SimplicialComplex ℝ E)
  (hcover : (⋃ i, (K i).space) = J.space)
  (hK : ∀ i, (K i).faces.Finite)
  (hdisjoint : Pairwise fun i j => Disjoint (K i).space (K j).space)

include hK hdisjoint


theorem componentCarrier_fundamentalGroup_injective
    {Y : Type*} [TopologicalSpace Y] (f : C(J.space, Y))
    (hf : ∀ x, Function.Injective (FundamentalGroup.map f x))
    (i : ι) (x : (K i).space) :
    Function.Injective
      (FundamentalGroup.map (f.comp (componentCarrierInclusion J K hcover i)) x) := by
  let S : ι → Set J.space := fun j => Subtype.val ⁻¹' (K j).space
  have hSclosed (j : ι) : IsClosed (S j) :=
    (K j).isCompact_space_of_finite (hK j) |>.isClosed.preimage continuous_subtype_val
  have hSdisjoint : Pairwise fun j k => Disjoint (S j) (S k) := by
    intro j k hjk
    exact (hdisjoint hjk).preimage Subtype.val
  have hScover : (⋃ j, S j) = univ := by
    apply eq_univ_of_forall
    intro y
    have hy : (y : E) ∈ ⋃ j, (K j).space := hcover.symm ▸ y.property
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨j, hj⟩
  let e : (K i).space ≃ₜ S i :=
    { toFun := fun y => ⟨componentCarrierInclusion J K hcover i y, y.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  change Function.Injective
    (FundamentalGroup.map ((f.restrict (S i)).comp ⟨e, e.continuous⟩) x)
  rw [FundamentalGroup.map_comp]
  exact (restrict_fundamentalGroup_injective S hSclosed hSdisjoint hScover f hf i (e x)).comp
    (FundamentalGroup.map_bijective_of_homotopyEquiv e.toHomotopyEquiv x).1

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))



theorem exists_PL_coveringMap_of_recognized_components [FiniteDimensional ℝ E]
    (hJ : J.faces.Finite)
    {κ : Type*} {d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (theta : C0) (f : C(J.space, C0 × C0))
    (hf : ∀ x, Function.Injective (FundamentalGroup.map f x))
    (h : ∀ i, (C0 × C0) ≃ₜ (K i).space)
    (hparam : ∀ i, PolyhedralPLInCharts d
      (hamiltonZeroCollarPhaseTarget (K i) ⟨(h i).symm, (h i).symm.continuous⟩ theta)
      (K i).space) :
    ∃ (A : ι → Matrix (Fin 2) (Fin 2) ℤ) (G : C(J.space, C0 × C0)),
      (∀ i, (A i).det ≠ 0) ∧ IsCoveringMap G ∧
      (∀ i (x : (K i).space), G (componentCarrierInclusion J K hcover i x) =
        LinearTorus.affineIntegerMatrixMap (4 * (16 : ℝ)) (A i)
          (f (componentCarrierInclusion J K hcover i (h i 0))) ((h i).symm x)) ∧
      Nonempty (f.Homotopy G) ∧
      PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget J G theta) J.space := by
  classical
  have hex (i : ι) : ∃ (A : Matrix (Fin 2) (Fin 2) ℤ) (g : C((K i).space, C0 × C0)),
      A.det ≠ 0 ∧ IsCoveringMap g ∧
      (∀ x, g x = LinearTorus.affineIntegerMatrixMap (4 * (16 : ℝ)) A
        (f (componentCarrierInclusion J K hcover i (h i 0))) ((h i).symm x)) ∧
      Nonempty ((f.comp (componentCarrierInclusion J K hcover i)).HomotopyRel g {h i 0}) ∧
      PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget (K i) g theta) (K i).space :=
    exists_parametrized_PL_torus_covering hd (K i) (h i) theta
      (f.comp (componentCarrierInclusion J K hcover i))
      (componentCarrier_fundamentalGroup_injective J K hcover hK hdisjoint f hf i (h i 0))
      (hparam i)
  choose A g hA hg hformula H hPL using hex
  obtain ⟨G, hG, hGPL, hGval, L, _⟩ :=
    exists_coveringMap_with_phasePL J K hcover hJ hK hdisjoint d theta f g hg
      (fun i => (H i).some.toHomotopy) hPL
  refine ⟨A, G, hA, hG, ?_, ⟨L⟩, hGPL⟩
  intro i x
  exact (hGval i x).trans (hformula i x)

end PoincareConjecture.M76.PhaseCovering
