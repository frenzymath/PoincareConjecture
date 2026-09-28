import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.FiniteComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.ParametrizedSurface

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.PhaseCovering

variable {ι F : Type*} [Finite ι] [TopologicalSpace F]
  (S : ι → Set F) (hclosed : ∀ i, IsClosed (S i))
  (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
  (hcover : (⋃ i, S i) = univ)

include hclosed hdisjoint hcover

theorem isClopen_member (i : ι) : IsClopen (S i) := by
  classical
  have heq : (S i)ᶜ = ⋃ j : {j : ι // j ≠ i}, S j.1 := by
    ext x
    constructor
    · intro hx
      have hu : x ∈ ⋃ j, S j := by rw [hcover]; exact mem_univ x
      obtain ⟨j, hj⟩ := mem_iUnion.mp hu
      have hji : j ≠ i := by intro h; subst j; exact hx hj
      exact mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · rintro hx hi
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact Set.disjoint_left.mp (hdisjoint j.property) hj hi
  refine ⟨hclosed i, ?_⟩
  have hc : IsClosed (S i)ᶜ := by
    rw [heq]
    exact isClosed_iUnion_of_finite (fun j => hclosed j.1)
  exact isClosed_compl_iff.mp hc

theorem restrict_fundamentalGroup_injective {Y : Type*} [TopologicalSpace Y]
    (f : C(F, Y)) (hf : ∀ x, Function.Injective (FundamentalGroup.map f x))
    (i : ι) (x : S i) :
    Function.Injective (FundamentalGroup.map (f.restrict (S i)) x) := by
  change Function.Injective
    (FundamentalGroup.map (f.comp ⟨Subtype.val, continuous_subtype_val⟩) x)
  rw [FundamentalGroup.map_comp]
  exact (hf x).comp
    ((isClopen_member S hclosed hdisjoint hcover i).fundamentalGroupMulEquiv x).injective

theorem exists_coveringMap_of_recognized_components [CompactSpace F] [T2Space F]
    (p : ℝ) (hp : 0 < p) (f : C(F, AddCircle p × AddCircle p))
    (hf : ∀ x, Function.Injective (FundamentalGroup.map f x))
    (h : ∀ i, (AddCircle p × AddCircle p) ≃ₜ S i) :
    ∃ (A : ι → Matrix (Fin 2) (Fin 2) ℤ) (G : C(F, AddCircle p × AddCircle p)),
      (∀ i, (A i).det ≠ 0) ∧ IsCoveringMap G ∧
      (∀ i (x : S i), G x = LinearTorus.affineIntegerMatrixMap p (A i)
        (f (h i 0)) ((h i).symm x)) ∧ Nonempty (f.Homotopy G) := by
  classical
  have hs : ∀ i, ∃ (A : Matrix (Fin 2) (Fin 2) ℤ)
      (g : C(S i, AddCircle p × AddCircle p)),
      A.det ≠ 0 ∧ IsCoveringMap g ∧
      (∀ x, g x = LinearTorus.affineIntegerMatrixMap p A (f (h i 0)) ((h i).symm x)) ∧
      Nonempty ((f.restrict (S i)).HomotopyRel g {h i 0}) := by
    intro i
    exact exists_parametrized_torus_covering p hp (h i) (f.restrict (S i))
      (restrict_fundamentalGroup_injective S hclosed hdisjoint hcover f hf i (h i 0))
  choose A g hA hg hformula H using hs
  refine ⟨A, componentMap S hclosed hdisjoint hcover g, hA,
    isCoveringMap_componentMap S hclosed hdisjoint hcover g hg, ?_, ?_⟩
  · intro i x
    rw [componentMap_apply]
    exact hformula i x
  · exact ⟨componentHomotopy S hclosed hdisjoint hcover f g
      (fun i => (H i).some.toHomotopy)⟩

end PoincareConjecture.M76.PhaseCovering
