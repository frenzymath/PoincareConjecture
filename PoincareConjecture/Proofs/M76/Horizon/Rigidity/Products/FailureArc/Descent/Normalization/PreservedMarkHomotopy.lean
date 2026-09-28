import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.DisjointMarks



set_option autoImplicit false
open Set Topology unitInterval
open scoped unitInterval

namespace PoincareConjecture.M76

theorem exists_parametrized_homotopy_in_preserved_mark
    {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    (p : C(X, M)) (R : Set M) (F : Bool → Set M)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (G : I → X ≃ₜ X) (hG : Continuous (fun z : I × X => G z.1 z.2))
    (hzero : ∀ x, G 0 x = x)
    (hmark : ∀ a, (G a) ⁻¹' (p ⁻¹' (F false ∪ F true)) = p ⁻¹' (F false ∪ F true))
    (b : Bool) (j : C(Y, X)) (gamma : C(Y, F b))
    (hgamma : ∀ y, (gamma y : M) = p (j y)) :
    ∃ (gamma' : C(Y, F b)) (eta : gamma.Homotopy gamma'),
      (∀ y, (gamma' y : M) = p (G 1 (j y))) ∧
      ∀ a y, (eta (a, y) : M) = p (G a (j y)) := by
  have hjmark (y : Y) : p (j y) ∈ F false ∪ F true := by
    rw [← hgamma y]
    cases b with
    | false => exact Or.inl (gamma y).property
    | true => exact Or.inr (gamma y).property
  have hm (a : I) (y : Y) : p (G a (j y)) ∈ F false ∪ F true := by
    change j y ∈ (G a) ⁻¹' (p ⁻¹' (F false ∪ F true))
    rw [hmark]
    exact hjmark y
  let H : C(I × Y, ↥(F false ∪ F true)) :=
    ⟨fun z => ⟨p (G z.1 (j z.2)), hm z.1 z.2⟩,
      (p.continuous.comp
        (hG.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd)))).subtype_mk _⟩
  have hH0 (y : Y) : (H (0, y) : M) = (gamma y : M) := by
    change p (G 0 (j y)) = _
    rw [hzero, hgamma]
  obtain ⟨gamma', eta, heta⟩ :=
    exists_homotopy_in_disjoint_open_mark F hF hopen hdis b gamma H hH0
  refine ⟨gamma', eta, ?_, heta⟩
  intro y
  have he : eta (1, y) = gamma' y := eta.map_one_left y
  exact (congrArg Subtype.val he).symm.trans (heta 1 y)

end PoincareConjecture.M76
