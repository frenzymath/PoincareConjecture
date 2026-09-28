import PoincareConjecture.Proofs.M83.LocalOrientation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set

universe u v

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology

namespace LocalOrientation

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]



theorem pullback_comp [T2Space X] [T2Space Y] [T2Space Z]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (O : LocalOrientation Z) (f : C(X, Y)) (g : C(Y, Z))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (x : X) :
    ((O.pullback g hg).pullback f hf).atPoint x =
      (O.pullback (g.comp f) (hg.comp hf)).atPoint x := by
  apply (localHomologyEquiv (g.comp f) (hg.comp hf) x 3).injective
  change localHomologyMap (g.comp f) (hg.injective.comp hf.injective) x 3 _ =
    localHomologyMap (g.comp f) (hg.injective.comp hf.injective) x 3 _
  rw [← localHomologyMap_comp f g hf.injective hg.injective,
    ModuleCat.comp_apply,
    LocalOrientation.map_pullback (O.pullback g hg) f hf x]
  rw [localHomologyMap_comp f g hf.injective hg.injective]
  exact (LocalOrientation.map_pullback O g hg (f x)).trans
    (LocalOrientation.map_pullback O (g.comp f) (hg.comp hf) x).symm



theorem pullback_congr [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O : LocalOrientation Y) (f g : C(X, Y))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (hfg : f = g) (x : X) :
    (O.pullback f hf).atPoint x = (O.pullback g hg).atPoint x := by
  subst g
  rfl



theorem pullback_smul [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O P : LocalOrientation Y) (a : Int)
    (h : ∀ y, O.atPoint y = a • P.atPoint y)
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) (x : X) :
    (O.pullback f hf).atPoint x = a • (P.pullback f hf).atPoint x := by
  apply (localHomologyEquiv f hf x 3).injective
  change localHomologyMap f hf.injective x 3 _ = localHomologyMap f hf.injective x 3 _
  rw [map_zsmul, map_pullback, map_pullback, h]



theorem exists_smul [T2Space X] [PreconnectedSpace X]
    (O P : LocalOrientation X) (x : X) :
    ∃ a : Int, ∀ y, O.atPoint y = a • P.atPoint y := by
  refine ⟨(P.basis x).symm (O.atPoint x), ?_⟩
  intro y
  have h := (O.comparison_locallyConstant P).apply_eq_of_preconnectedSpace y x
  have he := congrArg (P.basis y) h
  simpa only [LinearEquiv.apply_symm_apply, basis_apply] using he



def inclusionClass {U : Set X} (O : LocalOrientation U) (x : U) :
    LocalHomology X x 3 :=
  localHomologyMap (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
    Subtype.val_injective x 3 (O.atPoint x)



def glue [T2Space X] {I : Type v}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (O : ∀ i, LocalOrientation (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hcompat : ∀ (i j : I) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (O i).inclusionClass ⟨x, hi⟩ = (O j).inclusionClass ⟨x, hj⟩) :
    LocalOrientation X := by
  let idx (x : X) : I := (hcover x).choose
  have hidx (x : X) : x ∈ U (idx x) := (hcover x).choose_spec
  refine {
    atPoint := fun x => (O (idx x)).inclusionClass ⟨x, hidx x⟩
    generates := ?_
    locallyRepresented := ?_ }
  · intro x
    let inc : C(U (idx x), X) := ⟨Subtype.val, continuous_subtype_val⟩
    refine ⟨((O (idx x)).basis ⟨x, hidx x⟩).trans
      (localHomologyEquiv inc (hU (idx x)).isOpenEmbedding_subtypeVal ⟨x, hidx x⟩ 3), ?_⟩
    change localHomologyEquiv inc (hU (idx x)).isOpenEmbedding_subtypeVal ⟨x, hidx x⟩ 3
        ((O (idx x)).basis ⟨x, hidx x⟩ 1) = _
    rw [basis_one]
    rfl
  · intro x
    let i := idx x
    let inc : C(U i, X) := ⟨Subtype.val, continuous_subtype_val⟩
    obtain ⟨V, hV, hxV, b, hb⟩ := (O i).locallyRepresented ⟨x, hidx x⟩
    refine ⟨inc '' V, (hU i).isOpenMap_subtype_val V hV,
      ⟨⟨x, hidx x⟩, hxV, rfl⟩,
      homologyMap (integralSupportEmbeddingChains inc Subtype.val_injective V) 3 b, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    have h := congrArg (fun k => k b)
      (localHomologyMap_restriction inc Subtype.val_injective z hz 3)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hb z hz] at h
    exact h.symm.trans (hcompat i (idx z.val) z.val z.property (hidx z.val))



theorem glue_atPoint [T2Space X] {I : Type v}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (O : ∀ i, LocalOrientation (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hcompat : ∀ (i j : I) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (O i).inclusionClass ⟨x, hi⟩ = (O j).inclusionClass ⟨x, hj⟩)
    (i : I) (x : X) (hx : x ∈ U i) :
    (glue U hU O hcover hcompat).atPoint x = (O i).inclusionClass ⟨x, hx⟩ :=
  hcompat (hcover x).choose i x (hcover x).choose_spec hx

end LocalOrientation

end PoincareConjecture.Proofs.M83
