import Mathlib.Topology.Homotopy.Lifting












open Function Set Topology

namespace Poincare.Topology

variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E]
  [TopologicalSpace X] {p : E → X}



theorem exists_openEmbedding_lift [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (hp : IsCoveringMap p) {f : A → X} (hf : IsOpenEmbedding f)
    (a : A) (e : E) (he : p e = f a) :
    ∃ F : C(A, E), F a = e ∧ p ∘ F = f ∧ IsOpenEmbedding F := by
  obtain ⟨F, ⟨hFa, hF⟩, _⟩ := hp.existsUnique_continuousMap_lifts ⟨f, hf.continuous⟩ a e he
  refine ⟨F, hFa, hF, hp.isLocalHomeomorph.isOpenEmbedding_of_comp ?_ F.continuous⟩
  rwa [hF]



theorem disjoint_ranges_of_distinct_lifts [PreconnectedSpace A]
    (hp : IsCoveringMap p) {f : A → X} (hf : Injective f)
    (F G : C(A, E)) (hF : p ∘ F = f) (hG : p ∘ G = f) (hne : F ≠ G) :
    Disjoint (range F) (range G) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have hab : b = a := hf (by
    rw [← congr_fun hG b, ← congr_fun hF a]
    exact congr_arg p hb)
  subst b
  apply hne
  exact DFunLike.ext' (hp.eq_of_comp_eq F.continuous G.continuous
    (hF.trans hG.symm) a hb.symm)



theorem covering_transformation_eq_refl_of_fixedPoint [PreconnectedSpace E]
    (hp : IsCoveringMap p) (d : E ≃ₜ E) (hd : p ∘ d = p)
    {e : E} (he : d e = e) : d = Homeomorph.refl E := by
  apply Homeomorph.ext
  exact congr_fun (hp.eq_of_comp_eq d.continuous continuous_id hd e he)

omit [TopologicalSpace A] in


theorem disjoint_covering_translate [PreconnectedSpace E]
    (hp : IsCoveringMap p) {f : A → X} (hf : Injective f)
    {F : A → E} (hF : p ∘ F = f) (d : E ≃ₜ E) (hd : p ∘ d = p)
    (hne : d ≠ Homeomorph.refl E) : Disjoint (range F) (d '' range F) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨_, ⟨b, rfl⟩, hb⟩
  have hab : b = a := hf (by
    rw [← congr_fun hF b, ← congr_fun hF a]
    change p (F b) = p (F a)
    rw [← congr_fun hd (F b)]
    exact congr_arg p hb)
  subst b
  exact hne (covering_transformation_eq_refl_of_fixedPoint hp d hd hb)

end Poincare.Topology
