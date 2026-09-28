import PoincareConjecture.Proofs.M76.Mathlib.LocallyInjectiveFiberDescent
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Basic












set_option autoImplicit false

open Set

namespace IsLocallyInjective





theorem convex_cell_overlap
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace E] [T2Space E]
    {p : E → V} (hp : IsLocallyInjective p)
    {s t : Set V} (hs : Convex ℝ s) (ht : Convex ℝ t)
    (f : C(s, E)) (g : C(t, E))
    (hf : ∀ a, p (f a) = (a : V)) (hg : ∀ a, p (g a) = (a : V))
    (hmeet : (range f ∩ range g).Nonempty) :
    (∀ a : (s ∩ t : Set V), f ⟨a, a.property.1⟩ = g ⟨a, a.property.2⟩) ∧
      range f ∩ range g = range (fun a : (s ∩ t : Set V) => f ⟨a, a.property.1⟩) := by
  let fs : (s ∩ t : Set V) → E := fun a => f ⟨a, a.property.1⟩
  let gt : (s ∩ t : Set V) → E := fun a => g ⟨a, a.property.2⟩
  have hfs : Continuous fs := f.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hgt : Continuous gt := g.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hcoord (a : s) (b : t) (hab : f a = g b) : (a : V) = b :=
    (hf a).symm.trans ((congrArg p hab).trans (hg b))
  obtain ⟨y, ⟨a, hay⟩, ⟨b, hby⟩⟩ := hmeet
  have hab : f a = g b := hay.trans hby.symm
  have he := hcoord a b hab
  let a0 : (s ∩ t : Set V) := ⟨a, a.property, he.symm ▸ b.property⟩
  have hbase : fs a0 = gt a0 := by
    have hb : (⟨(a : V), he.symm ▸ b.property⟩ : t) = b := Subtype.ext he
    change f a = g ⟨(a : V), he.symm ▸ b.property⟩
    rw [hb]
    exact hab
  let : PreconnectedSpace (s ∩ t : Set V) :=
    isPreconnected_iff_preconnectedSpace.mp (hs.inter ht).isPreconnected
  have hproj : p ∘ fs = p ∘ gt := by
    funext x
    exact (hf ⟨x, x.property.1⟩).trans (hg ⟨x, x.property.2⟩).symm
  have heq : fs = gt :=
    (T2Space.isSeparatedMap p).eq_of_comp_eq hp hfs hgt hproj a0 hbase
  refine ⟨fun x => congrFun heq x, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨u, huz⟩, ⟨v, hvz⟩⟩
    have huv := hcoord u v (huz.trans hvz.symm)
    exact ⟨⟨u, u.property, huv.symm ▸ v.property⟩, huz⟩
  · rintro ⟨x, hxz⟩
    refine ⟨⟨⟨x, x.property.1⟩, hxz⟩, ⟨⟨x, x.property.2⟩, ?_⟩⟩
    exact (congrFun heq x).symm.trans hxz

end IsLocallyInjective
