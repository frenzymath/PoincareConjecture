import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.ParameterizedPieces



set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

local notation "I" => Icc (0 : ℝ) 1

theorem collision_iff_of_injective {C X : Type*} {f : C × I → X}
    (hi : Function.Injective f) (x y : C) (s t : I) :
    f (x,s) = f (y,t) ↔
      f (x,⟨0,by norm_num⟩) = f (y,⟨0,by norm_num⟩) ∧ s = t := by
  constructor
  · intro h
    have hxy := hi h
    exact ⟨congrArg (fun z => f (z,⟨0,by norm_num⟩)) (congrArg Prod.fst hxy),
      congrArg Prod.snd hxy⟩
  · rintro ⟨hxy,hst⟩
    have hbase := hi hxy
    have hxy' : x = y := congrArg Prod.fst hbase
    exact congrArg f (Prod.ext hxy' hst)

theorem collision_iff_of_disjoint_ranges {C D X : Type*}
    {f : C × I → X} {g : D × I → X} (hd : Disjoint (range f) (range g))
    (x : C) (y : D) (s t : I) :
    f (x,s) = g (y,t) ↔
      f (x,⟨0,by norm_num⟩) = g (y,⟨0,by norm_num⟩) ∧ s = t := by
  have hne (s t : I) : f (x,s) ≠ g (y,t) := fun h =>
    disjoint_left.mp hd (mem_range_self (x,s)) (h ▸ mem_range_self (y,t))
  exact iff_of_false (hne s t) (fun h => hne _ _ h.1)

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
