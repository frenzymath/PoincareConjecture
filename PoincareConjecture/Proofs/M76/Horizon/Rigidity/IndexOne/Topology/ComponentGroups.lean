import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.Injection

set_option autoImplicit false
open Set

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S F : Set X}

theorem inclusion_surjective_of_whole_component (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S) (x : S) :
    Function.Surjective (map (ContinuousMap.inclusion hSF) x) := by
  intro a
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  let f : unitInterval → X := fun t => (p t : X)
  have hf : Continuous f := continuous_subtype_val.comp p.continuous
  have hx : (x : X) ∈ range f := ⟨0, congrArg Subtype.val p.source⟩
  have hF : range f ⊆ F := by
    rintro _ ⟨t, rfl⟩
    exact (p t).property
  have hS : range f ⊆ S := by
    rw [← hcomponent x x.property]
    exact (isPreconnected_range hf).subset_connectedComponentIn hx hF
  let q : Path x x :=
    { toFun := fun t => ⟨p t, hS (mem_range_self t)⟩
      continuous_toFun := hf.subtype_mk _
      source' := Subtype.ext (congrArg (fun y : F => (y : X)) p.source)
      target' := Subtype.ext (congrArg (fun y : F => (y : X)) p.target) }
  refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
  change Path.Homotopic.Quotient.mk (q.map (continuous_inclusion hSF)) =
    Path.Homotopic.Quotient.mk p
  congr 1

theorem inclusion_bijective_of_whole_component (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S) (x : S) :
    Function.Bijective (map (ContinuousMap.inclusion hSF) x) :=
  ⟨inclusion_injective_of_whole_component hSF hcomponent x,
    inclusion_surjective_of_whole_component hSF hcomponent x⟩

theorem map_surjective_of_factor_through_whole_component (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    (f : C(Y, F)) (fS : C(Y, S))
    (hfactor : f = (ContinuousMap.inclusion hSF).comp fS) (c : Y)
    (hf : Function.Surjective (map f c)) :
    Function.Surjective (map fS c) := by
  subst f
  intro z
  obtain ⟨a, ha⟩ := hf (map (ContinuousMap.inclusion hSF) (fS c) z)
  refine ⟨a, inclusion_injective_of_whole_component hSF hcomponent (fS c) ?_⟩
  rw [map_comp, MonoidHom.comp_apply] at ha
  exact ha

theorem map_bijective_of_factor_through_whole_component (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    (f : C(Y, F)) (fS : C(Y, S))
    (hfactor : f = (ContinuousMap.inclusion hSF).comp fS) (c : Y)
    (hf : Function.Bijective (map f c)) :
    Function.Bijective (map fS c) := by
  refine ⟨?_, map_surjective_of_factor_through_whole_component
    hSF hcomponent f fS hfactor c hf.2⟩
  subst f
  intro a b hab
  apply hf.1
  rw [map_comp, MonoidHom.comp_apply, MonoidHom.comp_apply, hab]

end FundamentalGroup
