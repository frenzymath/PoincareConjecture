import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.RawCutComponentHomotopy



set_option autoImplicit false
open Set
open scoped Topology
namespace PoincareConjecture.M76

theorem exists_component_homotopy_section
    {X : Type*} [TopologicalSpace X] (U V : Set X) (hVU : V ⊆ U)
    (F : C(unitInterval × U, U)) (hF0 : ∀x, F (0,x) = x)
    (hF1 : ∀x, (F (1,x) : X) ∈ V) (x : U) :
    ∃ (s : C(connectedComponentIn U x,connectedComponentIn V (F (1,x) : X)))
      (i : C(connectedComponentIn V (F (1,x) : X),connectedComponentIn U x)),
      (∀y,(s y : X) = F (1,⟨y,connectedComponentIn_subset _ _ y.property⟩)) ∧
      (∀y,(i y : X) = y) ∧ (i.comp s).Homotopic (ContinuousMap.id _) := by
  have hpath (t : unitInterval) (y : U) :
      (F (t,y) : X) ∈ connectedComponentIn U y := by
    let p : unitInterval → X := fun t => F (t,y)
    have hp : Continuous p := continuous_subtype_val.comp
      (F.continuous.comp (continuous_id.prodMk continuous_const))
    exact (isConnected_range hp).isPreconnected.subset_connectedComponentIn
      (show (y : X) ∈ range p from ⟨0,congrArg Subtype.val (hF0 y)⟩)
      (show range p ⊆ U by rintro _ ⟨t,rfl⟩; exact (F (t,y)).property) ⟨t,rfl⟩
  let CU := connectedComponentIn U (x : X)
  let : ConnectedSpace CU := isConnected_iff_connectedSpace.mp
    (isConnected_connectedComponentIn_iff.mpr x.property)
  let f : C(CU,X) := ⟨fun y => F (1,⟨y,connectedComponentIn_subset _ _ y.property⟩),
    continuous_subtype_val.comp (F.continuous.comp
      (continuous_const.prodMk (continuous_subtype_val.subtype_mk _)))⟩
  have hmap : range f ⊆ connectedComponentIn V (F (1,x) : X) :=
    (isConnected_range f.continuous).isPreconnected.subset_connectedComponentIn
      ⟨⟨x,mem_connectedComponentIn x.property⟩,rfl⟩
      (by rintro _ ⟨y,rfl⟩; exact hF1 _)
  let s : C(CU,connectedComponentIn V (F (1,x) : X)) :=
    ⟨fun y => ⟨f y,hmap (mem_range_self y)⟩,f.continuous.subtype_mk _⟩
  have hsub : connectedComponentIn V (F (1,x) : X) ⊆ CU := by
    have hh := connectedComponentIn_mono (F (1,x) : X) hVU
    rwa [← connectedComponentIn_eq (hpath 1 x)] at hh
  let i : C(connectedComponentIn V (F (1,x) : X),CU) :=
    ⟨Set.inclusion hsub,continuous_inclusion _⟩
  have hstay (t : unitInterval) (y : CU) :
      (F (t,⟨y,connectedComponentIn_subset _ _ y.property⟩) : X) ∈ CU := by
    have hh := hpath t ⟨y,connectedComponentIn_subset _ _ y.property⟩
    rwa [← connectedComponentIn_eq y.property] at hh
  have H : (ContinuousMap.id CU).Homotopy (i.comp s) :=
    { toFun := fun z => ⟨F (z.1,⟨z.2,connectedComponentIn_subset _ _ z.2.property⟩),hstay z.1 z.2⟩
      continuous_toFun := (continuous_subtype_val.comp (F.continuous.comp
        (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))).subtype_mk _
      map_zero_left := fun y => Subtype.ext (congrArg (fun z : U => (z : X))
        (hF0 ⟨y,connectedComponentIn_subset _ _ y.property⟩))
      map_one_left := fun _ => rfl }
  exact ⟨s,i,fun _ => rfl,fun _ => rfl,⟨H.symm⟩⟩

end PoincareConjecture.M76
