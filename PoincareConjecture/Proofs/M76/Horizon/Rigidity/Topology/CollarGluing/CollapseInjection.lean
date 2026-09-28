import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.CollarGluing.OpenFrontierCollapse



set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X]

private theorem injection_of_square {A B C D : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (f : C(A, B)) (g : C(B, D)) (r : C(A, C)) (i : C(C, D))
    (hcomm : g.comp f = i.comp r) (x : A)
    (hr : Function.Injective (FundamentalGroup.map r x))
    (hi : Function.Injective (FundamentalGroup.map i (r x))) :
    Function.Injective (FundamentalGroup.map f x) := by
  intro a b hab
  apply hr
  apply hi
  have h := congrArg (FundamentalGroup.map g (f x)) hab
  rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply] at h
  have h' := Eq.mp (congrArg (fun k : C(A, D) =>
    FundamentalGroup.map k x a = FundamentalGroup.map k x b) hcomm) h
  simpa only [FundamentalGroup.map_comp_apply] using h'



theorem motion_endpoint_injective (D : C(unitInterval × X, X))
    (hzero : ∀ x, D (0, x) = x) {S : Set X}
    (hS : ∀ t, MapsTo (fun x => D (t, x)) S S) (x : S) :
    Function.Injective (FundamentalGroup.map
      (⟨fun y : S => ⟨D (1, y), hS 1 y.property⟩,
        (D.continuous.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩ :
          C(S, S)) x) := by
  let g : C(S, S) := ⟨fun y => ⟨D (1, y), hS 1 y.property⟩,
    (D.continuous.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩
  let H : (ContinuousMap.id S).HomotopyRel g ∅ := {
    toFun := fun z => ⟨D (z.1, z.2), hS z.1 z.2.property⟩
    continuous_toFun := (D.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (hzero x)
    map_one_left := fun _ => rfl
    prop' := by simp }
  exact (H.fundamentalGroup_map_bijective x).1

namespace OpenFrontierCollapse

variable {R : Set X} (C : OpenFrontierCollapse R)



theorem overlap_collapse_injective (x : C.overlap) :
    Function.Injective (FundamentalGroup.map
      (⟨fun y : C.overlap => ⟨C.motion (1, y), C.endpoint_overlap y.property⟩,
        (C.motion.continuous.comp
          (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩ :
            C(C.overlap, frontier R)) x) := by
  let r : C(C.overlap, frontier R) :=
    ⟨fun y => ⟨C.motion (1, y), C.endpoint_overlap y.property⟩,
      (C.motion.continuous.comp
        (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩
  have hinj := motion_endpoint_injective C.motion C.motion_zero C.motion_overlap x
  intro a b hab
  apply hinj
  have h := congrArg (FundamentalGroup.map (ContinuousMap.inclusion C.frontier_subset) (r x)) hab
  rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply] at h
  exact h



theorem overlap_inclusion_injective {T U : Set X}
    (hU : U = T ∪ C.overlap) (hST : frontier R ⊆ T)
    (hmoveT : ∀ t, MapsTo (fun x => C.motion (t, x)) T T)
    (hpi : ∀ x : frontier R,
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hST) x))
    (x : C.overlap) :
    Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (show C.overlap ⊆ U by rw [hU]; exact subset_union_right)) x) := by
  let hWU : C.overlap ⊆ U := by rw [hU]; exact subset_union_right
  have hUT : MapsTo (fun y => C.motion (1, y)) U T := by
    intro y hy
    rw [hU] at hy
    rcases hy with hy | hy
    · exact hmoveT 1 hy
    · exact hST (C.endpoint_overlap hy)
  let f : C(C.overlap, U) := ContinuousMap.inclusion hWU
  let g : C(U, T) := ⟨fun y => ⟨C.motion (1, y), hUT y.property⟩,
    (C.motion.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩
  let r : C(C.overlap, frontier R) :=
    ⟨fun y => ⟨C.motion (1, y), C.endpoint_overlap y.property⟩,
      (C.motion.continuous.comp
        (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩
  exact injection_of_square f g r (ContinuousMap.inclusion hST) rfl x
    (C.overlap_collapse_injective x) (hpi (r x))



theorem side_inclusion_injective {T U : Set X}
    (hU : U = T ∪ C.overlap) (hST : frontier R ⊆ T)
    (hmoveT : ∀ t, MapsTo (fun x => C.motion (t, x)) T T)
    (x : T) :
    Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (show T ⊆ U by rw [hU]; exact subset_union_left)) x) := by
  let hTU : T ⊆ U := by rw [hU]; exact subset_union_left
  have hUT : MapsTo (fun y => C.motion (1, y)) U T := by
    intro y hy
    rw [hU] at hy
    rcases hy with hy | hy
    · exact hmoveT 1 hy
    · exact hST (C.endpoint_overlap hy)
  let g : C(U, T) := ⟨fun y => ⟨C.motion (1, y), hUT y.property⟩,
    (C.motion.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩
  have hinj := motion_endpoint_injective C.motion C.motion_zero hmoveT x
  intro a b hab
  apply hinj
  have h := congrArg (FundamentalGroup.map g (ContinuousMap.inclusion hTU x)) hab
  rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply] at h
  exact h

end OpenFrontierCollapse

end PoincareConjecture.M76
