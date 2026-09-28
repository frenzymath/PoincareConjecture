import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.CollarGluing.CollapseInjection









set_option autoImplicit false
open Set CategoryTheory

namespace PoincareConjecture.M76.HamiltonIntervalTorus

private theorem homotopy_map_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
    (hf : Function.Injective (FundamentalGroup.map f x)) :
    Function.Injective (FundamentalGroup.map g x) := by
  let N := FundamentalGroupoidFunctor.homotopicMapsNatIso H
  intro u v huv
  apply hf
  apply (cancel_mono (N.app ⟨x⟩)).mp
  exact (N.naturality u).trans ((congrArg (fun q => N.app ⟨x⟩ ≫ q) huv).trans
    (N.naturality v).symm)

theorem pi1_injective_of_inward_motion_and_kernel
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(X, Z)) {A : Set X}
    (D : C(unitInterval × X, X)) (hzero : ∀ x, D (0, x) = x)
    (hA : ∀ t, MapsTo (fun x => D (t, x)) A A)
    (hend : ∀ x, D (1, x) ∈ A)
    (hg : ∀ x, Function.Injective (FundamentalGroup.map g x))
    (hker : ∀ x : A, ∀ c : FundamentalGroup A x,
      FundamentalGroup.map (f.comp ⟨Subtype.val, continuous_subtype_val⟩) x c = 1 →
        FundamentalGroup.map (g.comp ⟨Subtype.val, continuous_subtype_val⟩) x c = 1)
    (x : X) : Function.Injective (FundamentalGroup.map f x) := by
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let r : C(X, A) := ⟨fun y => ⟨D (1, y), hend y⟩,
    (D.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let HX : (ContinuousMap.id X).HomotopyRel (i.comp r) ∅ := {
    toFun := D
    continuous_toFun := D.continuous
    map_zero_left := hzero
    map_one_left := fun _ => rfl
    prop' := by simp }
  let HA : (ContinuousMap.id A).HomotopyRel (r.comp i) ∅ := {
    toFun := fun z => ⟨D (z.1, z.2), hA z.1 z.2.property⟩
    continuous_toFun := (D.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun y => Subtype.ext (hzero y)
    map_one_left := fun _ => rfl
    prop' := by simp }
  have hi (a : A) : Function.Injective (FundamentalGroup.map i a) := by
    intro u v huv
    apply (HA.fundamentalGroup_map_bijective a).1
    simpa only [FundamentalGroup.map_comp_apply] using
      congrArg (FundamentalGroup.map r (i a)) huv
  have hr : Function.Injective (FundamentalGroup.map r x) := by
    intro u v huv
    apply (HX.fundamentalGroup_map_bijective x).1
    simpa only [FundamentalGroup.map_comp_apply] using
      congrArg (FundamentalGroup.map i (r x)) huv
  have hfi (a : A) : Function.Injective (FundamentalGroup.map (f.comp i) a) := by
    apply (injective_iff_map_eq_one _).mpr
    intro c hc
    apply hi a
    apply hg (i a)
    simpa only [FundamentalGroup.map_comp_apply, map_one] using hker a c hc
  have hfr : Function.Injective (FundamentalGroup.map ((f.comp i).comp r) x) := by
    intro u v huv
    apply hr
    apply hfi (r x)
    simpa only [FundamentalGroup.map_comp_apply] using huv
  have Hf : f.Homotopy ((f.comp i).comp r) :=
    (ContinuousMap.Homotopy.refl f).comp HX.toHomotopy
  exact homotopy_map_injective Hf.symm x hfr

end PoincareConjecture.M76.HamiltonIntervalTorus
