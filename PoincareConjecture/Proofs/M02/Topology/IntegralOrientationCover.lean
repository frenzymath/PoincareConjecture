import PoincareConjecture.Proofs.M02.Topology.IntegralCompactGluing
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportLocalization
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.FiberBundle.Basic









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_open_integralSupportHomology_restrictions_eq [T2Space X]
    (K L : Set X) (d : Nat) (a : integralSupportHomology K d)
    (b : integralSupportHomology L d) (x : X) (hxK : x ∈ K) (hxL : x ∈ L)
    (hab : integralSupportHomologyRestriction (singleton_subset_iff.mpr hxK) d a =
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hxL) d b) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y : X, ∀ hy : y ∈ K ∩ L ∩ V,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy.1.1) d a =
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy.1.2) d b := by
  let c : integralSupportHomology (K ∩ L) d :=
    integralSupportHomologyRestriction inter_subset_left d a -
      integralSupportHomologyRestriction inter_subset_right d b
  have hc : integralSupportHomologyRestriction
      (singleton_subset_iff.mpr (show x ∈ K ∩ L from ⟨hxK, hxL⟩)) d c = 0 := by
    dsimp only [c]
    rw [map_sub, integralSupportHomologyRestriction_apply_comp,
      integralSupportHomologyRestriction_apply_comp, hab, sub_self]
  obtain ⟨V, hV, hxV, hcV⟩ :=
    exists_open_integralRelativeHomology_restriction_eq_zero (K ∩ L) d c x ⟨hxK, hxL⟩ hc
  change integralSupportHomologyRestriction (inter_subset_left : K ∩ L ∩ V ⊆ K ∩ L) d c = 0
    at hcV
  refine ⟨V, hV, hxV, ?_⟩
  intro y hy
  have he : integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d
      (integralSupportHomologyRestriction inter_subset_left d c) = 0 := by
    rw [hcV, map_zero]
  rw [integralSupportHomologyRestriction_apply_comp] at he
  dsimp only [c] at he
  rw [map_sub, integralSupportHomologyRestriction_apply_comp,
    integralSupportHomologyRestriction_apply_comp, sub_eq_zero] at he
  exact he



structure IntegralLocalHomologyAtlas (X : Type u) [TopologicalSpace X] (d : Nat) where
  support : X → Set X
  baseSet : X → Set X
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  mem_baseSet : ∀ i, i ∈ baseSet i
  baseSet_subset_support : ∀ i, baseSet i ⊆ support i
  basis : ∀ i, Int ≃ₗ[Int] integralSupportHomology (support i) d
  restriction_isIso : ∀ i x (hx : x ∈ baseSet i),
    IsIso (integralSupportHomologyRestriction
      (singleton_subset_iff.mpr (baseSet_subset_support i hx)) d)

@[ext]
structure IntegralOrientationFiber where
  equiv : Int ≃ₗ[Int] Int

instance : Coe IntegralOrientationFiber (Int ≃ₗ[Int] Int) := ⟨IntegralOrientationFiber.equiv⟩

instance : TopologicalSpace IntegralOrientationFiber := ⊥

instance : DiscreteTopology IntegralOrientationFiber := ⟨rfl⟩

instance : Inhabited IntegralOrientationFiber := ⟨⟨LinearEquiv.refl Int Int⟩⟩

namespace IntegralLocalHomologyAtlas

variable {d : Nat} (A : IntegralLocalHomologyAtlas X d)

def localFrame (i x : X) (hx : x ∈ A.baseSet i) :
    Int ≃ₗ[Int] integralSupportHomology ({x} : Set X) d := by
  let := A.restriction_isIso i x hx
  exact (A.basis i).trans (asIso (integralSupportHomologyRestriction
    (singleton_subset_iff.mpr (A.baseSet_subset_support i hx)) d)).toLinearEquiv

@[simp]
theorem localFrame_apply (i x : X) (hx : x ∈ A.baseSet i) (z : Int) :
    A.localFrame i x hx z = integralSupportHomologyRestriction
      (singleton_subset_iff.mpr (A.baseSet_subset_support i hx)) d (A.basis i z) := rfl

def frame (i x : X) : Int ≃ₗ[Int] integralSupportHomology ({x} : Set X) d := by
  classical
  exact if hx : x ∈ A.baseSet i then A.localFrame i x hx else A.localFrame x x (A.mem_baseSet x)

theorem frame_apply (i x : X) (hx : x ∈ A.baseSet i) (z : Int) :
    A.frame i x z = integralSupportHomologyRestriction
      (singleton_subset_iff.mpr (A.baseSet_subset_support i hx)) d (A.basis i z) := by
  simp only [frame, dif_pos hx, localFrame_apply]

def coordChange (i j x : X) (a : IntegralOrientationFiber) : IntegralOrientationFiber :=
  ⟨((a : Int ≃ₗ[Int] Int).trans (A.frame i x)).trans (A.frame j x).symm⟩

@[simp]
theorem coordChange_apply (i j x : X) (a : IntegralOrientationFiber) (z : Int) :
    (A.coordChange i j x a : Int ≃ₗ[Int] Int) z =
      (A.frame j x).symm (A.frame i x ((a : Int ≃ₗ[Int] Int) z)) := rfl

theorem coordChange_self (i x : X) (a : IntegralOrientationFiber) :
    A.coordChange i i x a = a := by
  apply IntegralOrientationFiber.ext
  apply LinearEquiv.ext
  intro z
  simp only [coordChange_apply, LinearEquiv.symm_apply_apply]

theorem coordChange_comp (i j k x : X) (a : IntegralOrientationFiber) :
    A.coordChange j k x (A.coordChange i j x a) = A.coordChange i k x a := by
  apply IntegralOrientationFiber.ext
  apply LinearEquiv.ext
  intro z
  simp only [coordChange_apply, LinearEquiv.apply_symm_apply]

private theorem orientationFiber_ext {a b : IntegralOrientationFiber}
    (h : (a : Int ≃ₗ[Int] Int) 1 = (b : Int ≃ₗ[Int] Int) 1) : a = b := by
  apply IntegralOrientationFiber.ext
  apply LinearEquiv.ext
  intro z
  have ha : (a : Int ≃ₗ[Int] Int) z = z • (a : Int ≃ₗ[Int] Int) 1 := by
    simpa only [smul_eq_mul, mul_one] using (a : Int ≃ₗ[Int] Int).map_smul z 1
  have hb : (b : Int ≃ₗ[Int] Int) z = z • (b : Int ≃ₗ[Int] Int) 1 := by
    simpa only [smul_eq_mul, mul_one] using (b : Int ≃ₗ[Int] Int).map_smul z 1
  rw [ha, hb, h]

theorem exists_open_coordChange_eq [T2Space X]
    (i j x : X) (hx : x ∈ A.baseSet i ∩ A.baseSet j) (a : IntegralOrientationFiber) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ A.baseSet i ∩ A.baseSet j ∩ V,
        A.coordChange i j y a = A.coordChange i j x a := by
  let b := A.coordChange i j x a
  have hab : A.frame i x ((a : Int ≃ₗ[Int] Int) 1) =
      A.frame j x ((b : Int ≃ₗ[Int] Int) 1) := by
    simp only [b, coordChange_apply, LinearEquiv.apply_symm_apply]
  rw [A.frame_apply i x hx.1, A.frame_apply j x hx.2] at hab
  obtain ⟨V, hV, hxV, heq⟩ := exists_open_integralSupportHomology_restrictions_eq
    (A.support i) (A.support j) d (A.basis i ((a : Int ≃ₗ[Int] Int) 1))
    (A.basis j ((b : Int ≃ₗ[Int] Int) 1)) x
    (A.baseSet_subset_support i hx.1) (A.baseSet_subset_support j hx.2) hab
  refine ⟨V, hV, hxV, ?_⟩
  intro y hy
  apply orientationFiber_ext
  apply (A.frame j y).injective
  rw [coordChange_apply, LinearEquiv.apply_symm_apply,
    A.frame_apply i y hy.1.1, A.frame_apply j y hy.1.2]
  exact heq y ⟨⟨A.baseSet_subset_support i hy.1.1,
    A.baseSet_subset_support j hy.1.2⟩, hy.2⟩

theorem continuousOn_coordChange [T2Space X] (i j : X) :
    ContinuousOn (fun p : X × IntegralOrientationFiber => A.coordChange i j p.1 p.2)
      ((A.baseSet i ∩ A.baseSet j) ×ˢ univ) := by
  rw [continuousOn_prod_of_discrete_right]
  intro a x hx
  have hx' : x ∈ A.baseSet i ∩ A.baseSet j := hx.1
  obtain ⟨V, hV, hxV, heq⟩ := A.exists_open_coordChange_eq i j x hx' a
  have hc : ContinuousWithinAt (fun _ : X => A.coordChange i j x a)
      {y : X | (y, a) ∈ (A.baseSet i ∩ A.baseSet j) ×ˢ univ} x :=
    continuousWithinAt_const
  apply hc.congr_of_eventuallyEq_of_mem ?_ hx
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), self_mem_nhdsWithin]
    with y hyV hy
  exact heq y ⟨hy.1, hyV⟩

def orientationBundleCore [T2Space X] : FiberBundleCore X X IntegralOrientationFiber where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := id
  mem_baseSet_at := A.mem_baseSet
  coordChange := A.coordChange
  coordChange_self i x _ a := A.coordChange_self i x a
  continuousOn_coordChange := A.continuousOn_coordChange
  coordChange_comp i j k x _ a := A.coordChange_comp i j k x a

theorem orientationBundleCore_isCoveringMap [T2Space X] :
    IsCoveringMap A.orientationBundleCore.proj :=
  IsFiberBundle.isCoveringMap (fun x =>
    ⟨A.orientationBundleCore.localTriv x, A.mem_baseSet x⟩)

include A in
theorem exists_locallyRepresented_generators [T2Space X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x0 : X) :
    ∃ omega : ∀ x : X, integralSupportHomology ({x} : Set X) d,
      (∀ x : X, ∃ e : Int ≃ₗ[Int] integralSupportHomology ({x} : Set X) d,
        e 1 = omega x) ∧
      ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∃ b : integralSupportHomology U d,
          ∀ y : X, ∀ hy : y ∈ U,
            integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d b = omega y := by
  classical
  let Z := A.orientationBundleCore
  obtain ⟨s, hs, _⟩ := A.orientationBundleCore_isCoveringMap.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x0
    (show Z.TotalSpace from ⟨x0, (show Z.Fiber x0 from (default : IntegralOrientationFiber))⟩) rfl
  have hproj : ∀ x : X, (s x).1 = x := fun x => congrFun hs.2 x
  let a : X → IntegralOrientationFiber := fun x => (s x).2
  let omega : ∀ x : X, integralSupportHomology ({x} : Set X) d :=
    fun x => A.frame x x ((a x).equiv 1)
  refine ⟨omega, ?_, ?_⟩
  · intro x
    exact ⟨(a x).equiv.trans (A.frame x x), rfl⟩
  · intro x
    let c : X → IntegralOrientationFiber := fun y => (Z.localTriv x (s y)).2
    have hsource : s x ∈ (Z.localTriv x).source := by
      change (s x).1 ∈ A.baseSet x
      rw [hproj x]
      exact A.mem_baseSet x
    have hc : ContinuousAt c x :=
      (((Z.localTriv x).toOpenPartialHomeomorph.continuousAt hsource).comp
        s.continuous.continuousAt).snd
    have hcx : {y : X | c y = c x} ∈ nhds x :=
      hc.preimage_mem_nhds ((isOpen_discrete ({c x} : Set IntegralOrientationFiber)).mem_nhds
        (mem_singleton (c x)))
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp
      (inter_mem hcx ((A.isOpen_baseSet x).mem_nhds (A.mem_baseSet x)))
    have hUsupport : U ⊆ A.support x := fun y hy =>
      A.baseSet_subset_support x (hUsub hy).2
    refine ⟨U, hU, hxU,
      integralSupportHomologyRestriction hUsupport d (A.basis x ((c x).equiv 1)), ?_⟩
    intro y hy
    rw [integralSupportHomologyRestriction_apply_comp,
      ← A.frame_apply x y (hUsub hy).2]
    have hcy : c y = c x := (hUsub hy).1
    rw [← hcy]
    have hformula : c y = A.coordChange y x y (a y) := by
      dsimp only [c]
      rw [FiberBundleCore.localTriv_apply]
      change A.coordChange (s y).1 x (s y).1 (a y) = _
      rw [hproj y]
    rw [hformula]
    change A.frame x y ((A.coordChange y x y (a y) : Int ≃ₗ[Int] Int) 1) = omega y
    rw [coordChange_apply, LinearEquiv.apply_symm_apply]

end IntegralLocalHomologyAtlas

end PoincareConjecture.Proofs.M02.Topology
