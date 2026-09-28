import PoincareConjecture.Proofs.M54.Mathlib.PathMaps
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set
open scoped unitInterval

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def ofSetInverse (f : X → Y) (g : Y → X) (s : Set X) (t : Set Y)
    (hf : ContinuousOn f s) (hg : ContinuousOn g t)
    (hfst : MapsTo f s t) (hgts : MapsTo g t s)
    (hgf : LeftInvOn g f s) (hfg : LeftInvOn f g t) : s ≃ₜ t where
  toFun x := ⟨f x, hfst x.2⟩
  invFun y := ⟨g y, hgts y.2⟩
  left_inv x := Subtype.ext (hgf x.2)
  right_inv y := Subtype.ext (hfg y.2)
  continuous_toFun := hf.domRestrict.subtype_mk _
  continuous_invFun := hg.domRestrict.subtype_mk _

noncomputable def fundamentalGroupMulEquiv (e : X ≃ₜ Y) (b : X) :
    FundamentalGroup X b ≃* FundamentalGroup Y (e b) :=
  MulEquiv.ofBijective (FundamentalGroup.map (e : C(X, Y)) b) (by
    constructor
    · intro p q hpq
      induction p using Path.Homotopic.Quotient.ind with
      | mk p =>
        induction q using Path.Homotopic.Quotient.ind with
        | mk q =>
          have h := (Path.Homotopic.Quotient.eq.mp hpq).map (e.symm : C(Y, X))
          have h' := h.pathCast (e.symm_apply_apply b).symm (e.symm_apply_apply b).symm
          apply Path.Homotopic.Quotient.eq.mpr
          convert h' using 1 <;> apply Path.ext <;> funext t <;> exact (e.symm_apply_apply _).symm
    · intro q
      induction q using Path.Homotopic.Quotient.ind with
      | mk q =>
        let p := (q.map e.symm.continuous).cast
          (e.symm_apply_apply b).symm (e.symm_apply_apply b).symm
        refine ⟨Path.Homotopic.Quotient.mk p, ?_⟩
        change Path.Homotopic.Quotient.mk (p.map e.continuous) = Path.Homotopic.Quotient.mk q
        congr 1
        ext t
        exact e.apply_symm_apply (q t))

end Homeomorph

theorem simplyConnectedSpace_prod_contractible (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [ContractibleSpace Y] : SimplyConnectedSpace (X × Y) := by
  let e := (ContinuousMap.HomotopyEquiv.refl X).prodCongr (ContractibleSpace.hequiv Y Unit).some
  exact (e.trans (Homeomorph.prodUnique X Unit).toHomotopyEquiv).simplyConnectedSpace

namespace IsClopen

variable {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]

theorem map_mem [PreconnectedSpace T] {U : Set X} (hU : IsClopen U)
    {f : T → X} (hf : Continuous f) (t : T) (ht : f t ∈ U) (s : T) : f s ∈ U := by
  exact (isPreconnected_range hf).subset_isClopen hU ⟨f t, ⟨t, rfl⟩, ht⟩ ⟨s, rfl⟩

noncomputable def fundamentalGroupMulEquiv {U : Set X} (hU : IsClopen U) (b : U) :
    FundamentalGroup U b ≃* FundamentalGroup X b.1 :=
  MulEquiv.ofBijective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ b) (by
    constructor
    · intro p q hpq
      induction p using Path.Homotopic.Quotient.ind with
      | mk p =>
        induction q using Path.Homotopic.Quotient.ind with
        | mk q =>
          obtain ⟨H⟩ := Path.Homotopic.Quotient.eq.mp hpq
          have hH : ∀ z, H z ∈ U :=
            hU.map_mem H.continuous (0, 0) (by simp)
          apply Path.Homotopic.Quotient.eq.mpr
          exact ⟨{
            toFun := fun z => ⟨H z, hH z⟩
            continuous_toFun := H.continuous.subtype_mk hH
            map_zero_left := fun t => Subtype.ext (H.map_zero_left t)
            map_one_left := fun t => Subtype.ext (H.map_one_left t)
            prop' := fun t s hs => Subtype.ext (H.prop' t s hs) }⟩
    · intro q
      induction q using Path.Homotopic.Quotient.ind with
      | mk q =>
        have hq : ∀ t, q t ∈ U := hU.map_mem q.continuous 0 (by simp)
        let p : Path b b := ⟨⟨fun t => ⟨q t, hq t⟩, q.continuous.subtype_mk hq⟩,
          Subtype.ext q.source, Subtype.ext q.target⟩
        exact ⟨Path.Homotopic.Quotient.mk p, rfl⟩)

end IsClopen
