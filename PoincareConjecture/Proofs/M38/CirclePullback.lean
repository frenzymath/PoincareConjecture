import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Circle
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable {M : Type*} [TopologicalSpace M]

def CirclePullback (π : M → UnitCircle) :=
  {p : M × ℝ // π p.1 = unitCircleExp p.2}

namespace CirclePullback

variable (π : M → UnitCircle)

instance : TopologicalSpace (CirclePullback π) :=
  inferInstanceAs (TopologicalSpace {p : M × ℝ // π p.1 = unitCircleExp p.2})

def projection (a : CirclePullback π) : M := a.val.1

def height (a : CirclePullback π) : ℝ := a.val.2

theorem continuous_projection : Continuous (projection π) := continuous_fst.comp continuous_subtype_val

theorem continuous_height : Continuous (height π) := continuous_snd.comp continuous_subtype_val

omit [TopologicalSpace M] in
theorem projection_height (a : CirclePullback π) :
    π (projection π a) = unitCircleExp (height π a) := a.property

omit [TopologicalSpace M] in
theorem projection_surjective : Function.Surjective (projection π) := by
  intro x
  obtain ⟨t, ht⟩ := unitCircleExp_surjective (π x)
  exact ⟨⟨(x, t), ht.symm⟩, rfl⟩

theorem projection_isLocalHomeomorph (hπ : Continuous π) :
    IsLocalHomeomorph (projection π) := by
  classical
  intro a
  let h := isLocalDiffeomorph_unitCircleExp (height π a)
  let e := h.localInverse.toOpenPartialHomeomorph
  let L : M → CirclePullback π := fun x =>
    if hx : π x ∈ e.source then ⟨(x, e (π x)), (h.localInverse_right_inv hx).symm⟩ else a
  have hL (x : M) (hx : π x ∈ e.source) : (L x).val = (x, e (π x)) := by
    simp only [L, dif_pos hx]
  have hsource (b : CirclePullback π) (hb : height π b ∈ e.target) :
      π (projection π b) ∈ e.source := by
    rw [projection_height π b]
    change unitCircleExp (height π b) ∈ h.choose.target
    rw [h.choose_spec.2 hb]
    exact h.choose.map_source hb
  have hleft (b : CirclePullback π) (hb : height π b ∈ e.target) :
      L (projection π b) = b := by
    apply Subtype.ext
    rw [hL _ (hsource b hb)]
    apply Prod.ext
    · rfl
    change h.localInverse (π (projection π b)) = height π b
    rw [projection_height π b]
    exact h.localInverse_left_inv hb
  let C : OpenPartialHomeomorph (CirclePullback π) M := {
    toFun := projection π
    invFun := L
    source := height π ⁻¹' e.target
    target := π ⁻¹' e.source
    map_source' := hsource
    map_target' := by
      intro x hx
      change (L x).val.2 ∈ e.target
      rw [hL x hx]
      exact e.map_source hx
    left_inv' := hleft
    right_inv' := by
      intro x hx
      change (L x).val.1 = x
      rw [hL x hx]
    open_source := e.open_target.preimage (continuous_height π)
    open_target := e.open_source.preimage hπ
    continuousOn_toFun := (continuous_projection π).continuousOn
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (continuous_id.continuousOn.prodMk
        (e.continuousOn.comp hπ.continuousOn (fun _ hx => hx))).congr
      intro x hx
      exact hL x hx }
  exact ⟨C, h.localInverse_mem_target, rfl⟩

instance : AddAction ℤ (CirclePullback π) where
  vadd n a := ⟨(projection π a, height π a + n),
    (projection_height π a).trans (unitCircleExp_add_int (height π a) n).symm⟩
  zero_vadd a := by
    apply Subtype.ext
    change (a.val.1, a.val.2 + ((0 : ℤ) : ℝ)) = a.val
    simp only [Int.cast_zero, add_zero]
  add_vadd n m a := by
    apply Subtype.ext
    change (a.val.1, a.val.2 + ((n + m : ℤ) : ℝ)) =
      (a.val.1, (a.val.2 + m) + n)
    simp only [Int.cast_add]
    congr 1
    ring

omit [TopologicalSpace M] in
theorem projection_vadd (n : ℤ) (a : CirclePullback π) :
    projection π (n +ᵥ a) = projection π a := rfl

omit [TopologicalSpace M] in
theorem height_vadd (n : ℤ) (a : CirclePullback π) :
    height π (n +ᵥ a) = height π a + n := rfl

instance : ContinuousConstVAdd ℤ (CirclePullback π) where
  continuous_const_vadd _n :=
    (continuous_projection π |>.prodMk ((continuous_height π).add continuous_const)).subtype_mk _

theorem projection_isAddQuotientCoveringMap (hπ : Continuous π) :
    IsAddQuotientCoveringMap (projection π) ℤ where
  toIsQuotientMap := (projection_isLocalHomeomorph π hπ).isOpenMap.isQuotientMap
    (continuous_projection π) (projection_surjective π)
  apply_eq_iff_mem_orbit := by
    intro a b
    constructor
    · intro hab
      have he : unitCircleExp (height π a) = unitCircleExp (height π b) :=
        (projection_height π a).symm.trans ((congrArg π hab).trans (projection_height π b))
      obtain ⟨n, hn⟩ := unitCircleExp_eq_iff.mp he
      refine ⟨n, Subtype.ext ?_⟩
      exact Prod.ext hab.symm hn.symm
    · rintro ⟨n, rfl⟩
      rfl
  disjoint a := by
    refine ⟨height π ⁻¹' Ioo (height π a - 1 / 4) (height π a + 1 / 4),
      ((continuous_height π).isOpen_preimage _ isOpen_Ioo).mem_nhds
        (by constructor <;> linarith), ?_⟩
    intro n hn
    obtain ⟨b, ⟨d, hd, rfl⟩, hb⟩ := hn
    change height π a - 1 / 4 < height π d + n ∧
      height π d + n < height π a + 1 / 4 at hb
    have hlo : (-1 : ℝ) < n := by linarith [hd.1, hd.2, hb.1, hb.2]
    have hhi : (n : ℝ) < 1 := by linarith [hd.1, hd.2, hb.1, hb.2]
    have hlo' : (-1 : ℤ) < n := by exact_mod_cast hlo
    have hhi' : n < (1 : ℤ) := by exact_mod_cast hhi
    omega

theorem height_isProperMap [CompactSpace M] (hπ : Continuous π) :
    IsProperMap (height π) := by
  have hclosed : IsClosed {p : M × ℝ | π p.1 = unitCircleExp p.2} :=
    isClosed_eq (hπ.comp continuous_fst)
      (contMDiff_unitCircleExp.continuous.comp continuous_snd)
  exact isProperMap_snd_of_compactSpace.comp hclosed.isProperMap_subtypeVal

end CirclePullback

end PoincareConjecture.M38
