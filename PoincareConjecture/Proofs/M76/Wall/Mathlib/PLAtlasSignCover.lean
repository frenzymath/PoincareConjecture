import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasTransitionSigns
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Instances.Sign
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open Set Topology

namespace Geometry

abbrev PLOrientationSheet := {s : SignType // s ≠ 0}

def plOrientationSheetEquivBool : PLOrientationSheet ≃ Bool where
  toFun s := decide (s.val = 1)
  invFun b := if b then ⟨1, one_ne_zero⟩ else ⟨-1, by decide⟩
  left_inv s := by
    rcases s with ⟨s, hs⟩
    cases s with
    | zero => exact (hs rfl).elim
    | neg => rfl
    | pos => rfl
  right_inv b := by cases b <;> rfl

theorem nat_card_plOrientationSheet : Nat.card PLOrientationSheet = 2 := by
  rw [Nat.card_congr plOrientationSheetEquivBool,
    Nat.card_eq_fintype_card, Fintype.card_bool]

variable {X E ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private noncomputable def atlasSheetChange
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (U : Set X) (i j : ι) (x : U) (v : PLOrientationSheet) : PLOrientationSheet := by
  classical
  exact if h : (x : X) ∈ (e i).source ∩ (e j).source then
    ⟨plAtlasTransitionSign e hcompat i j ⟨x, h⟩ * v.val,
      mul_ne_zero (plAtlasTransitionSign_ne_zero e hcompat i j ⟨x, h⟩) v.property⟩
  else v

private theorem atlasSheetChange_val
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (U : Set X) (i j : ι) (x : U) (v : PLOrientationSheet)
    (hx : (x : X) ∈ (e i).source ∩ (e j).source) :
    (atlasSheetChange e hcompat U i j x v).val =
      plAtlasTransitionSign e hcompat i j ⟨x, hx⟩ * v.val := by
  classical
  simp only [atlasSheetChange, dif_pos hx]

private theorem continuousOn_atlasSheetChange
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (U : Set X) (i j : ι) :
    ContinuousOn (fun z : U × PLOrientationSheet => atlasSheetChange e hcompat U i j z.1 z.2)
      ({x : U | (x : X) ∈ (e i).source ∩ (e j).source} ×ˢ univ) := by
  let V : Set (U × PLOrientationSheet) :=
    {x : U | (x : X) ∈ (e i).source ∩ (e j).source} ×ˢ univ
  let q : V → ((e i).source ∩ (e j).source : Set X) :=
    fun z => ⟨z.val.1, z.property.1⟩
  have hq : Continuous q :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _
  have hs : Continuous (fun z : V => plAtlasTransitionSign e hcompat i j (q z)) :=
    (isLocallyConstant_plAtlasTransitionSign e hcompat i j).continuous.comp hq
  have hv : Continuous (fun z : V => (z.val.2 : SignType)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hm : Continuous (fun z : V =>
      plAtlasTransitionSign e hcompat i j (q z) * (z.val.2 : SignType)) :=
    (continuous_of_discreteTopology :
      Continuous (fun p : SignType × SignType => p.1 * p.2)).comp (hs.prodMk hv)
  have hc : Continuous (fun z : V =>
      (⟨plAtlasTransitionSign e hcompat i j (q z) * (z.val.2 : SignType),
        mul_ne_zero (plAtlasTransitionSign_ne_zero e hcompat i j (q z))
          z.val.2.property⟩ : PLOrientationSheet)) := hm.subtype_mk _
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun z : V => atlasSheetChange e hcompat U i j z.val.1 z.val.2)
  exact hc.congr (fun z => Subtype.ext
    (atlasSheetChange_val e hcompat U i j z.val.1 z.val.2 z.property.1).symm)

noncomputable def plAtlasSignCore
    (e : ι → OpenPartialHomeomorph X E)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (U : Set X) : FiberBundleCore ι U PLOrientationSheet where
  baseSet i := {x : U | (x : X) ∈ (e i).source}
  isOpen_baseSet i := (e i).open_source.preimage continuous_subtype_val
  indexAt x := (hcover x).choose
  mem_baseSet_at x := (hcover x).choose_spec
  coordChange := atlasSheetChange e hcompat U
  coordChange_self := by
    intro i x hx v
    apply Subtype.ext
    rw [atlasSheetChange_val e hcompat U i i x v ⟨hx, hx⟩,
      plAtlasTransitionSign_self e hcompat i ⟨x, hx⟩, one_mul]
  continuousOn_coordChange i j := continuousOn_atlasSheetChange e hcompat U i j
  coordChange_comp := by
    intro i j k x hx v
    apply Subtype.ext
    rw [atlasSheetChange_val e hcompat U j k x _ ⟨hx.1.2, hx.2⟩,
      atlasSheetChange_val e hcompat U i j x v hx.1,
      atlasSheetChange_val e hcompat U i k x v ⟨hx.1.1, hx.2⟩]
    simpa only [mul_assoc] using congrArg (fun s : SignType => s * v.val)
      (plAtlasTransitionSign_cocycle e hcompat i j k x hx.1.1 hx.1.2 hx.2)

variable (e : ι → OpenPartialHomeomorph X E)
  (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
  (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
  (U : Set X)

theorem plAtlasSignCore_coordChange (i j : ι) (x : U) (v : PLOrientationSheet)
    (hx : (x : X) ∈ (e i).source ∩ (e j).source) :
    ((plAtlasSignCore e hcover hcompat U).coordChange i j x v).val =
      plAtlasTransitionSign e hcompat i j ⟨x, hx⟩ * v.val :=
  atlasSheetChange_val e hcompat U i j x v hx

noncomputable def plAtlasSignFiberEquiv (x : U) :
    ((plAtlasSignCore e hcover hcompat U).proj ⁻¹' {x}) ≃ PLOrientationSheet where
  toFun z := z.val.2
  invFun v := ⟨⟨x, v⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨y, v⟩, hy⟩
    change y = x at hy
    cases hy
    rfl
  right_inv _ := rfl

theorem plAtlasSignCore_covering :
    let Z := plAtlasSignCore e hcover hcompat U
    IsCoveringMap Z.proj ∧ Continuous Z.proj ∧ IsOpenMap Z.proj ∧
      Function.Surjective Z.proj ∧ ∀ x : U, Nat.card (Z.proj ⁻¹' {x}) = 2 := by
  let Z := plAtlasSignCore e hcover hcompat U
  refine ⟨FiberBundle.isCoveringMap, Z.continuous_proj, Z.isOpenMap_proj, ?_, ?_⟩
  · intro x
    exact ⟨⟨x, ⟨1, one_ne_zero⟩⟩, rfl⟩
  · intro x
    exact (Nat.card_congr (plAtlasSignFiberEquiv e hcover hcompat U x)).trans
      nat_card_plOrientationSheet

theorem plAtlasSignCore_localTriv (i : ι) :
    let Z := plAtlasSignCore e hcover hcompat U
    (Z.localTriv i).source = Z.proj ⁻¹' {x : U | (x : X) ∈ (e i).source} ∧
      (Z.localTriv i).target = {x : U | (x : X) ∈ (e i).source} ×ˢ univ ∧
      (∀ (z : Z.TotalSpace) (hz : (z.proj : X) ∈ (e i).source),
        ((Z.localTriv i) z).1 = z.proj ∧
        (((Z.localTriv i) z).2 : SignType) =
          plAtlasTransitionSign e hcompat (Z.indexAt z.proj) i
            ⟨z.proj, Z.mem_baseSet_at z.proj, hz⟩ * (z.snd : PLOrientationSheet).val) ∧
      ∀ (x : U) (hx : (x : X) ∈ (e i).source) (v : PLOrientationSheet),
        ((Z.localTriv i).toOpenPartialHomeomorph.symm (x, v)).proj = x ∧
        (((Z.localTriv i).toOpenPartialHomeomorph.symm (x, v)).snd :
          PLOrientationSheet).val =
          plAtlasTransitionSign e hcompat i (Z.indexAt x)
            ⟨x, hx, Z.mem_baseSet_at x⟩ * v.val := by
  dsimp only
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro z hz
    refine ⟨rfl, ?_⟩
    exact plAtlasSignCore_coordChange e hcover hcompat U _ _ z.proj z.2
      ⟨(plAtlasSignCore e hcover hcompat U).mem_baseSet_at z.proj, hz⟩
  · intro x hx v
    refine ⟨rfl, ?_⟩
    exact plAtlasSignCore_coordChange e hcover hcompat U _ _ x v
      ⟨hx, (plAtlasSignCore e hcover hcompat U).mem_baseSet_at x⟩

theorem plAtlasSignCore_localTriv_change (i j : ι) (x : U)
    (hi : (x : X) ∈ (e i).source) (hj : (x : X) ∈ (e j).source)
    (v : PLOrientationSheet) :
    let Z := plAtlasSignCore e hcover hcompat U
    ((Z.localTriv j) ((Z.localTriv i).toOpenPartialHomeomorph.symm (x, v))).1 = x ∧
      (((Z.localTriv j) ((Z.localTriv i).toOpenPartialHomeomorph.symm (x, v))).2 :
        SignType) = plAtlasTransitionSign e hcompat i j ⟨x, hi, hj⟩ * v.val := by
  let Z := plAtlasSignCore e hcover hcompat U
  refine ⟨rfl, ?_⟩
  change (Z.coordChange (Z.indexAt x) j x (Z.coordChange i (Z.indexAt x) x v)).val = _
  rw [Z.coordChange_comp i (Z.indexAt x) j x ⟨⟨hi, Z.mem_baseSet_at x⟩, hj⟩ v]
  exact plAtlasSignCore_coordChange e hcover hcompat U i j x v ⟨hi, hj⟩

end Geometry
