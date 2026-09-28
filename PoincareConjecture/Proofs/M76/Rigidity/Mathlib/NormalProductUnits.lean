import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.NormalProductTransitions
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.LocallyConnectedNormalSigns
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open Set Bundle

namespace BrownCollar

theorem exists_coherent_normal_product_units
    {P X ι : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [LocallyConnectedSpace P] [SimplyConnectedSpace P]
    [LocallyPathConnectedSpace P] [Nonempty P]
    (q : ι → OpenPartialHomeomorph (P × ℝ) X) (b : P → X) (S : Set X)
    (hzero : ∀ i x, (x, (0 : ℝ)) ∈ (q i).source → q i (x, 0) = b x)
    (hpair : ∀ i z, z ∈ (q i).source → (q i z ∈ S ↔ z.2 = 0))
    (hcover : ∀ x : P, ∃ i, (x, (0 : ℝ)) ∈ (q i).source) :
    ∃ a : ι → P → SignTypeˣ,
      (∀ i, ContinuousOn (a i) {x | (x, (0 : ℝ)) ∈ (q i).source}) ∧
      ∀ i j x, (x, (0 : ℝ)) ∈ (q i).source → (x, (0 : ℝ)) ∈ (q j).source →
        NormalSignAt ((q i).trans (q j).symm) x
          ((a j x : SignType) * (a i x : SignType)) := by
  classical
  let B (i : ι) : Set P := {x | (x, (0 : ℝ)) ∈ (q i).source}
  have hB (i : ι) : IsOpen (B i) :=
    (q i).open_source.preimage (continuous_id.prodMk continuous_const)
  let t (i j : ι) := (q i).trans (q j).symm
  have ht (i j : ι) : ∀ z ∈ (t i j).source, (t i j z).2 = 0 ↔ z.2 = 0 :=
    normal_product_transition_pair (q i) (q j) S (hpair i) (hpair j)
  have hbase (i j : ι) (x : P) (hx : x ∈ B i ∩ B j) :
      (x, (0 : ℝ)) ∈ (t i j).source ∧ t i j (x, 0) = (x, 0) :=
    normal_product_transition_base (q i) (q j) x hx.1 hx.2
      ((hzero i x hx.1).trans (hzero j x hx.2).symm)
  let c (i j : ι) (x : P) : SignType :=
    if hx : x ∈ B i ∩ B j then
      locallyConnectedNormalTransitionSign (t i j) (ht i j) ⟨x, (hbase i j x hx).1⟩
    else 1
  have hcspec (i j : ι) (x : P) (hx : x ∈ B i ∩ B j) :
      NormalSignAt (t i j) x (c i j x) := by
    dsimp only [c]
    rw [dif_pos hx]
    exact locallyConnectedNormalTransitionSign_spec _ _ _
  have hcne (i j : ι) (x : P) : c i j x ≠ 0 := by
    by_cases hx : x ∈ B i ∩ B j
    · exact (hcspec i j x hx).1
    · dsimp only [c]
      rw [dif_neg hx]
      exact one_ne_zero
  have hcself (i : ι) (x : P) (hx : x ∈ B i) : c i i x = 1 := by
    apply (hcspec i i x ⟨hx, hx⟩).unique
    refine ⟨one_ne_zero, (t i i).source, (t i i).open_source,
      (hbase i i x ⟨hx, hx⟩).1, subset_rfl, ?_⟩
    intro z hz
    change SignType.sign ((q i).symm (q i z)).2 = 1 * SignType.sign z.2
    rw [(q i).left_inv hz.1, one_mul]
  have hccocycle (i j k : ι) (x : P) (hx : x ∈ B i ∩ B j ∩ B k) :
      c j k x * c i j x = c i k x :=
    normal_product_sign_cocycle (q i) (q j) (q k) x (hbase i j x hx.1).2
      (hcspec i j x hx.1) (hcspec j k x ⟨hx.1.2, hx.2⟩)
      (hcspec i k x ⟨hx.1.1, hx.2⟩)
  have hcc (i j : ι) : ContinuousOn (c i j) (B i ∩ B j) := by
    let f : ↥(B i ∩ B j) → {x : P // (x, (0 : ℝ)) ∈ (t i j).source} :=
      fun x => ⟨x, (hbase i j x x.property).1⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    have h := (locallyConnectedNormalTransitionSign_isLocallyConstant
      (t i j) (ht i j)).continuous.comp hf
    rw [continuousOn_iff_continuous_domRestrict]
    convert h using 1
    funext x
    exact dif_pos x.property
  let d (i j : ι) (x : P) : SignTypeˣ := Units.mk0 (c i j x) (hcne i j x)
  have hdself (i : ι) (x : P) (hx : x ∈ B i) : d i i x = 1 := by
    apply Units.ext
    exact hcself i x hx
  have hdcocycle (i j k : ι) (x : P) (hx : x ∈ B i ∩ B j ∩ B k) :
      d j k x * d i j x = d i k x := by
    apply Units.ext
    exact hccocycle i j k x hx
  have hdc (i j : ι) : ContinuousOn (d i j) (B i ∩ B j) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply Units.continuous_iff.mpr
    exact ⟨(hcc i j).domRestrict, (hcc i j).domRestrict⟩
  choose indexAt hindex using hcover
  let Z : FiberBundleCore ι P SignTypeˣ := {
    baseSet := B
    isOpen_baseSet := hB
    indexAt := indexAt
    mem_baseSet_at := hindex
    coordChange := fun i j x v => d i j x * v
    coordChange_self := fun i x hx v => by rw [hdself i x hx, one_mul]
    continuousOn_coordChange := fun i j =>
      ((hdc i j).comp continuous_fst.continuousOn (fun _ h => h.1)).mul
        continuous_snd.continuousOn
    coordChange_comp := fun i j k x hx v => by
      rw [← mul_assoc, hdcocycle i j k x hx] }
  have hZ : IsCoveringMap Z.proj := FiberBundle.isCoveringMap
  let x0 : P := Classical.choice inferInstance
  let z0 : Z.TotalSpace := ⟨x0, (1 : SignTypeˣ)⟩
  obtain ⟨sigma, ⟨_, hsigma⟩, _⟩ :=
    hZ.existsUnique_continuousMap_lifts (ContinuousMap.id P) x0 z0 rfl
  have hs (x : P) : Z.proj (sigma x) = x := congrFun hsigma x
  let a (i : ι) (x : P) : SignTypeˣ := (Z.localTriv i (sigma x)).2
  have hac (i : ι) : ContinuousOn (a i) (B i) := by
    have hsource : ∀ x ∈ B i, sigma x ∈ (Z.localTriv i).source := by
      intro x hx
      change (sigma x).proj ∈ B i
      have hp : (sigma x).proj = x := hs x
      rwa [hp]
    exact ((Z.localTriv i).continuousOn.comp sigma.continuous.continuousOn hsource).snd
  have ha (i j : ι) (x : P) (hx : x ∈ B i ∩ B j) :
      a j x = d i j x * a i x := by
    have hp : (sigma x).proj = x := hs x
    change Z.coordChange (Z.indexAt (sigma x).proj) j (sigma x).proj (sigma x).snd =
      d i j x * Z.coordChange (Z.indexAt (sigma x).proj) i (sigma x).proj (sigma x).snd
    rw [hp]
    exact (Z.coordChange_comp (Z.indexAt x) i j x
      ⟨⟨Z.mem_baseSet_at x, hx.1⟩, hx.2⟩ (sigma x).snd).symm
  refine ⟨a, hac, ?_⟩
  intro i j x hxi hxj
  have haval : (a j x : SignType) = c i j x * (a i x : SignType) :=
    congrArg (fun v : SignTypeˣ => (v : SignType)) (ha i j x ⟨hxi, hxj⟩)
  have hsq : (a i x : SignType) * (a i x : SignType) = 1 :=
    mul_inv_cancel₀ (Units.ne_zero (a i x))
  rw [haval, mul_assoc, hsq, mul_one]
  exact hcspec i j x ⟨hxi, hxj⟩

end BrownCollar
