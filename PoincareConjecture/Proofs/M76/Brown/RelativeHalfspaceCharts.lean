import PoincareConjecture.Proofs.M76.Brown.LocalPairChartCoordinates
import PoincareConjecture.Proofs.M76.Brown.SpindleHeight

set_option autoImplicit false

open Set

namespace BrownCollar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]

theorem exists_relative_halfspace_chart
    (q : OpenPartialHomeomorph (B × ℝ) X) (R : Set X)
    (hhalf : ∀ z ∈ q.source, q z ∈ R ↔ 0 ≤ z.2)
    (b : B) (hb : (b, (0 : ℝ)) ∈ q.source) :
    ∃ c : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) R,
      c.source = (fun z : B × Ico (0 : ℝ) 1 => (z.1, (z.2 : ℝ))) ⁻¹' q.source ∧
      c.target = {y : R | (y : X) ∈ q.target ∧ (q.symm (y : X)).2 < 1} ∧
      ∀ z ∈ c.source, (c z : X) = q (z.1, (z.2 : ℝ)) := by
  let F : B × Ico (0 : ℝ) 1 → B × ℝ := fun z => (z.1, z.2)
  have hF : Continuous F := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  let D : TopologicalSpace.Opens (B × Ico (0 : ℝ) 1) :=
    ⟨F ⁻¹' q.source, q.open_source.preimage hF⟩
  let T : TopologicalSpace.Opens R :=
    ⟨{y : R | (y : X) ∈ q.target ∧ (q.symm (y : X)).2 < 1}, by
      exact (q.symm.continuousOn.snd.isOpen_inter_preimage q.open_target
        isOpen_Iio).preimage continuous_subtype_val⟩
  have hnonneg (y : T) : 0 ≤ (q.symm (y.val : X)).2 := by
    apply (hhalf _ (q.map_target y.property.1)).mp
    rw [q.right_inv y.property.1]
    exact y.val.property
  let f : D ≃ₜ T :=
    { toFun := fun z => ⟨⟨q (F z.val),
        (hhalf _ z.property).mpr z.val.2.property.1⟩, q.map_source z.property, by
          change (q.symm (q (F z.val))).2 < 1
          rw [q.left_inv z.property]
          exact z.val.2.property.2⟩
      invFun := fun y => ⟨((q.symm (y.val : X)).1,
        ⟨(q.symm (y.val : X)).2, hnonneg y, y.property.2⟩),
          q.map_target y.property.1⟩
      left_inv := by
        intro z
        apply Subtype.ext
        have hf : (q.symm (q (F z.val))).1 = z.val.1 :=
          congrArg Prod.fst (q.left_inv z.property)
        have hs : (q.symm (q (F z.val))).2 = (z.val.2 : ℝ) :=
          congrArg Prod.snd (q.left_inv z.property)
        exact Prod.ext hf (Subtype.ext hs)
      right_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        exact q.right_inv y.property.1
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact q.continuousOn.comp_continuous (hF.comp continuous_subtype_val)
          (fun z => z.property)
      continuous_invFun := by
        have hc : Continuous (fun y : T => q.symm (y.val : X)) :=
          q.symm.continuousOn.comp_continuous
            (continuous_subtype_val.comp continuous_subtype_val)
            (fun y => y.property.1)
        apply Continuous.subtype_mk
        exact hc.fst.prodMk (hc.snd.subtype_mk _) }
  let d0 : D := ⟨collarBase b, hb⟩
  let id := D.openPartialHomeomorphSubtypeCoe ⟨d0⟩
  let it := T.openPartialHomeomorphSubtypeCoe ⟨f d0⟩
  have hidS : id.source = univ := rfl
  have hidT : id.target = (D : Set (B × Ico (0 : ℝ) 1)) :=
    D.openPartialHomeomorphSubtypeCoe_target ⟨d0⟩
  have hitS : it.source = univ := rfl
  have hitT : it.target = (T : Set R) :=
    T.openPartialHomeomorphSubtypeCoe_target ⟨f d0⟩
  let c := id.symm.trans (f.toOpenPartialHomeomorph.trans it)
  have hcS : c.source = F ⁻¹' q.source := by
    dsimp only [c]
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source, hitS, preimage_univ, inter_univ, hidT]
    rfl
  have hcT : c.target = (T : Set R) := by
    dsimp only [c]
    simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Homeomorph.toOpenPartialHomeomorph_target, hidS, preimage_univ, inter_univ, hitT]
  refine ⟨c, hcS, hcT, ?_⟩
  intro z hz
  let d : D := ⟨z, by
    change z ∈ F ⁻¹' q.source
    rw [← hcS]
    exact hz⟩
  have hinv : id.symm z = d := id.left_inv (x := d) (mem_univ d)
  change ((f (id.symm z) : T).val : X) = q (F z)
  rw [hinv]
  rfl

theorem exists_relative_halfspace_local_collar
    (q : OpenPartialHomeomorph (B × ℝ) X) (R : Set X)
    (hhalf : ∀ z ∈ q.source, q z ∈ R ↔ 0 ≤ z.2)
    (i : B → R) (hbase : ∀ a, (a, (0 : ℝ)) ∈ q.source → q (a, 0) = (i a : X))
    (b : B) (hb : (b, (0 : ℝ)) ∈ q.source) :
    ∃ c : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) R,
      collarBase b ∈ c.source ∧
        ∀ a, collarBase a ∈ c.source → c (collarBase a) = i a := by
  obtain ⟨c, hcS, _, hc⟩ := exists_relative_halfspace_chart q R hhalf b hb
  refine ⟨c, ?_, ?_⟩
  · rw [hcS]
    exact hb
  · intro a ha
    apply Subtype.ext
    rw [hc _ ha]
    change q (a, (0 : ℝ)) = (i a : X)
    apply hbase
    rw [hcS] at ha
    exact ha

end BrownCollar
