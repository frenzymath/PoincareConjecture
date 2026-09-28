import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachmentEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem commonCollarAttachment_middle
    {E X Z : Type*} (c : E × ℝ → X) (rim : Bool → Z → E)
    (G : X → X) (f : ℝ × Z → X) (a : ℝ) {A : Set Z}
    (hbase : ∀ b z, z ∈ A → c (rim b z, 0) = f (if b then 1 else -1, z))
    (hlevel : ∀ b z, z ∈ A → G (c (rim b z, 0)) = c (rim b z, a))
    {z : ℝ × Z} (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ A) :
    commonCollarAttachment c rim G f a z = G (f z) := by
  unfold commonCollarAttachment
  split_ifs with hlow hhigh
  · have ht : z.1 = -1 := le_antisymm hlow hz.1.1
    rw [ht]
    have hh := (hlevel false z.2 hz.2).symm.trans (congrArg G (hbase false z.2 hz.2))
    have hzEq : z = (-1, z.2) := Prod.ext ht rfl
    rw [hzEq]
    norm_num at hh ⊢
    exact hh
  · have ht : z.1 = 1 := le_antisymm hz.1.2 hhigh
    rw [ht]
    have hh := (hlevel true z.2 hz.2).symm.trans (congrArg G (hbase true z.2 hz.2))
    have hzEq : z = (1, z.2) := Prod.ext ht rfl
    rw [hzEq]
    norm_num at hh ⊢
    exact hh
  · rfl

theorem continuousOn_commonCollarAttachment
    {E X Z : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Z]
    (c : E × ℝ → X) (rim : Bool → Z → E)
    {K : Set E} {A : Set Z} (hA : IsClosed A) {a : ℝ} (ha : 0 < a)
    (hc : ContinuousOn c (K ×ˢ Icc (0 : ℝ) a))
    (hrim : ∀ b, MapsTo (rim b) A K) (hcrim : ∀ b, ContinuousOn (rim b) A)
    (G : X → X) (hG : Continuous G)
    (f : ℝ × Z → X) (hf : ContinuousOn f (Icc (-1 : ℝ) 1 ×ˢ A))
    (hbase : ∀ b z, z ∈ A → c (rim b z, 0) = f (if b then 1 else -1, z))
    (hlevel : ∀ b z, z ∈ A → G (c (rim b z, 0)) = c (rim b z, a)) :
    ContinuousOn (commonCollarAttachment c rim G f a) (Icc (-2 : ℝ) 2 ×ˢ A) := by
  let L := Icc (-2 : ℝ) (-1) ×ˢ A
  let M := Icc (-1 : ℝ) 1 ×ˢ A
  let U := Icc (1 : ℝ) 2 ×ˢ A
  have hL : ContinuousOn (commonCollarAttachment c rim G f a) L := by
    have hparam : ContinuousOn (fun z : ℝ × Z => (rim false z.2, a * (z.1 + 2))) L :=
      ((hcrim false).comp continuous_snd.continuousOn (fun _ hz => hz.2)).prodMk
        (continuous_const.mul (continuous_fst.add continuous_const)).continuousOn
    have hmap : MapsTo (fun z : ℝ × Z => (rim false z.2, a * (z.1 + 2))) L
        (K ×ˢ Icc (0 : ℝ) a) := by
      intro z hz
      refine ⟨hrim false hz.2, ?_, ?_⟩ <;> nlinarith [hz.1.1, hz.1.2]
    apply (hc.comp hparam hmap).congr
    intro z hz
    exact if_pos hz.1.2
  have hM : ContinuousOn (commonCollarAttachment c rim G f a) M :=
    (hG.comp_continuousOn hf).congr (fun _ hz => commonCollarAttachment_middle c rim G f a hbase hlevel hz)
  have hU : ContinuousOn (commonCollarAttachment c rim G f a) U := by
    have hparam : ContinuousOn (fun z : ℝ × Z => (rim true z.2, a * (2 - z.1))) U :=
      ((hcrim true).comp continuous_snd.continuousOn (fun _ hz => hz.2)).prodMk
        (continuous_const.mul (continuous_const.sub continuous_fst)).continuousOn
    have hmap : MapsTo (fun z : ℝ × Z => (rim true z.2, a * (2 - z.1))) U
        (K ×ˢ Icc (0 : ℝ) a) := by
      intro z hz
      refine ⟨hrim true hz.2, ?_, ?_⟩ <;> nlinarith [hz.1.1, hz.1.2]
    apply (hc.comp hparam hmap).congr
    intro z hz
    simp only [commonCollarAttachment, if_neg (show ¬z.1 ≤ -1 by linarith [hz.1.1]),
      if_pos hz.1.1, Function.comp_apply]
  have hclosedL : IsClosed L := isClosed_Icc.prod hA
  have hclosedM : IsClosed M := isClosed_Icc.prod hA
  have hclosedU : IsClosed U := isClosed_Icc.prod hA
  have hcover : (L ∪ M) ∪ U = Icc (-2 : ℝ) 2 ×ˢ A := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
      · exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
      · exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩
    · intro hz
      by_cases hlow : z.1 ≤ -1
      · exact Or.inl (Or.inl ⟨⟨hz.1.1, hlow⟩, hz.2⟩)
      · by_cases hhigh : 1 ≤ z.1
        · exact Or.inr ⟨⟨hhigh, hz.1.2⟩, hz.2⟩
        · exact Or.inl (Or.inr ⟨⟨(lt_of_not_ge hlow).le, (lt_of_not_ge hhigh).le⟩, hz.2⟩)
  rw [← hcover]
  exact (hL.union_of_isClosed hM hclosedL hclosedM).union_of_isClosed hU
    (hclosedL.union hclosedM) hclosedU

end PoincareConjecture.M76
