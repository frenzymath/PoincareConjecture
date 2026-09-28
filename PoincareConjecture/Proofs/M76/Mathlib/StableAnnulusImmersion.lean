import PoincareConjecture.Proofs.M76.Mathlib.StableAnnulusMap
import PoincareConjecture.Proofs.M76.Mathlib.TorusCrossingBandImmersion

set_option autoImplicit false

open Set Geometry

namespace StableAnnulus

theorem exists_stable_circle_PL_immersion :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    ∃ f : (AddCircle (4 * (16 : ℝ)) × ℝ) → ℝ × ℝ,
      IsLocalHomeomorphOn f (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo f (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo f (univ ×ˢ Ioo (-1 / 2) (1 / 2)) (univ ×ˢ Ioo (-1 / 2) (1 / 2)) ∧
      (∀ z ∈ univ ×ˢ Ioo (-1) 1, |(f z).1| ≤ 9) ∧
      (∀ s : ℝ, |s| ≤ 1 → ∀ t ∈ Ioo (-1) 1,
        f ((s : AddCircle (4 * (16 : ℝ))), t) = (s, t)) ∧
      ∀ a : ℝ,
        let Q := (AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) a).prod
          (OpenPartialHomeomorph.refl ℝ)
        LocallyPiecewiseAffineOn (f ∘ Q)
          (Q.source ∩ Q ⁻¹' (univ ×ˢ Ioo (-1) 1)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let p : ℝ := 4 * 16
  let U : Set (AddCircle p × ℝ) := univ ×ˢ Ioo (-1) 1
  let A : Set (AddCircle p) := ((↑) : ℝ → AddCircle p) '' Ioo (-6) 6
  let C : Set (AddCircle p) := ((↑) : ℝ → AddCircle p) '' Icc (-5) 5
  have hA : IsOpen A := by
    rw [show A = (AddCircle.shortArcQuotient p 6).target from
      (AddCircle.shortArcQuotient_target p (by norm_num [p])).symm]
    exact (AddCircle.shortArcQuotient p 6).open_target
  have hC : IsClosed C :=
    (isCompact_Icc.image (AddCircle.continuous_mk' p)).isClosed
  have hCA : C ⊆ A := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
  obtain ⟨e, heS, heval, hePL⟩ :=
    PLAnnularStrip.exists_centeredAnnulus_PL_openPartialHomeomorph
      (L := (16 : ℝ)) (d := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  let b := e.trans squash.toOpenPartialHomeomorph
  let m := b.trans expand.toOpenPartialHomeomorph
  let E := m.restr (A ×ˢ univ)
  let B := b.restr (Cᶜ ×ˢ univ)
  have hbS : b.source = U := by
    ext z
    change (z ∈ e.source ∧ e z ∈ univ) ↔ z ∈ U
    rw [heS]
    exact and_iff_left (mem_univ _)
  have hmS : m.source = U := by
    ext z
    change (z ∈ b.source ∧ b z ∈ univ) ↔ z ∈ U
    rw [hbS]
    exact and_iff_left (mem_univ _)
  have hES : E.source = A ×ˢ Ioo (-1) 1 := by
    rw [OpenPartialHomeomorph.restr_source, (hA.prod isOpen_univ).interior_eq, hmS]
    ext z
    simp only [U, mem_inter_iff, mem_prod, mem_univ, true_and, and_true]
    exact and_comm
  have hBS : B.source = Cᶜ ×ˢ Ioo (-1) 1 := by
    rw [OpenPartialHomeomorph.restr_source, (hC.isOpen_compl.prod isOpen_univ).interior_eq, hbS]
    ext z
    simp only [U, mem_inter_iff, mem_prod, mem_univ, true_and, and_true]
    exact and_comm
  have hcover : E.source ∪ B.source = U := by
    rw [hES, hBS]
    ext z
    constructor
    · rintro (hz | hz)
      · exact ⟨mem_univ _, hz.2⟩
      · exact ⟨mem_univ _, hz.2⟩
    · intro hz
      by_cases hzC : z.1 ∈ C
      · exact Or.inl ⟨hCA hzC, hz.2⟩
      · exact Or.inr ⟨hzC, hz.2⟩
  have hmiddle (s : ℝ) (hs : s ∈ Ioo (-6) 6) (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      e ((s : AddCircle p), t) = (s, t) := by
    rw [heval]
    have ht' : |t| < 1 := abs_lt.mpr ht
    apply PLAnnularStrip.centeredAnnulusMap_middle (by norm_num)
    · linarith
    · norm_num
      linarith [hs.1]
    · norm_num
      linarith [hs.2]
  have hEB : EqOn E B (E.source ∩ B.source) := by
    intro z hz
    have hzE : z ∈ A ×ˢ Ioo (-1) 1 := hES ▸ hz.1
    have hzB : z ∈ Cᶜ ×ˢ Ioo (-1) 1 := hBS ▸ hz.2
    obtain ⟨s, hs, hsval⟩ := hzE.1
    have hs5 : 5 < |s| := by
      by_contra hn
      have hsC : s ∈ Icc (-5) 5 := abs_le.mp (le_of_not_gt hn)
      exact hzB.1 ⟨s, hsC, hsval⟩
    have hzval : z = ((s : AddCircle p), z.2) := Prod.ext hsval.symm rfl
    change expand (squash (e z)) = squash (e z)
    rw [hzval, hmiddle s hs z.2 hzE.2]
    exact expand_squash_outer hs5 (abs_lt.mpr hzE.2)
  obtain ⟨f, hf, hfE, hfB⟩ := E.exists_union_localHomeomorph B hEB
  refine ⟨f, (show IsLocalHomeomorphOn f U from hcover ▸ hf), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hzunion : z ∈ E.source ∪ B.source := hcover.symm ▸ hz
    rcases hzunion with hzE | hzB
    · rw [hfE hzE]
      have hzE' : z ∈ A ×ˢ Ioo (-1) 1 := hES ▸ hzE
      obtain ⟨s, hs, hsval⟩ := hzE'.1
      have hzval : z = ((s : AddCircle p), z.2) := Prod.ext hsval.symm rfl
      refine ⟨mem_univ _, ?_⟩
      change (expand (squash (e z))).2 ∈ Ioo (-1) 1
      rw [hzval, hmiddle s hs z.2 hzE'.2]
      exact expand_squash_snd_mem s (abs_lt.mpr hzE'.2)
    · rw [hfB hzB]
      have hzB' : z ∈ Cᶜ ×ˢ Ioo (-1) 1 := hBS ▸ hzB
      have hheight := PLAnnularStrip.centeredAnnulusMap_snd_mem
        (L := (16 : ℝ)) (d := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
          z.1 ⟨hzB'.2.1.le, hzB'.2.2.le⟩
      refine ⟨mem_univ _, ?_⟩
      change (e z).2 / 64 ∈ Ioo (-1) 1
      rw [heval]
      constructor <;> norm_num at hheight ⊢ <;> linarith [hheight.1, hheight.2]
  · intro z hz
    have hzU : z ∈ U := ⟨mem_univ _, by
      constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hzunion : z ∈ E.source ∪ B.source := hcover.symm ▸ hzU
    rcases hzunion with hzE | hzB
    · rw [hfE hzE]
      have hzE' : z ∈ A ×ˢ Ioo (-1) 1 := hES ▸ hzE
      obtain ⟨s, hs, hsval⟩ := hzE'.1
      have hzval : z = ((s : AddCircle p), z.2) := Prod.ext hsval.symm rfl
      refine ⟨mem_univ _, ?_⟩
      change (expand (squash (e z))).2 ∈ Ioo (-1 / 2) (1 / 2)
      rw [hzval, hmiddle s hs z.2 hzE'.2]
      have hb := PLFiberCompression.abs_value_le
        (delta := (64 : ℝ)) (w := width s) (t := z.2 / 64)
          (by norm_num) (le_max_left _ _)
      have hb' : 64 * |z.2 / 64| = |z.2| := by rw [abs_div]; norm_num; ring
      have htHalf : |z.2| < (1 / 2 : ℝ) :=
        abs_lt.mpr ⟨by linarith [hz.2.1], hz.2.2⟩
      change PLFiberCompression.value 64 (width s) (z.2 / 64) ∈ Ioo (-1 / 2) (1 / 2)
      simpa only [mem_Ioo, neg_div] using abs_lt.mp (lt_of_le_of_lt (hb.trans_eq hb') htHalf)
    · rw [hfB hzB]
      have hheight := PLAnnularStrip.centeredAnnulusMap_snd_mem
        (L := (16 : ℝ)) (d := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
          z.1 ⟨hzU.2.1.le, hzU.2.2.le⟩
      refine ⟨mem_univ _, ?_⟩
      change (e z).2 / 64 ∈ Ioo (-1 / 2) (1 / 2)
      rw [heval]
      constructor <;> norm_num at hheight ⊢ <;> linarith [hheight.1, hheight.2]
  · intro z hz
    have hzunion : z ∈ E.source ∪ B.source := hcover.symm ▸ hz
    rcases hzunion with hzE | hzB
    · rw [hfE hzE]
      have hzE' : z ∈ A ×ˢ Ioo (-1) 1 := hES ▸ hzE
      obtain ⟨s, hs, hsval⟩ := hzE'.1
      have hzval : z = ((s : AddCircle p), z.2) := Prod.ext hsval.symm rfl
      change |(e z).1| ≤ 9
      rw [hzval, hmiddle s hs z.2 hzE'.2]
      exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · rw [hfB hzB]
      have hzB' : z ∈ Cᶜ ×ˢ Ioo (-1) 1 := hBS ▸ hzB
      let q : AddCircle p := ((16 / 2 : ℝ) : AddCircle p) + z.1
      have hq : PLAnnularStrip.annulusMap 16 (by norm_num) (q, z.2) ∈
          PLAnnularStrip.squareAnnulus 16 1 := by
        rw [← PLAnnularStrip.range_annulusMap (L := (16 : ℝ)) (d := (1 : ℝ))
          (by norm_num) (by norm_num) (by norm_num)]
        exact ⟨(q, ⟨z.2, ⟨hzB'.2.1.le, hzB'.2.2.le⟩⟩), rfl⟩
      change |(e z).1| ≤ 9
      rw [heval]
      change |(PLAnnularStrip.annulusMap 16 (by norm_num) (q, z.2)).1 - 16 / 2| ≤ 9
      have hb := hq.1.1
      apply abs_le.mpr
      constructor <;> norm_num at hb ⊢ <;> linarith [hb.1, hb.2]
  · intro s hs t ht
    have hs6 : s ∈ Ioo (-6) 6 := by
      have hs' := abs_le.mp hs
      constructor <;> linarith [hs'.1, hs'.2]
    have hzE : ((s : AddCircle p), t) ∈ E.source := by
      rw [hES]
      exact ⟨⟨s, hs6, rfl⟩, ht⟩
    rw [hfE hzE]
    change expand (squash (e ((s : AddCircle p), t))) = (s, t)
    rw [hmiddle s hs6 t ht]
    exact expand_squash_core hs t
  · intro a
    let Q := (AddCircle.openPartialHomeomorphCoe p a).prod (OpenPartialHomeomorph.refl ℝ)
    let V := Q.source ∩ Q ⁻¹' U
    have hV : IsOpen V :=
      Q.continuousOn_toFun.isOpen_inter_preimage Q.open_source (isOpen_univ.prod isOpen_Ioo)
    have hbPL : LocallyPiecewiseAffineOn (Q.trans b) (Q.trans b).source := by
      apply (mem_piecewiseAffineGroupoid_iff_forward (Q.trans b)).mp
      change Q.trans (e.trans squash.toOpenPartialHomeomorph) ∈ piecewiseAffineGroupoid (ℝ × ℝ)
      rw [← OpenPartialHomeomorph.trans_assoc]
      exact (piecewiseAffineGroupoid (ℝ × ℝ)).trans (hePL a) squash_mem_piecewiseAffineGroupoid
    have hmPL : LocallyPiecewiseAffineOn (Q.trans m) (Q.trans m).source := by
      apply (mem_piecewiseAffineGroupoid_iff_forward (Q.trans m)).mp
      change Q.trans (b.trans expand.toOpenPartialHomeomorph) ∈ piecewiseAffineGroupoid (ℝ × ℝ)
      rw [← OpenPartialHomeomorph.trans_assoc]
      exact (piecewiseAffineGroupoid (ℝ × ℝ)).trans
        ((mem_piecewiseAffineGroupoid_iff_forward (Q.trans b)).mpr hbPL)
        expand_mem_piecewiseAffineGroupoid
    apply LocallyPiecewiseAffineOn.locality
    intro x hx
    have hxunion : Q x ∈ E.source ∪ B.source := hcover.symm ▸ hx.2
    rcases hxunion with hxE | hxB
    · let W := (Q.trans E).source
      refine ⟨W, ⟨hx.1, hxE⟩, ?_⟩
      have hsub : V ∩ W ⊆ (Q.trans m).source :=
        fun _ hy => ⟨hy.2.1, hy.2.2.1⟩
      apply (hmPL.mono (hV.inter (Q.trans E).open_source) hsub).congr
      intro y hy
      exact (hfE hy.2.2).symm
    · let W := (Q.trans B).source
      refine ⟨W, ⟨hx.1, hxB⟩, ?_⟩
      have hsub : V ∩ W ⊆ (Q.trans b).source :=
        fun _ hy => ⟨hy.2.1, hy.2.2.1⟩
      apply (hbPL.mono (hV.inter (Q.trans B).open_source) hsub).congr
      intro y hy
      exact (hfB hy.2.2).symm

end StableAnnulus
