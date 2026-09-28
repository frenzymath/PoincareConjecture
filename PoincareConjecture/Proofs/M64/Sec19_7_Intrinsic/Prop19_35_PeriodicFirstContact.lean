import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PeriodicNormalMap













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_exists_periodic_first_contact
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u) {P T : ℝ} (hP : 0 < P)
    (hperiod : ∀ t, Function.Periodic (fun a => u (a, t)) P)
    (hregular : ∀ z ∈ Ico (0 : ℝ) P ×ˢ Icc (0 : ℝ) T,
      Function.Injective (fderiv ℝ u z))
    (hfail : ¬InjOn u (Ico (0 : ℝ) P ×ˢ Icc (0 : ℝ) T)) :
    ∃ p q : ℝ × ℝ,
      p ∈ Ico (0 : ℝ) P ×ˢ Icc (0 : ℝ) T ∧
      q ∈ Ico (0 : ℝ) P ×ˢ Icc (0 : ℝ) T ∧ p ≠ q ∧ u p = u q ∧
      ∀ x y : ℝ × ℝ, x.2 ∈ Ico (0 : ℝ) (max p.2 q.2) →
        y.2 ∈ Ico (0 : ℝ) (max p.2 q.2) → u x = u y →
          (x.1 : AddCircle P) = (y.1 : AddCircle P) ∧ x.2 = y.2 := by
  let : Fact (0 < P) := ⟨hP⟩
  obtain ⟨U, hU, hcast, hlocal⟩ := m64Intrinsic_periodic_normal_map_on_cylinder hu hperiod
  let X := AddCircle P × Icc (0 : ℝ) T
  let i : X → AddCircle P × ℝ := fun z => (z.1, z.2.val)
  let f : X → AnnulusCoordinates := U ∘ i
  have hic : Continuous i := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hii : Function.Injective i := by
    intro x y hxy
    exact Prod.ext (congrArg (fun z : AddCircle P × ℝ => z.1) hxy)
      (Subtype.ext (congrArg (fun z : AddCircle P × ℝ => z.2) hxy))
  have hfc : Continuous f := hU.comp hic
  have hflocal (z : X) : ∃ W ∈ 𝓝 z, InjOn f W := by
    let a := (AddCircle.equivIco P 0 z.1).val
    have ha : a ∈ Ico (0 : ℝ) P := by
      simpa only [zero_add] using (AddCircle.equivIco P 0 z.1).property
    have heqa : (a : AddCircle P) = z.1 := AddCircle.coe_equivIco
    obtain ⟨W, hW, hiW⟩ := hlocal a z.2.val (hregular (a, z.2.val) ⟨ha, z.2.property⟩)
    have hW' : W ∈ 𝓝 (i z) := by simpa only [heqa, i] using hW
    refine ⟨i ⁻¹' W, hic.continuousAt.preimage_mem_nhds hW', ?_⟩
    intro x hx y hy hxy
    exact hii (hiW hx hy hxy)
  have hffail : ¬Function.Injective f := by
    intro hfi
    apply hfail
    rintro ⟨a, s⟩ ⟨ha, hs⟩ ⟨b, t⟩ ⟨hb, ht⟩ hab
    let x : X := ((a : AddCircle P), ⟨s, hs⟩)
    let y : X := ((b : AddCircle P), ⟨t, ht⟩)
    have hxy : x = y := hfi (by simpa only [f, Function.comp_apply, i, x, y, hcast] using hab)
    have hbase : a = b := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa only [zero_add] using ha) (by simpa only [zero_add] using hb)).mp
        (congrArg Prod.fst hxy)
    exact Prod.ext hbase (congrArg (fun z : X => z.2.val) hxy)
  obtain ⟨p, q, hpq, hmeet, hbelow⟩ := m64Intrinsic_exists_compact_first_contact f hfc hflocal
    (fun z : X => z.2.val) (continuous_subtype_val.comp continuous_snd) hffail
  let a := (AddCircle.equivIco P 0 p.1).val
  let b := (AddCircle.equivIco P 0 q.1).val
  have ha : a ∈ Ico (0 : ℝ) P := by
    simpa only [zero_add] using (AddCircle.equivIco P 0 p.1).property
  have hb : b ∈ Ico (0 : ℝ) P := by
    simpa only [zero_add] using (AddCircle.equivIco P 0 q.1).property
  have heqa : (a : AddCircle P) = p.1 := AddCircle.coe_equivIco
  have heqb : (b : AddCircle P) = q.1 := AddCircle.coe_equivIco
  have hpimage : f p = u (a, p.2.val) := by
    change U (p.1, p.2.val) = _
    rw [← heqa, hcast]
  have hqimage : f q = u (b, q.2.val) := by
    change U (q.1, q.2.val) = _
    rw [← heqb, hcast]
  have hpq' : (a, p.2.val) ≠ (b, q.2.val) := by
    intro heq
    apply hpq
    apply hii
    exact Prod.ext (heqa.symm.trans ((congrArg (fun x : ℝ => (x : AddCircle P))
      (congrArg (fun z : ℝ × ℝ => z.1) heq)).trans heqb))
        (congrArg (fun z : ℝ × ℝ => z.2) heq)
  refine ⟨(a, p.2.val), (b, q.2.val), ⟨ha, p.2.property⟩,
    ⟨hb, q.2.property⟩, hpq', hpimage.symm.trans (hmeet.trans hqimage), ?_⟩
  intro x y hx hy hxy
  have hmax : max p.2.val q.2.val ≤ T := max_le p.2.property.2 q.2.property.2
  let x' : X := ((x.1 : AddCircle P), ⟨x.2, hx.1, hx.2.le.trans hmax⟩)
  let y' : X := ((y.1 : AddCircle P), ⟨y.2, hy.1, hy.2.le.trans hmax⟩)
  have hxy' : x' = y' := hbelow hx.2 hy.2 (by
    simpa only [f, Function.comp_apply, i, x', y', hcast] using hxy)
  exact ⟨congrArg Prod.fst hxy', congrArg (fun z : X => z.2.val) hxy'⟩

end PoincareConjecture
