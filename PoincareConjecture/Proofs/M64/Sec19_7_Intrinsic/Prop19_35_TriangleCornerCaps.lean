import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCapData

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Matrix

namespace PoincareConjecture

abbrev M64IntrinsicTriangleCaps (base alpha beta : ℝ → AnnulusCoordinates)
    (D A B : ℝ) (U : Set AnnulusCoordinates) :=
  M64IntrinsicFiniteCornerCaps
    (![base, (fun s => base (D - s)), (fun s => alpha (A - s))] :
      Fin 3 → ℝ → AnnulusCoordinates)
    (![alpha, beta, (fun s => beta (B - s))] : Fin 3 → ℝ → AnnulusCoordinates)
    (![D, D, A] : Fin 3 → ℝ) (![A, B, B] : Fin 3 → ℝ) U

private theorem reverse_inj {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hi : InjOn gamma (Icc 0 T)) : InjOn (fun s => gamma (T - s)) (Icc 0 T) := by
  intro s hs t ht heq
  have h := hi ⟨by linarith [hs.2], by linarith [hs.1]⟩
    ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
  linarith

private theorem reverse_image (gamma : ℝ → AnnulusCoordinates) (T : ℝ) :
    (fun s => gamma (T - s)) '' Icc 0 T = gamma '' Icc 0 T := by
  change (gamma ∘ fun s => T - s) '' Icc 0 T = _
  rw [image_comp, image_const_sub_Icc]
  simp only [sub_self, sub_zero]

theorem m64Intrinsic_exists_triangle_corner_caps
    {base alpha beta : ℝ → AnnulusCoordinates}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {D A B : ℝ} (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hindA : LinearIndependent ℝ
      (![deriv base 0, deriv alpha 0] : Fin 2 → AnnulusCoordinates))
    (hindB : LinearIndependent ℝ
      (![-deriv base D, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hindT : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U) :
    Nonempty (M64IntrinsicTriangleCaps base alpha beta D A B U) := by
  let left : Fin 3 → ℝ → AnnulusCoordinates :=
    ![base, (fun s => base (D - s)), (fun s => alpha (A - s))]
  let right : Fin 3 → ℝ → AnnulusCoordinates :=
    ![alpha, beta, (fun s => beta (B - s))]
  let lenL : Fin 3 → ℝ := ![D, D, A]
  let lenR : Fin 3 → ℝ := ![A, B, B]
  let rest : Fin 3 → Set AnnulusCoordinates :=
    ![beta '' Icc 0 B, alpha '' Icc 0 A, base '' Icc 0 D]
  have hl (j : Fin 3) : ContDiff ℝ ∞ (left j) := by
    fin_cases j
    · exact hc
    · exact hc.comp (contDiff_const.sub contDiff_id)
    · exact ha.comp (contDiff_const.sub contDiff_id)
  have hr (j : Fin 3) : ContDiff ℝ ∞ (right j) := by
    fin_cases j
    · exact ha
    · exact hb
    · exact hb.comp (contDiff_const.sub contDiff_id)
  have hlenL (j : Fin 3) : 0 < lenL j := by
    fin_cases j
    · exact hD
    · exact hD
    · exact hA
  have hlenR (j : Fin 3) : 0 < lenR j := by
    fin_cases j
    · exact hA
    · exact hB
    · exact hB
  have hli (j : Fin 3) : InjOn (left j) (Icc 0 (lenL j)) := by
    fin_cases j
    · exact hci
    · exact reverse_inj hci
    · exact reverse_inj hai
  have hri (j : Fin 3) : InjOn (right j) (Icc 0 (lenR j)) := by
    fin_cases j
    · exact hai
    · exact hbi
    · exact reverse_inj hbi
  have hbase (j : Fin 3) : right j 0 = left j 0 := by
    fin_cases j
    · exact hstartA.symm
    · change beta 0 = base (D - 0)
      simpa only [sub_zero] using hstartB.symm
    · change beta (B - 0) = alpha (A - 0)
      simpa only [sub_zero] using hmeet.symm
  have hind (j : Fin 3) : LinearIndependent ℝ
      (![deriv (left j) 0, deriv (right j) 0] : Fin 2 → AnnulusCoordinates) := by
    fin_cases j
    · exact hindA
    · change LinearIndependent ℝ
        (![deriv (fun s => base (D - s)) 0, deriv beta 0] : Fin 2 → AnnulusCoordinates)
      simpa only [deriv_comp_const_sub, sub_zero] using hindB
    · change LinearIndependent ℝ
        (![deriv (fun s => alpha (A - s)) 0, deriv (fun s => beta (B - s)) 0] :
          Fin 2 → AnnulusCoordinates)
      simpa only [deriv_comp_const_sub, sub_zero] using hindT
  have hrest (j : Fin 3) : IsCompact (rest j) := by
    fin_cases j
    · exact isCompact_Icc.image hb.continuous
    · exact isCompact_Icc.image ha.continuous
    · exact isCompact_Icc.image hc.continuous
  have hnot (j : Fin 3) : left j 0 ∉ rest j := by
    fin_cases j
    · rintro ⟨t, ht, heq⟩
      exact hD.ne (hbaseB 0 ⟨le_rfl, hD.le⟩ t ht heq.symm).1
    · change base (D - 0) ∉ alpha '' Icc 0 A
      rw [sub_zero]
      rintro ⟨t, ht, heq⟩
      exact hD.ne' (hbaseA D ⟨hD.le, le_rfl⟩ t ht heq.symm).1
    · change alpha (A - 0) ∉ base '' Icc 0 D
      rw [sub_zero]
      rintro ⟨s, hs, heq⟩
      exact hA.ne' (hbaseA s hs A ⟨hA.le, le_rfl⟩ heq).2
  have hne01 : base 0 ≠ base D := by
    intro heq
    exact hD.ne (hci ⟨le_rfl, hD.le⟩ ⟨hD.le, le_rfl⟩ heq)
  have hne02 : base 0 ≠ alpha A := by
    intro heq
    exact hA.ne' (hbaseA 0 ⟨le_rfl, hD.le⟩ A ⟨hA.le, le_rfl⟩ heq).2
  have hne12 : base D ≠ alpha A := by
    intro heq
    exact hD.ne' (hbaseA D ⟨hD.le, le_rfl⟩ A ⟨hA.le, le_rfl⟩ heq).1
  have hdistinct : Function.Injective (fun j => left j 0) := by
    intro i j heq
    fin_cases i <;> fin_cases j
    · rfl
    · change base 0 = base (D - 0) at heq
      exact (hne01 (by simpa only [sub_zero] using heq)).elim
    · change base 0 = alpha (A - 0) at heq
      exact (hne02 (by simpa only [sub_zero] using heq)).elim
    · change base (D - 0) = base 0 at heq
      exact (hne01 (by simpa only [sub_zero] using heq.symm)).elim
    · rfl
    · change base (D - 0) = alpha (A - 0) at heq
      exact (hne12 (by simpa only [sub_zero] using heq)).elim
    · change alpha (A - 0) = base 0 at heq
      exact (hne02 (by simpa only [sub_zero] using heq.symm)).elim
    · change alpha (A - 0) = base (D - 0) at heq
      exact (hne12 (by simpa only [sub_zero] using heq.symm)).elim
    · rfl
  have hfront (j : Fin 3) : frontier U =
      left j '' Icc 0 (lenL j) ∪ right j '' Icc 0 (lenR j) ∪ rest j := by
    fin_cases j
    · exact hfU.trans (union_assoc _ _ _).symm
    · change frontier U = (fun s => base (D - s)) '' Icc 0 D ∪
        beta '' Icc 0 B ∪ alpha '' Icc 0 A
      rw [reverse_image, hfU]
      ac_rfl
    · change frontier U = (fun s => alpha (A - s)) '' Icc 0 A ∪
        (fun s => beta (B - s)) '' Icc 0 B ∪ base '' Icc 0 D
      rw [reverse_image, reverse_image, hfU]
      ac_rfl
  exact m64Intrinsic_exists_finite_corner_cap_data left right lenL lenR rest hl hr
    hlenL hlenR hli hri hbase hind hrest hnot hdistinct hU hV hdisj hfront hfV

end PoincareConjecture
