import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentEmbedding








set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

private theorem square_rim_iff (z : V2) :
    z ∈ Q ↔ -1 ≤ z 0 ∧ z 0 ≤ 1 ∧ -1 ≤ z 1 ∧ z 1 ≤ 1 ∧
      (z 0 = -1 ∨ z 0 = 1 ∨ z 1 = -1 ∨ z 1 = 1) := by
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro hz
    have h0 : |z 0| ≤ 1 := by simpa only [Real.norm_eq_abs,hz] using norm_le_pi_norm z 0
    have h1 : |z 1| ≤ 1 := by simpa only [Real.norm_eq_abs,hz] using norm_le_pi_norm z 1
    rcases abs_le.mp h0 with ⟨h0l,h0u⟩
    rcases abs_le.mp h1 with ⟨h1l,h1u⟩
    refine ⟨h0l,h0u,h1l,h1u,?_⟩
    by_contra hn
    push Not at hn
    have hh : ‖z‖ < 1 := (pi_norm_lt_iff (by norm_num : (0:ℝ) < 1)).mpr (by
      intro i
      fin_cases i
      · exact Real.norm_eq_abs (z 0) ▸ abs_lt.mpr
          ⟨lt_of_le_of_ne h0l hn.1.symm,lt_of_le_of_ne h0u hn.2.1⟩
      · exact Real.norm_eq_abs (z 1) ▸ abs_lt.mpr
          ⟨lt_of_le_of_ne h1l hn.2.2.1.symm,lt_of_le_of_ne h1u hn.2.2.2⟩)
    exact (ne_of_lt hh) hz
  · rintro ⟨h0l,h0u,h1l,h1u,hface⟩
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      fin_cases i
      · exact Real.norm_eq_abs (z 0) ▸ abs_le.mpr ⟨h0l,h0u⟩
      · exact Real.norm_eq_abs (z 1) ▸ abs_le.mpr ⟨h1l,h1u⟩
    · rcases hface with h | h | h | h
      · simpa only [h,norm_neg,norm_one] using norm_le_pi_norm z 0
      · simpa only [h,norm_one] using norm_le_pi_norm z 0
      · simpa only [h,norm_neg,norm_one] using norm_le_pi_norm z 1
      · simpa only [h,norm_one] using norm_le_pi_norm z 1

theorem isPreconnected_square_rim_complement_segment
    {a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1) :
    IsPreconnected (Q \ {z : V2 | z 0 = -1 ∧ a < z 1 ∧ z 1 < b}) := by
  let left : ℝ → V2 := fun t => ![-1,t]
  let bottom : ℝ → V2 := fun t => ![t,-1]
  let right : ℝ → V2 := fun t => ![1,t]
  let top : ℝ → V2 := fun t => ![t,1]
  have hl : Continuous left := by fun_prop
  have hbott : Continuous bottom := by fun_prop
  have hr : Continuous right := by fun_prop
  have ht : Continuous top := by fun_prop
  let E0 := left '' Icc (-1) a
  let E1 := bottom '' Icc (-1) 1
  let E2 := right '' Icc (-1) 1
  let E3 := top '' Icc (-1) 1
  let E4 := left '' Icc b 1
  have hc0 : IsPreconnected E0 := isPreconnected_Icc.image _ hl.continuousOn
  have hc1 : IsPreconnected E1 := isPreconnected_Icc.image _ hbott.continuousOn
  have hc2 : IsPreconnected E2 := isPreconnected_Icc.image _ hr.continuousOn
  have hc3 : IsPreconnected E3 := isPreconnected_Icc.image _ ht.continuousOn
  have hc4 : IsPreconnected E4 := isPreconnected_Icc.image _ hl.continuousOn
  have h01 : IsPreconnected (E0 ∪ E1) := hc0.union ![-1,-1]
    ⟨-1,⟨le_rfl,ha.le⟩,rfl⟩ ⟨-1,⟨le_rfl,by norm_num⟩,rfl⟩ hc1
  have h012 : IsPreconnected (E0 ∪ E1 ∪ E2) := h01.union ![1,-1]
    (Or.inr ⟨1,⟨by norm_num,le_rfl⟩,rfl⟩) ⟨-1,⟨le_rfl,by norm_num⟩,rfl⟩ hc2
  have h0123 : IsPreconnected (E0 ∪ E1 ∪ E2 ∪ E3) := h012.union ![1,1]
    (Or.inr ⟨1,⟨by norm_num,le_rfl⟩,rfl⟩) ⟨1,⟨by norm_num,le_rfl⟩,rfl⟩ hc3
  have hconn : IsPreconnected (E0 ∪ E1 ∪ E2 ∪ E3 ∪ E4) := h0123.union ![-1,1]
    (Or.inr ⟨-1,⟨le_rfl,by norm_num⟩,rfl⟩) ⟨1,⟨hb.le,le_rfl⟩,rfl⟩ hc4
  have hEq : Q \ {z : V2 | z 0 = -1 ∧ a < z 1 ∧ z 1 < b} =
      E0 ∪ E1 ∪ E2 ∪ E3 ∪ E4 := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨h0l,h0u,h1l,h1u,hface⟩ := (square_rim_iff z).mp hz.1
      have hvec : ![z 0,z 1] = z := by ext i; fin_cases i <;> rfl
      rcases hface with h | h | h | h
      · by_cases hh : z 1 ≤ a
        · exact Or.inl (Or.inl (Or.inl (Or.inl
            ⟨z 1,⟨h1l,hh⟩,by dsimp only [left]; rw [←h]; exact hvec⟩)))
        · have hh' : b ≤ z 1 := le_of_not_gt (fun hn => hz.2 ⟨h,lt_of_not_ge hh,hn⟩)
          exact Or.inr ⟨z 1,⟨hh',h1u⟩,by dsimp only [left]; rw [←h]; exact hvec⟩
      · exact Or.inl (Or.inl (Or.inr
          ⟨z 1,⟨h1l,h1u⟩,by dsimp only [right]; rw [←h]; exact hvec⟩))
      · exact Or.inl (Or.inl (Or.inl (Or.inr
          ⟨z 0,⟨h0l,h0u⟩,by dsimp only [bottom]; rw [←h]; exact hvec⟩)))
      · exact Or.inl (Or.inr
          ⟨z 0,⟨h0l,h0u⟩,by dsimp only [top]; rw [←h]; exact hvec⟩)
    · rintro z ((((hz|hz)|hz)|hz)|hz)
      all_goals obtain ⟨t,ht,rfl⟩ := hz
      all_goals
        constructor
        · apply (square_rim_iff _).mpr
          dsimp only [left,bottom,right,top,Matrix.cons_val_zero,Matrix.cons_val_one,
            Matrix.head_cons]
          constructor <;> try norm_num
          all_goals first | exact ht.1 | exact ht.2 | omega |
            (constructor <;> linarith [ht.1,ht.2])
        · dsimp only [left,bottom,right,top,mem_ofPred_eq,Matrix.cons_val_zero,
            Matrix.cons_val_one,Matrix.head_cons]
          intro hh
          rcases hh with ⟨h,hlo,hhi⟩
          all_goals linarith [ht.1,ht.2]
  rw [hEq]
  exact hconn

theorem endpoints_mem_square_rim_complement_segment
    {a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1) :
    ![-1,a] ∈ Q \ {z : V2 | z 0 = -1 ∧ a < z 1 ∧ z 1 < b} ∧
    ![-1,b] ∈ Q \ {z : V2 | z 0 = -1 ∧ a < z 1 ∧ z 1 < b} := by
  constructor
  · refine ⟨(square_rim_iff _).mpr ?_,?_⟩
    · simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
      exact ⟨le_rfl,by norm_num,ha.le,(hab.trans hb).le,Or.inl trivial⟩
    · simp
  · refine ⟨(square_rim_iff _).mpr ?_,?_⟩
    · simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
      exact ⟨le_rfl,by norm_num,(ha.trans hab).le,hb.le,Or.inl trivial⟩
    · simp

end PoincareConjecture.M76
