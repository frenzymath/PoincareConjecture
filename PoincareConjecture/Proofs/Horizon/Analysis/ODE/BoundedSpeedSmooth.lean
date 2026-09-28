import PoincareConjecture.Proofs.Horizon.Analysis.ODE.BoundedSpeed
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Continuation

noncomputable section

namespace Poincare.ODE

open Set Metric
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_open_solution_extension
    {U : Set E} (hU : IsOpen U) {F : E → E} (hF : ContDiffOn ℝ ∞ F U)
    {α : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hα : ∀ t ∈ Icc 0 T, α t ∈ U ∧ HasDerivWithinAt α (F (α t)) (Icc 0 T) t) :
    ∃ δ > 0, ∃ γ : ℝ → E, γ 0 = α 0 ∧ EqOn γ α (Icc 0 T) ∧
      ∀ t ∈ Ioo (-δ) (T + δ), γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t := by
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTmem : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  obtain ⟨Vl, δl, Φl, _, hxl, _, hδl, _, hinitl, hmapsl, hderivl⟩ :=
    LocalFlow.exists_smooth_localFlow hU hF (hα 0 h0mem).1
  obtain ⟨Vr, δr, Φr, _, hxr, _, hδr, _, hinitr, hmapsr, hderivr⟩ :=
    LocalFlow.exists_smooth_localFlow hU hF (hα T hTmem).1
  let ε : ℝ := min δl δr / 2
  have hε : 0 < ε := half_pos (lt_min hδl hδr)
  have hεltl : ε < δl := (half_lt_self (lt_min hδl hδr)).trans_le (min_le_left _ _)
  have hεltr : ε < δr := (half_lt_self (lt_min hδl hδr)).trans_le (min_le_right _ _)
  let βl : ℝ → E := fun t => Φl (α 0, t)
  let βr : ℝ → E := fun t => Φr (α T, t - T)
  have hβl0 : βl 0 = α 0 := hinitl (α 0) hxl
  have hβrT : βr T = α T := by simpa only [βr, sub_self] using hinitr (α T) hxr
  have hβl : ∀ t ∈ Icc (-ε) 0, βl t ∈ U ∧ HasDerivAt βl (F (βl t)) t := by
    intro t ht
    have hr : t ∈ Ioo (-δl) δl := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨hmapsl _ hxl _ hr, hderivl _ hxl _ hr⟩
  have hβr : ∀ t ∈ Icc T (T + ε), βr t ∈ U ∧ HasDerivAt βr (F (βr t)) t := by
    intro t ht
    have hr : t - T ∈ Ioo (-δr) δr := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨hmapsr _ hxr _ hr, ?_⟩
    simpa only [βr, one_smul, Function.comp_def, id_eq] using
      (hderivr _ hxr _ hr).scomp t ((hasDerivAt_id t).sub_const T)
  let η : ℝ → E := fun t => if t ≤ 0 then βl t else α t
  have hη : ∀ t ∈ Icc (-ε) T, η t ∈ U ∧
      HasDerivWithinAt η (F (η t)) (Icc (-ε) T) t := by
    have hd := hasDerivWithinAt_glue (by linarith : -ε ≤ 0) hT
      (fun t ht => (hβl t ht).2.hasDerivWithinAt)
      (fun t ht => (hα t ht).2) hβl0.symm
    intro t ht
    refine ⟨?_, hd t ht⟩
    by_cases ht0 : t ≤ 0
    · simpa only [η, if_pos ht0] using (hβl t ⟨ht.1, ht0⟩).1
    · simpa only [η, if_neg ht0] using (hα t ⟨le_of_not_ge ht0, ht.2⟩).1
  have hηT : η T = α T := by
    by_cases ht0 : T ≤ 0
    · have hzero : T = 0 := le_antisymm ht0 hT
      subst T
      simpa only [η, if_pos le_rfl] using hβl0
    · exact if_neg ht0
  let γ : ℝ → E := fun t => if t ≤ T then η t else βr t
  have hγ : ∀ t ∈ Icc (-ε) (T + ε), γ t ∈ U ∧
      HasDerivWithinAt γ (F (γ t)) (Icc (-ε) (T + ε)) t := by
    have hd := hasDerivWithinAt_glue (by linarith : -ε ≤ T)
      (by linarith : T ≤ T + ε) (fun t ht => (hη t ht).2)
      (fun t ht => (hβr t ht).2.hasDerivWithinAt) (hβrT.trans hηT.symm)
    intro t ht
    refine ⟨?_, hd t ht⟩
    by_cases htT : t ≤ T
    · simpa only [γ, if_pos htT] using (hη t ⟨ht.1, htT⟩).1
    · simpa only [γ, if_neg htT] using (hβr t ⟨le_of_not_ge htT, ht.2⟩).1
  refine ⟨ε, hε, γ, ?_, ?_, ?_⟩
  · simp only [γ, η, if_pos hT, if_pos le_rfl, hβl0]
  · intro t ht
    change (if t ≤ T then η t else βr t) = α t
    rw [if_pos ht.2]
    by_cases ht0 : t ≤ 0
    · have htzero : t = 0 := le_antisymm ht0 ht.1
      subst t
      simpa only [η, if_pos le_rfl] using hβl0
    · exact if_neg ht0
  · intro t ht
    exact ⟨(hγ t (Ioo_subset_Icc_self ht)).1,
      (hγ t (Ioo_subset_Icc_self ht)).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

theorem exists_smooth_flow_of_bounded_speed
    {U : Set E} (hU : IsOpen U) {F : E → E} (hF : ContDiffOn ℝ ∞ F U)
    {p x : E} {R C T : ℝ} (hball : closedBall p R ⊆ U)
    (hC : 0 ≤ C) (hbound : ∀ y ∈ U, ‖F y‖ ≤ C) (hT : 0 ≤ T)
    (hmargin : dist x p + C * T ≤ R) :
    ∃ (V : Set E) (δ : ℝ) (Φ : E × ℝ → E), IsOpen V ∧ x ∈ V ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-δ) (T + δ)) ∧
      (∀ y ∈ V, Φ (y, 0) = y) ∧
      (∀ y ∈ V, ∀ t ∈ Ioo (-δ) (T + δ), Φ (y, t) ∈ U ∧
        HasDerivAt (fun s => Φ (y, s)) (F (Φ (y, t))) t) ∧
      ∀ t ∈ Icc 0 T, dist (Φ (x, t)) p ≤ dist x p + C * t := by
  obtain ⟨α, hα0, hα⟩ :=
    exists_solution_of_bounded_speed hU hF hball hC hbound hT hmargin
  obtain ⟨ε, hε, γ, hγ0, _, hγopen⟩ :=
    exists_open_solution_extension hU hF hT (fun t ht => ⟨(hα t ht).1, (hα t ht).2.2⟩)
  have hγx : γ 0 = x := hγ0.trans hα0
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hsub : Icc 0 T ⊆ Ioo (-ε) (T + ε) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨V, δ, Φ, hV, hxV, hδ, hs, hi, hf⟩ :=
    LocalFlow.exists_smooth_flow_along_compact_interval hU hF isOpen_Ioo
      (convex_Ioo _ _) hγopen hT hsub
  rw [hγx] at hxV
  refine ⟨V, δ, Φ, hV, hxV, hδ, hs, hi, hf, ?_⟩
  have htime : Icc 0 T ⊆ Ioo (-δ) (T + δ) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlip := (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (C := ⟨C, hC⟩) (fun t ht => (hf x hxV t (htime ht)).2.hasDerivWithinAt)
    (fun t ht => show ‖F (Φ (x, t))‖₊ ≤ ⟨C, hC⟩ from
      hbound _ (hf x hxV t (htime ht)).1)
  intro t ht
  have hb : dist (Φ (x, t)) (Φ (x, 0)) ≤ C * dist t 0 := hlip.dist_le_mul t ht 0 h0mem
  rw [hi x hxV, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] at hb
  have hh := dist_triangle (Φ (x, t)) x p
  linarith

end Poincare.ODE
