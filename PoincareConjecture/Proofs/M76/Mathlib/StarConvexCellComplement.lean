import PoincareConjecture.Proofs.M76.Mathlib.PuncturedBallSimplyConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas












set_option autoImplicit false

open Set Metric
open scoped unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem StarConvex.smul_notMem_of_one_le {C : Set E} (hC : StarConvex ℝ 0 C)
    {x : E} (hx : x ∉ C) {a : ℝ} (ha : 1 ≤ a) : a • x ∉ C := by
  intro hax
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hback := hC.smul_mem hax (inv_nonneg.mpr ha0.le) (inv_le_one_of_one_le₀ ha)
  apply hx
  simpa only [smul_smul, inv_mul_cancel₀ ha0.ne', one_smul] using hback






theorem exists_ball_sdiff_starConvex_homotopyEquiv
    {C : Set E} (hC : StarConvex ℝ 0 C) (h0 : (0 : E) ∈ C)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hbound : C ⊆ ball (0 : E) ρ) :
    ∃ e : ContinuousMap.HomotopyEquiv (ball (0 : E) R \ C : Set E)
      (ball (0 : E) R \ {0} : Set E),
      (∀ x, (e x : E) = (x : E)) ∧
      ∀ x, (e.symm x : E) = max 1 (ρ / ‖(x : E)‖) • (x : E) := by
  let U : Set E := ball (0 : E) R \ C
  let V : Set E := ball (0 : E) R \ {0}
  have hxne (x : V) : (x : E) ≠ 0 := x.property.2
  have hxnorm (x : V) : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (hxne x)
  let s : V → ℝ := fun x => max 1 (ρ / ‖(x : E)‖)
  let r : V → E := fun x => s x • (x : E)
  have hsone (x : V) : 1 ≤ s x := le_max_left _ _
  have hs : Continuous s :=
    continuous_const.max (continuous_const.div continuous_subtype_val.norm hxnorm)
  have hr : Continuous r := hs.smul continuous_subtype_val
  have hrnorm (x : V) : ‖r x‖ = max ‖(x : E)‖ ρ := by
    change ‖s x • (x : E)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (hsone x))]
    change max 1 (ρ / ‖(x : E)‖) * ‖(x : E)‖ = _
    rw [max_mul_of_nonneg _ _ (norm_nonneg _), one_mul,
      div_mul_cancel₀ _ (hxnorm x)]
  have hrball (x : V) : r x ∈ ball (0 : E) R := by
    rw [mem_ball_zero_iff, hrnorm]
    exact max_lt_iff.mpr ⟨mem_ball_zero_iff.mp x.property.1, hρR⟩
  have hrC (x : V) : r x ∉ C := by
    intro hxC
    have hlt : ‖r x‖ < ρ := mem_ball_zero_iff.mp (hbound hxC)
    rw [hrnorm] at hlt
    exact (not_lt_of_ge (le_max_right _ _)) hlt
  let f : C(U, V) :=
    ⟨fun x => ⟨x, x.property.1, fun hx0 => x.property.2 (hx0.symm ▸ h0)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let g : C(V, U) := ⟨fun x => ⟨r x, hrball x, hrC x⟩, hr.subtype_mk _⟩
  let T : I × V → E := fun tx => ((1 - (tx.1 : ℝ)) * s tx.2 + (tx.1 : ℝ)) •
    (tx.2 : E)
  have htime : Continuous (fun tx : I × V => (tx.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hT : Continuous T :=
    (((continuous_const.sub htime).mul (hs.comp continuous_snd)).add htime).smul
      (continuous_subtype_val.comp continuous_snd)
  have hscalar (t : I) (x : V) :
      1 ≤ (1 - (t : ℝ)) * s x + (t : ℝ) ∧
      (1 - (t : ℝ)) * s x + (t : ℝ) ≤ s x := by
    have hs0 : 0 ≤ s x - 1 := sub_nonneg.mpr (hsone x)
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) hs0]
    · nlinarith [mul_nonneg t.property.1 hs0]
  have hTball (t : I) (x : V) : T (t, x) ∈ ball (0 : E) R := by
    have hle : ‖T (t, x)‖ ≤ ‖r x‖ := by
      change ‖((1 - (t : ℝ)) * s x + (t : ℝ)) • (x : E)‖ ≤ ‖s x • (x : E)‖
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (zero_le_one.trans (hscalar t x).1),
        abs_of_nonneg (zero_le_one.trans (hsone x))]
      exact mul_le_mul_of_nonneg_right (hscalar t x).2 (norm_nonneg _)
    exact mem_ball_zero_iff.mpr (hle.trans_lt (mem_ball_zero_iff.mp (hrball x)))
  have hTC (t : I) (x : V) (hxC : (x : E) ∉ C) : T (t, x) ∉ C :=
    hC.smul_notMem_of_one_le hxC (hscalar t x).1
  have hTzero (t : I) (x : V) : T (t, x) ≠ 0 :=
    smul_ne_zero (ne_of_gt (zero_lt_one.trans_le (hscalar t x).1)) (hxne x)
  have hT0 (x : V) : T (0, x) = r x := by simp [T, r]
  have hT1 (x : V) : T (1, x) = (x : E) := by simp [T]
  let HU : ContinuousMap.Homotopy (g.comp f) (ContinuousMap.id U) :=
    { toFun := fun tx => ⟨T (tx.1, f tx.2), hTball tx.1 (f tx.2),
        hTC tx.1 (f tx.2) tx.2.property.2⟩
      continuous_toFun :=
        (hT.comp (continuous_fst.prodMk (f.continuous.comp continuous_snd))).subtype_mk _
      map_zero_left := fun x => Subtype.ext (hT0 (f x))
      map_one_left := fun x => Subtype.ext (hT1 (f x)) }
  let HV : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id V) :=
    { toFun := fun tx => ⟨T tx, hTball tx.1 tx.2, hTzero tx.1 tx.2⟩
      continuous_toFun := hT.subtype_mk _
      map_zero_left := fun x => Subtype.ext (hT0 x)
      map_one_left := fun x => Subtype.ext (hT1 x) }
  exact ⟨⟨f, g, ⟨HU⟩, ⟨HV⟩⟩, fun _ => rfl, fun _ => rfl⟩





theorem isSimplyConnected_ball_sdiff_starConvex_of_two_lt_finrank
    [FiniteDimensional ℝ E] (hdim : 2 < Module.finrank ℝ E)
    {C : Set E} (hC : StarConvex ℝ 0 C) (h0 : (0 : E) ∈ C)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hbound : C ⊆ ball (0 : E) ρ) :
    IsSimplyConnected (ball (0 : E) R \ C) := by
  obtain ⟨e, _, _⟩ := exists_ball_sdiff_starConvex_homotopyEquiv hC h0 hρ hρR hbound
  let : SimplyConnectedSpace (ball (0 : E) R \ {0} : Set E) :=
    isSimplyConnected_ball_sdiff_center_of_two_lt_finrank hdim 0 (hρ.trans hρR)
  exact e.simplyConnectedSpace





theorem isSimplyConnected_ball_sdiff_compact_convex_of_two_lt_finrank
    [FiniteDimensional ℝ E] (hdim : 2 < Module.finrank ℝ E)
    {C : Set E} (hC : IsCompact C) (hconv : Convex ℝ C) (h0 : (0 : E) ∈ C)
    {R : ℝ} (hbound : C ⊆ ball (0 : E) R) :
    IsSimplyConnected (ball (0 : E) R \ C) := by
  have hR : 0 < R := by simpa only [mem_ball, dist_self] using hbound h0
  obtain ⟨ρ, hρ, hρC⟩ := exists_pos_lt_subset_ball hR hC.isClosed hbound
  exact isSimplyConnected_ball_sdiff_starConvex_of_two_lt_finrank hdim
    (hconv.starConvex h0) h0 hρ.1 hρ.2 hρC
