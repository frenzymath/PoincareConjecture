import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Plane.Nontrapping
import Mathlib.Topology.Order.IntermediateValue












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.ODE.Plane

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "v₀" => (!₂[(1 : ℝ), 0] : E₂)



theorem eq_horizontal_forward_ray
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E₂}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) {R a : ℝ}
    (hfix : ∀ x : E₂, R ≤ x 0 → V x = v₀) (ha : R ≤ γ a 0) :
    ∀ t ≥ 0, γ (a + t) = γ a + t • v₀ := by
  intro t ht
  have hα (s : ℝ) (_hs : s ∈ Icc 0 t) :
      HasDerivAt (fun u => γ (a + u)) (V (γ (a + s))) s := by
    simpa only [Function.comp_def, one_smul, id_eq] using
      (hγ (a + s)).scomp s ((hasDerivAt_id s).const_add a)
  have hβ (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun u => γ a + u • v₀) (V (γ a + s • v₀)) s := by
    rw [hfix _ (by simpa using (show R ≤ γ a 0 + s by linarith [hs.1]))]
    simpa using ((hasDerivAt_id s).smul_const v₀).const_add (γ a)
  have heq := Poincare.ODE.eqOn_Icc_of_hasDerivAt (hV.of_le (by simp)) hα hβ (by simp)
  exact heq ⟨ht, le_rfl⟩



theorem eq_horizontal_backward_ray
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E₂}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) {L a : ℝ}
    (hfix : ∀ x : E₂, x 0 ≤ L → V x = v₀) (ha : γ a 0 ≤ L) :
    ∀ t ≥ 0, γ (a - t) = γ a - t • v₀ := by
  intro t ht
  have hα (s : ℝ) (_hs : s ∈ Icc 0 t) :
      HasDerivAt (fun u => γ (a - u)) (-V (γ (a - s))) s := by
    simpa only [Function.comp_def, neg_smul, one_smul, id_eq] using
      (hγ (a - s)).scomp s ((hasDerivAt_id s).const_sub a)
  have hβ (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun u => γ a - u • v₀) (-V (γ a - s • v₀)) s := by
    rw [hfix _ (by simpa using (show γ a 0 - s ≤ L by linarith [hs.1]))]
    simpa using ((hasDerivAt_id s).smul_const v₀).const_sub (γ a)
  have heq := Poincare.ODE.eqOn_Icc_of_hasDerivAt (hV.neg.of_le (by simp)) hα hβ (by simp)
  exact heq ⟨ht, le_rfl⟩

private theorem eq_horizontal_line_of_height
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E₂}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) {B T a : ℝ}
    (hfix : ∀ x : E₂, x 1 ≤ B ∨ T ≤ x 1 → V x = v₀)
    (ha : γ a 1 ≤ B ∨ T ≤ γ a 1) :
    ∀ t, γ t = γ a + (t - a) • v₀ := by
  have hβ (s : ℝ) : HasDerivAt (fun u => γ a + (u - a) • v₀)
      (V (γ a + (s - a) • v₀)) s := by
    rw [hfix _ (by simpa using ha)]
    simpa using (((hasDerivAt_id s).sub_const a).smul_const v₀).const_add (γ a)
  have heq := Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hV.contDiffOn
    isOpen_univ isPreconnected_univ
    (fun t _ => ⟨mem_univ _, hγ t⟩) (fun t _ => ⟨mem_univ _, hβ t⟩)
    (mem_univ a) (by simp)
  exact fun t => heq (mem_univ t)




theorem exists_horizontal_right_exit
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {L R B T : ℝ} (hLR : L < R)
    (hfix : ∀ x : E₂,
      x 0 ≤ L ∨ R ≤ x 0 ∨ x 1 ≤ B ∨ T ≤ x 1 → V x = v₀)
    {γ : ℝ → E₂} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t)
    (hstart : γ 0 0 = L) (hheight : γ 0 1 ∈ Icc B T) :
    ∃ τ > 0, γ τ 0 = R ∧
      (∀ t ≥ 0, γ t 1 ∈ Icc B T) ∧
      (∀ t ∈ Ioo 0 τ, γ t 0 ∈ Ioo L R) ∧
      (∀ t ≥ 0, γ (τ + t) = γ τ + t • v₀) ∧
      HasDerivAt (fun t => γ t 0) 1 τ ∧
      ∀ t ≥ 0, γ t 0 = R → t = τ := by
  have hright : ∀ x : E₂, R ≤ x 0 → V x = v₀ :=
    fun x hx => hfix x (Or.inr (Or.inl hx))
  have hleft : ∀ x : E₂, x 0 ≤ L → V x = v₀ :=
    fun x hx => hfix x (Or.inl hx)
  have hhorizontal : ∀ x : E₂, x 1 ≤ B ∨ T ≤ x 1 → V x = v₀ :=
    fun x hx => hfix x (Or.inr (Or.inr hx))
  have hvertical (t : ℝ) : γ t 1 ∈ Icc B T := by
    constructor
    · by_contra! hlow
      have heq := eq_horizontal_line_of_height hV hγ hhorizontal (Or.inl hlow.le) 0
      have hy := congrArg (fun x : E₂ => x 1) heq
      simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, smul_zero, add_zero] at hy
      linarith [hheight.1]
    · by_contra! hhigh
      have heq := eq_horizontal_line_of_height hV hγ hhorizontal (Or.inr hhigh.le) 0
      have hy := congrArg (fun x : E₂ => x 1) heq
      simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, smul_zero, add_zero] at hy
      linarith [hheight.2]
  have hafter_left (t : ℝ) (ht : 0 < t) : L < γ t 0 := by
    by_contra! htl
    have heq := eq_horizontal_backward_ray hV hγ hleft htl t ht.le
    have hx := congrArg (fun x : E₂ => x 0) heq
    simp only [sub_self, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, mul_one, hstart] at hx
    linarith
  have hclosed_left (t : ℝ) (ht : 0 ≤ t) : L ≤ γ t 0 := by
    rcases ht.eq_or_lt with ht | ht
    · subst t
      exact hstart.ge
    · exact (hafter_left t ht).le
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  have hfar : ∃ t ≥ 0, R < γ t 0 := by
    by_contra! hbounded
    let box : Set E₂ :=
      (fun p : ℝ × ℝ => (!₂[p.1, p.2] : E₂)) '' (Icc L R ×ˢ Icc B T)
    have hmap : Continuous (fun p : ℝ × ℝ => (!₂[p.1, p.2] : E₂)) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    have hcompact : IsCompact box := (isCompact_Icc.prod isCompact_Icc).image hmap
    apply not_isBounded_forward_orbit hV hne (fun t _ => hγ t)
    apply hcompact.isBounded.subset
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(γ t 0, γ t 1), ⟨⟨hclosed_left t ht, hbounded t ht⟩, hvertical t⟩, ?_⟩
    ext i
    fin_cases i <;> simp
  obtain ⟨t₁, ht₁, hfar⟩ := hfar
  have hxcont : Continuous (fun t => γ t 0) := (EuclideanSpace.proj 0).continuous.comp hγc
  obtain ⟨τ, hτrange, hτR⟩ := intermediate_value_Icc ht₁ hxcont.continuousOn
    (show R ∈ Icc (γ 0 0) (γ t₁ 0) from ⟨by simpa [hstart] using hLR.le, hfar.le⟩)
  have hτ : 0 < τ := by
    refine lt_of_le_of_ne hτrange.1 ?_
    intro heq
    subst τ
    linarith [hτR]
  have htail := eq_horizontal_forward_ray hV hγ hright hτR.ge
  have hbefore (t : ℝ) (ht : t ∈ Ioo 0 τ) : γ t 0 ∈ Ioo L R := by
    refine ⟨hafter_left t ht.1, ?_⟩
    by_contra! htr
    have heq := eq_horizontal_forward_ray hV hγ hright htr (τ - t) (by linarith [ht.2])
    have hx := congrArg (fun x : E₂ => x 0) heq
    simp only [add_sub_cancel, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, mul_one, hτR] at hx
    linarith [ht.2]
  refine ⟨τ, hτ, hτR, fun t _ => hvertical t, hbefore, htail, ?_, ?_⟩
  · have hd := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt τ (hγ τ)
    simpa [EuclideanSpace.coe_proj, Function.comp_def, hright (γ τ) hτR.ge] using hd
  · intro t ht htr
    rcases lt_or_ge t τ with htτ | htτ
    · rcases ht.eq_or_lt with ht | ht
      · subst t
        linarith [hstart]
      · exact False.elim ((hbefore t ⟨ht, htτ⟩).2.ne htr)
    · have heq := htail (t - τ) (sub_nonneg.mpr htτ)
      have hx := congrArg (fun x : E₂ => x 0) heq
      simp only [add_sub_cancel, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, mul_one, hτR, htr] at hx
      linarith



theorem existsUnique_horizontal_section_hit
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {L R B T : ℝ}
    (hfix : ∀ x : E₂,
      x 0 ≤ L ∨ R ≤ x 0 ∨ x 1 ≤ B ∨ T ≤ x 1 → V x = v₀)
    {γ : ℝ → E₂} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) :
    ∃! t : ℝ, γ t 0 = L := by
  have hleft : ∀ x : E₂, x 0 ≤ L → V x = v₀ :=
    fun x hx => hfix x (Or.inl hx)
  have hright : ∀ x : E₂, R ≤ x 0 → V x = v₀ :=
    fun x hx => hfix x (Or.inr (Or.inl hx))
  have hhorizontal : ∀ x : E₂, x 1 ≤ B ∨ T ≤ x 1 → V x = v₀ :=
    fun x hx => hfix x (Or.inr (Or.inr hx))
  have hunique (a b : ℝ) (ha : γ a 0 = L) (hb : γ b 0 = L) : b = a := by
    rcases le_total a b with hab | hba
    · have heq := eq_horizontal_backward_ray hV hγ hleft hb.le (b - a) (sub_nonneg.mpr hab)
      have hx := congrArg (fun x : E₂ => x 0) heq
      simp only [sub_sub_cancel, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, mul_one, ha, hb] at hx
      linarith
    · have heq := eq_horizontal_backward_ray hV hγ hleft ha.le (a - b) (sub_nonneg.mpr hba)
      have hx := congrArg (fun x : E₂ => x 0) heq
      simp only [sub_sub_cancel, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, mul_one, ha, hb] at hx
      linarith
  suffices hexists : ∃ t : ℝ, γ t 0 = L by
    obtain ⟨a, ha⟩ := hexists
    exact ⟨a, ha, fun b hb => hunique a b ha hb⟩
  by_cases hstart : γ 0 0 ≤ L
  · let d : ℝ := L - γ 0 0
    have hd : 0 ≤ d := sub_nonneg.mpr hstart
    have hη (s : ℝ) (hs : s ∈ Icc 0 d) :
        HasDerivAt (fun u => γ 0 + u • v₀) (V (γ 0 + s • v₀)) s := by
      have hpos : (γ 0 + s • v₀) 0 ≤ L := by
        simpa using (show γ 0 0 + s ≤ L by dsimp [d] at hs; linarith [hs.2])
      rw [hleft _ hpos]
      simpa using ((hasDerivAt_id s).smul_const v₀).const_add (γ 0)
    have heq := Poincare.ODE.eqOn_Icc_of_hasDerivAt (hV.of_le (by simp))
      (fun s (_ : s ∈ Icc 0 d) => hγ s) hη (by simp)
    refine ⟨d, ?_⟩
    have hx := congrArg (fun x : E₂ => x 0) (heq ⟨hd, le_rfl⟩)
    simpa [d] using hx
  · have hstartL : L < γ 0 0 := lt_of_not_ge hstart
    have hvertical (t : ℝ) :
        γ t 1 ∈ Icc (min B (γ 0 1)) (max T (γ 0 1)) := by
      by_cases htB : γ t 1 ≤ B
      · have heq := eq_horizontal_line_of_height hV hγ hhorizontal (Or.inl htB) 0
        have hy := congrArg (fun x : E₂ => x 1) heq
        simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_one,
          Matrix.cons_val_zero, smul_zero, add_zero] at hy
        rw [← hy]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      · by_cases htT : T ≤ γ t 1
        · have heq := eq_horizontal_line_of_height hV hγ hhorizontal (Or.inr htT) 0
          have hy := congrArg (fun x : E₂ => x 1) heq
          simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_one,
            Matrix.cons_val_zero, smul_zero, add_zero] at hy
          rw [← hy]
          exact ⟨min_le_right _ _, le_max_right _ _⟩
        · exact ⟨(min_le_left _ _).trans (le_of_not_ge htB),
            (le_of_not_ge htT).trans (le_max_left _ _)⟩
    have hupper (t : ℝ) (ht : 0 ≤ t) : γ (-t) 0 ≤ max R (γ 0 0) := by
      by_cases hx : R ≤ γ (-t) 0
      · have heq := eq_horizontal_forward_ray hV hγ hright hx t ht
        have hx' := congrArg (fun x : E₂ => x 0) heq
        simp only [neg_add_cancel, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          Matrix.cons_val_zero, mul_one] at hx'
        exact (show γ (-t) 0 ≤ γ 0 0 by linarith).trans (le_max_right _ _)
      · exact (le_of_not_ge hx).trans (le_max_left _ _)
    have hfar : ∃ t ≥ 0, γ (-t) 0 < L := by
      by_contra! hbounded
      let box : Set E₂ := (fun p : ℝ × ℝ => (!₂[p.1, p.2] : E₂)) ''
        (Icc L (max R (γ 0 0)) ×ˢ Icc (min B (γ 0 1)) (max T (γ 0 1)))
      have hmap : Continuous (fun p : ℝ × ℝ => (!₂[p.1, p.2] : E₂)) := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> fun_prop
      have hcompact : IsCompact box := (isCompact_Icc.prod isCompact_Icc).image hmap
      have hreverse (t : ℝ) :
          HasDerivAt (fun s => γ (-s)) (-V (γ (-t))) t := by
        simpa only [Function.comp_def, neg_smul, one_smul] using
          (hγ (-t)).scomp t (hasDerivAt_neg t)
      apply not_isBounded_forward_orbit hV.neg (fun x => neg_ne_zero.mpr (hne x))
        (fun t _ => hreverse t)
      apply hcompact.isBounded.subset
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨(γ (-t) 0, γ (-t) 1),
        ⟨⟨hbounded t ht, hupper t ht⟩, hvertical (-t)⟩, ?_⟩
      ext i
      fin_cases i <;> simp
    obtain ⟨t, ht, hfar⟩ := hfar
    have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
    have hxcont : Continuous (fun s => γ s 0) := (EuclideanSpace.proj 0).continuous.comp hγc
    obtain ⟨a, _, ha⟩ := intermediate_value_Icc (neg_nonpos.mpr ht) hxcont.continuousOn
      (show L ∈ Icc (γ (-t) 0) (γ 0 0) from ⟨hfar.le, hstartL.le⟩)
    exact ⟨a, ha⟩


theorem existsUnique_horizontal_right_section_hit
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {L R B T : ℝ}
    (hfix : ∀ x : E₂,
      x 0 ≤ L ∨ R ≤ x 0 ∨ x 1 ≤ B ∨ T ≤ x 1 → V x = v₀)
    {γ : ℝ → E₂} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) :
    ∃! t : ℝ, γ t 0 = R := by
  let W : E₂ → E₂ := fun x => V (-x)
  let β : ℝ → E₂ := fun t => -γ (-t)
  have hW : ContDiff ℝ ∞ W := hV.comp contDiff_neg
  have hWfix (x : E₂)
      (hx : x 0 ≤ -R ∨ -L ≤ x 0 ∨ x 1 ≤ -T ∨ -B ≤ x 1) : W x = v₀ := by
    apply hfix
    rcases hx with hx | hx | hx | hx
    · exact Or.inr (Or.inl (by simpa using (show R ≤ -x 0 by linarith)))
    · exact Or.inl (by simpa using (show -x 0 ≤ L by linarith))
    · exact Or.inr (Or.inr (Or.inr (by simpa using (show T ≤ -x 1 by linarith))))
    · exact Or.inr (Or.inr (Or.inl (by simpa using (show -x 1 ≤ B by linarith))))
  have hβ (t : ℝ) : HasDerivAt β (W (β t)) t := by
    convert! ((hγ (-t)).scomp t (hasDerivAt_neg t)).neg using 1
    simp [β, W]
  obtain ⟨a, ha, huniq⟩ :=
    existsUnique_horizontal_section_hit hW (fun x => hne (-x)) hWfix hβ
  have haR : γ (-a) 0 = R := by
    change -(γ (-a) 0) = -R at ha
    exact neg_inj.mp ha
  refine ⟨-a, haR, ?_⟩
  intro b hb
  have hb' : β (-b) 0 = -R := by simp [β, hb]
  have := huniq (-b) hb'
  linarith



theorem existsUnique_exterior_horizontal_section_hit
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {L R B T c : ℝ}
    (hfix : ∀ x : E₂,
      x 0 ≤ L ∨ R ≤ x 0 ∨ x 1 ≤ B ∨ T ≤ x 1 → V x = v₀)
    (hc : c ≤ L ∨ R ≤ c)
    {γ : ℝ → E₂} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) :
    ∃! t : ℝ, γ t 0 = c := by
  rcases hc with hc | hc
  · apply existsUnique_horizontal_section_hit hV hne (L := c) (R := R) (B := B) (T := T)
      (hγ := hγ)
    intro x hx
    apply hfix
    rcases hx with hx | hx
    · exact Or.inl (hx.trans hc)
    · exact Or.inr hx
  · apply existsUnique_horizontal_right_section_hit hV hne (L := L) (R := c) (B := B) (T := T)
      (hγ := hγ)
    intro x hx
    apply hfix
    rcases hx with hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl (hc.trans hx))
    · exact Or.inr (Or.inr hx)

end Poincare.ODE.Plane
