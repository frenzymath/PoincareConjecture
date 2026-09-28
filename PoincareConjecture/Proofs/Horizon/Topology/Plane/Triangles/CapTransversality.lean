import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CornerCaps
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false
open Set
open scoped ContDiff Topology Matrix

namespace Poincare.Topology.Plane.Triangles

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def capExcess (F : OpenPartialHomeomorph (ℝ × ℝ) E) (ε : ℝ) (z : E) : ℝ :=
  (F.symm z).1 + (F.symm z).2 - ε

private theorem cap_inverse_derivative
    (F : OpenPartialHomeomorph (ℝ × ℝ) E)
    (hF : ContDiffOn ℝ ∞ F F.source) (hI : ContDiffOn ℝ ∞ F.symm F.target)
    {q : ℝ × ℝ} (hq : q ∈ F.source) :
    Function.LeftInverse (fderiv ℝ F.symm (F q)) (fderiv ℝ F q) := by
  have hdF := ((hF q hq).contDiffAt (F.open_source.mem_nhds hq)).differentiableAt
    (by simp) |>.hasFDerivAt
  have hdI := ((hI (F q) (F.map_source hq)).contDiffAt
    (F.open_target.mem_nhds (F.map_source hq))).differentiableAt (by simp) |>.hasFDerivAt
  have he := (hdI.comp q hdF).unique
    ((hasFDerivAt_id q).congr_of_eventuallyEq (F.eventually_left_inverse hq))
  intro v
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L v) he

private theorem capExcess_fderiv_apply
    (F : OpenPartialHomeomorph (ℝ × ℝ) E) (hI : ContDiffOn ℝ ∞ F.symm F.target)
    (ε : ℝ) {q : ℝ × ℝ} (hq : q ∈ F.source) (v : E) :
    fderiv ℝ (capExcess F ε) (F q) v =
      (fderiv ℝ F.symm (F q) v).1 + (fderiv ℝ F.symm (F q) v).2 := by
  unfold capExcess
  have hdI := ((hI (F q) (F.map_source hq)).contDiffAt
    (F.open_target.mem_nhds (F.map_source hq))).differentiableAt (by simp) |>.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) ((hdI.fst.add hdI.snd).sub_const ε).fderiv
  simpa only [Pi.add_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using he

omit [NormedSpace ℝ E] in

theorem capExcess_nonpos_on_cap
    (F : OpenPartialHomeomorph (ℝ × ℝ) E) {ε : ℝ}
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source) :
    ∀ z ∈ F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε}, capExcess F ε z ≤ 0 := by
  rintro z ⟨q, hq, rfl⟩
  rw [capExcess, F.left_inv (hsource hq)]
  exact sub_nonpos.mpr hq.2.2

theorem cap_chord_fderiv
    (F : OpenPartialHomeomorph (ℝ × ℝ) E) (hF : ContDiffOn ℝ ∞ F F.source)
    {ε : ℝ} (hε : 0 < ε)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    (hchord : ∀ t ∈ Icc (0 : ℝ) 1, F ((1 - t) * ε, t * ε) =
      (1 - t) • F (ε, 0) + t • F (0, ε))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fderiv ℝ F ((1 - t) * ε, t * ε) (-ε, ε) = F (0, ε) - F (ε, 0) := by
  have hq : ((1 - t) * ε, t * ε) ∈ F.source := hsource
    ⟨mul_nonneg (sub_nonneg.mpr ht.2) hε.le, mul_nonneg ht.1 hε.le, by dsimp; linarith⟩
  have hdF := ((hF _ hq).contDiffAt (F.open_source.mem_nhds hq)).differentiableAt
    (by simp) |>.hasFDerivAt
  have hpath : HasDerivAt (fun u : ℝ => ((1 - u) * ε, u * ε)) (-ε, ε) t := by
    simpa using (((hasDerivAt_id t).const_sub 1).mul_const ε).prodMk
      ((hasDerivAt_id t).mul_const ε)
  have hd := hdF.comp_hasDerivAt (f := fun u : ℝ => ((1 - u) * ε, u * ε)) t hpath
  have hline : HasDerivAt (fun u : ℝ => (1 - u) • F (ε, 0) + u • F (0, ε))
      (F (0, ε) - F (ε, 0)) t := by
    convert! (((hasDerivAt_id t).const_sub 1).smul_const (F (ε, 0))).add
      ((hasDerivAt_id t).smul_const (F (0, ε))) using 1
    simp [sub_eq_add_neg, add_comm]
  have hline' := hline.hasDerivWithinAt.congr_of_mem hchord ht
  exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one t ht)).symm.trans
    (hline'.derivWithin (uniqueDiffOn_Icc_zero_one t ht))

theorem cap_endpoint_transversality
    (F : OpenPartialHomeomorph (ℝ × ℝ) E)
    (hF : ContDiffOn ℝ ∞ F F.source) (hI : ContDiffOn ℝ ∞ F.symm F.target)
    {ε : ℝ} (hε : 0 < ε)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    (hchord : ∀ t ∈ Icc (0 : ℝ) 1, F ((1 - t) * ε, t * ε) =
      (1 - t) • F (ε, 0) + t • F (0, ε)) :
    LinearIndependent ℝ (![deriv (fun s : ℝ => F (s, 0)) ε,
      F (0, ε) - F (ε, 0)] : Fin 2 → E) ∧
    LinearIndependent ℝ (![deriv (fun t : ℝ => F (0, t)) ε,
      F (ε, 0) - F (0, ε)] : Fin 2 → E) ∧
    fderiv ℝ F.symm (F (ε, 0)) (F (0, ε) - F (ε, 0)) = (-ε, ε) ∧
    fderiv ℝ F.symm (F (0, ε)) (F (ε, 0) - F (0, ε)) = (ε, -ε) ∧
    fderiv ℝ (capExcess F ε) (F (ε, 0)) (deriv (fun s : ℝ => F (s, 0)) ε) = 1 ∧
    fderiv ℝ (capExcess F ε) (F (0, ε)) (deriv (fun t : ℝ => F (0, t)) ε) = 1 ∧
    fderiv ℝ (capExcess F ε) (F (ε, 0)) (F (0, ε) - F (ε, 0)) = 0 ∧
    fderiv ℝ (capExcess F ε) (F (0, ε)) (F (ε, 0) - F (0, ε)) = 0 := by
  have hq₁ : (ε, (0 : ℝ)) ∈ F.source := hsource ⟨hε.le, le_rfl, by simp⟩
  have hq₂ : ((0 : ℝ), ε) ∈ F.source := hsource ⟨le_rfl, hε.le, by simp⟩
  have hleft₁ := cap_inverse_derivative F hF hI hq₁
  have hleft₂ := cap_inverse_derivative F hF hI hq₂
  have hdF₁ := ((hF _ hq₁).contDiffAt (F.open_source.mem_nhds hq₁)).differentiableAt
    (by simp) |>.hasFDerivAt
  have hdF₂ := ((hF _ hq₂).contDiffAt (F.open_source.mem_nhds hq₂)).differentiableAt
    (by simp) |>.hasFDerivAt
  have haxis₁ : deriv (fun s : ℝ => F (s, 0)) ε = fderiv ℝ F (ε, 0) (1, 0) :=
    (hdF₁.comp_hasDerivAt (f := fun s : ℝ => (s, 0)) ε
      ((hasDerivAt_id ε).prodMk (hasDerivAt_const ε (0 : ℝ)))).deriv
  have haxis₂ : deriv (fun t : ℝ => F (0, t)) ε = fderiv ℝ F (0, ε) (0, 1) :=
    (hdF₂.comp_hasDerivAt (f := fun t : ℝ => (0, t)) ε
      ((hasDerivAt_const ε (0 : ℝ)).prodMk (hasDerivAt_id ε))).deriv
  have hchord₁ : fderiv ℝ F (ε, 0) (-ε, ε) = F (0, ε) - F (ε, 0) := by
    simpa using cap_chord_fderiv F hF hε hsource hchord (t := 0) ⟨le_rfl, zero_le_one⟩
  have hchord₂ : fderiv ℝ F (0, ε) (ε, -ε) = F (ε, 0) - F (0, ε) := by
    have hc : fderiv ℝ F (0, ε) (-ε, ε) = F (0, ε) - F (ε, 0) := by
      simpa using cap_chord_fderiv F hF hε hsource hchord (t := 1) ⟨zero_le_one, le_rfl⟩
    have hn := congrArg Neg.neg hc
    rw [← map_neg] at hn
    simpa using hn
  have hind₁ : LinearIndependent ℝ (![((1 : ℝ), (0 : ℝ)), (-ε, ε)] : Fin 2 → ℝ × ℝ) := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      exact hε.ne' (congrArg Prod.snd h)
    · intro a h
      have haε : a * ε = 0 := congrArg Prod.snd h
      have ha : a = 0 := (mul_eq_zero.mp haε).resolve_right hε.ne'
      have he := congrArg Prod.fst h
      simp [ha] at he
  have hind₂ : LinearIndependent ℝ (![((0 : ℝ), (1 : ℝ)), (ε, -ε)] : Fin 2 → ℝ × ℝ) := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      exact hε.ne' (congrArg Prod.fst h)
    · intro a h
      have haε : a * ε = 0 := congrArg Prod.fst h
      have ha : a = 0 := (mul_eq_zero.mp haε).resolve_right hε.ne'
      have he := congrArg Prod.snd h
      simp [ha] at he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [haxis₁, ← hchord₁]
    convert hind₁.map_injOn (fderiv ℝ F (ε, 0)).toLinearMap hleft₁.injective.injOn using 1
    ext i
    fin_cases i <;> rfl
  · rw [haxis₂, ← hchord₂]
    convert hind₂.map_injOn (fderiv ℝ F (0, ε)).toLinearMap hleft₂.injective.injOn using 1
    ext i
    fin_cases i <;> rfl
  · rw [← hchord₁]
    exact hleft₁ (-ε, ε)
  · rw [← hchord₂]
    exact hleft₂ (ε, -ε)
  · rw [capExcess_fderiv_apply F hI ε hq₁, haxis₁, hleft₁]
    norm_num
  · rw [capExcess_fderiv_apply F hI ε hq₂, haxis₂, hleft₂]
    norm_num
  · rw [capExcess_fderiv_apply F hI ε hq₁, ← hchord₁, hleft₁]
    simp
  · rw [capExcess_fderiv_apply F hI ε hq₂, ← hchord₂, hleft₂]
    simp

theorem cap_endpoint_transversality_of_axis_maps
    (F : OpenPartialHomeomorph (ℝ × ℝ) E)
    (hF : ContDiffOn ℝ ∞ F F.source) (hI : ContDiffOn ℝ ∞ F.symm F.target)
    {ε : ℝ} (hε : 0 < ε)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    (hchord : ∀ t ∈ Icc (0 : ℝ) 1, F ((1 - t) * ε, t * ε) =
      (1 - t) • F (ε, 0) + t • F (0, ε))
    {f g : ℝ → E} (hf : DifferentiableAt ℝ f ε) (hg : DifferentiableAt ℝ g ε)
    (hfirst : ∀ s ∈ Icc (0 : ℝ) ε, F (s, 0) = f s)
    (hsecond : ∀ t ∈ Icc (0 : ℝ) ε, F (0, t) = g t) :
    LinearIndependent ℝ (![deriv f ε, g ε - f ε] : Fin 2 → E) ∧
    LinearIndependent ℝ (![deriv g ε, f ε - g ε] : Fin 2 → E) ∧
    fderiv ℝ (capExcess F ε) (f ε) (deriv f ε) = 1 ∧
    fderiv ℝ (capExcess F ε) (g ε) (deriv g ε) = 1 := by
  have hmem : ε ∈ Icc (0 : ℝ) ε := ⟨hε.le, le_rfl⟩
  have hq₁ : (ε, (0 : ℝ)) ∈ F.source := hsource ⟨hε.le, le_rfl, by simp⟩
  have hq₂ : ((0 : ℝ), ε) ∈ F.source := hsource ⟨le_rfl, hε.le, by simp⟩
  have hdF₁ := ((hF _ hq₁).contDiffAt (F.open_source.mem_nhds hq₁)).differentiableAt
    (by simp) |>.hasFDerivAt
  have hdF₂ := ((hF _ hq₂).contDiffAt (F.open_source.mem_nhds hq₂)).differentiableAt
    (by simp) |>.hasFDerivAt
  have hfaxis : DifferentiableAt ℝ (fun s : ℝ => F (s, 0)) ε :=
    (hdF₁.comp_hasDerivAt (f := fun s : ℝ => (s, 0)) ε
      ((hasDerivAt_id ε).prodMk (hasDerivAt_const ε (0 : ℝ)))).differentiableAt
  have hgaxis : DifferentiableAt ℝ (fun t : ℝ => F (0, t)) ε :=
    (hdF₂.comp_hasDerivAt (f := fun t : ℝ => (0, t)) ε
      ((hasDerivAt_const ε (0 : ℝ)).prodMk (hasDerivAt_id ε))).differentiableAt
  have hdf : deriv (fun s : ℝ => F (s, 0)) ε = deriv f ε := by
    rw [← hfaxis.derivWithin (uniqueDiffOn_Icc hε ε hmem),
      ← hf.derivWithin (uniqueDiffOn_Icc hε ε hmem)]
    exact derivWithin_congr hfirst (hfirst ε hmem)
  have hdg : deriv (fun t : ℝ => F (0, t)) ε = deriv g ε := by
    rw [← hgaxis.derivWithin (uniqueDiffOn_Icc hε ε hmem),
      ← hg.derivWithin (uniqueDiffOn_Icc hε ε hmem)]
    exact derivWithin_congr hsecond (hsecond ε hmem)
  obtain ⟨h₁, h₂, _, _, h₃, h₄, _, _⟩ := cap_endpoint_transversality F hF hI hε hsource hchord
  simpa only [hfirst ε hmem, hsecond ε hmem, hdf, hdg] using
    And.intro h₁ (And.intro h₂ (And.intro h₃ h₄))

end Poincare.Topology.Plane.Triangles
