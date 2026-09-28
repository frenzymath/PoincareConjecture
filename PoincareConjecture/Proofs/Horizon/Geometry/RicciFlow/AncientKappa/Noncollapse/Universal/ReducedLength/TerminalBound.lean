import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ReducedLength.Recovery
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Constants









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture

namespace ReducedLengthMinimum.Variational

theorem exists_continuous_interval_join {M : Type*} [TopologicalSpace M]
    {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (α β : ℝ → M)
    (hα : ContinuousOn α (Icc a c)) (hβ : ContinuousOn β (Icc c b))
    (hmatch : α c = β c) :
    ∃ γ : ℝ → M, Continuous γ ∧ EqOn γ α (Icc a c) ∧ EqOn γ β (Icc c b) := by
  classical
  let left : ℝ → M := fun s => α (projIcc a c hac s)
  let right : ℝ → M := fun s => β (projIcc c b hcb s)
  have hl : Continuous left :=
    (continuousOn_iff_continuous_domRestrict.mp hα).comp continuous_projIcc
  have hr : Continuous right :=
    (continuousOn_iff_continuous_domRestrict.mp hβ).comp continuous_projIcc
  have hleft : EqOn left α (Icc a c) := by
    intro s hs
    dsimp only [left]
    rw [projIcc_of_mem _ hs]
  have hright : EqOn right β (Icc c b) := by
    intro s hs
    dsimp only [right]
    rw [projIcc_of_mem _ hs]
  let γ := (Iic c).piecewise left right
  refine ⟨γ, ?_, ?_, ?_⟩
  · apply Continuous.piecewise ?_ hl hr
    intro s hs
    have hs' : s = c := by simpa only [frontier_Iic, mem_singleton_iff] using hs
    subst s
    exact (hleft ⟨hac, le_rfl⟩).trans (hmatch.trans (hright ⟨le_rfl, hcb⟩).symm)
  · intro s hs
    exact (piecewise_eq_of_mem (Iic c) left right hs.2).trans (hleft hs)
  · intro s hs
    by_cases hsc : s ≤ c
    · have heq : s = c := le_antisymm hsc hs.1
      subst s
      exact (piecewise_eq_of_mem (Iic c) left right (show c ∈ Iic c by simp)).trans
        ((hleft ⟨hac, le_rfl⟩).trans hmatch)
    · exact (piecewise_eq_of_notMem (Iic c) left right hsc).trans (hright hs)

private theorem integral_le_nonnegative_const {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (f : ℝ → ℝ) (hf : ∀ s ∈ Icc a b, f s ≤ C) :
    (∫ s in a..b, f s) ≤ (b - a) * C := by
  by_cases hi : IntervalIntegrable f volume a b
  · have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hf
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  · rw [intervalIntegral.integral_undef hi]
    exact mul_nonneg (sub_nonneg.mpr hab) hC

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J}



theorem terminal_square_action_le
    (q : ℝ → M) {W : Set ℝ} (hW : IsOpen W) (hIW : Icc (1 : ℝ) 2 ⊆ W)
    (hq : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ q W)
    (hscalar : ∀ s ∈ Icc (1 : ℝ) 2, (F.connection (0 - s)).scalarCurvature (q s) ≤ 2)
    (hspeed : ∀ s ∈ Icc (1 : ℝ) 2,
      (F.metric (0 - s)).inner (q s) (curveVelocity q s) (curveVelocity q s) ≤ Real.exp 4) :
    (∫ s in 1..Real.sqrt 2, regularizedLIntegrand F 0 (fun r => q (r ^ 2)) s) ≤
      8 + 4 * Real.exp 4 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hbound : ∀ s ∈ Icc 1 (Real.sqrt 2),
      regularizedLIntegrand F 0 (fun r => q (r ^ 2)) s ≤ 8 + 4 * Real.exp 4 := by
    intro s hs
    have hs2 : s ^ 2 ∈ Icc (1 : ℝ) 2 := by
      constructor
      · nlinarith [hs.1]
      · exact (Real.le_sqrt (by linarith [hs.1]) (by norm_num)).mp hs.2
    have hvel := curveVelocity_comp_sq
      (((hq _ (hIW hs2)).contMDiffAt (hW.mem_nhds (hIW hs2))).mdifferentiableAt (by simp))
    unfold regularizedLIntegrand
    rw [hvel]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hR := hscalar _ hs2
    have hv := hspeed _ hs2
    have hpot := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2 * s ^ 2)
    have hkin := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * s ^ 2)
    have hexp := Real.exp_pos (4 : ℝ)
    nlinarith [hs2.2]
  have h := integral_le_nonnegative_const hsqrt (by positivity) _ hbound
  have hlen : Real.sqrt 2 - 1 ≤ 1 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  exact h.trans (by nlinarith [Real.exp_pos (4 : ℝ)])

end ReducedLengthMinimum.Variational

namespace LGeodesicTheory

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J}
  {τmax : ℝ}




theorem reducedLength_two_le_of_terminal_path
    (L : LGeodesicTheory F 0 τmax) (hmax : 2 ≤ τmax)
    (hzero : 0 ∈ J) (hback : ∀ s ∈ Icc (0 : ℝ) 2, 0 - s ∈ J)
    (hscalarRegular : ContinuousOn (fun z : ℝ × M =>
      (F.connection z.1).scalarCurvature z.2) (J ×ˢ univ))
    (p z y : M) (hseed : reducedLength F 0 p z 1 ≤ 3)
    (q : ℝ → M) {W : Set ℝ} (hW : IsOpen W) (hIW : Icc (1 : ℝ) 2 ⊆ W)
    (hq : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ q W)
    (hqone : q 1 = z) (hqtwo : q 2 = y)
    (hscalar : ∀ s ∈ Icc (1 : ℝ) 2, (F.connection (0 - s)).scalarCurvature (q s) ≤ 2)
    (hspeed : ∀ s ∈ Icc (1 : ℝ) 2,
      (F.metric (0 - s)).inner (q s) (curveVelocity q s) (curveVelocity q s) ≤ Real.exp 4) :
    reducedLength F 0 p y 2 ≤ universalNoncollapseLength := by
  let : MetricSpace M := referenceMetricSpace (F.metric 0)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨path, hp0, hp1, hpmin, hvalue⟩ :=
    L.reduced_length_attained 1 (by norm_num) (by linarith) p z
  have heuler := L.euler_lagrange 0 1 (by norm_num) (by norm_num) (by linarith) path hpmin
  obtain ⟨S⟩ := L.regularized_geodesic 0 1 (by norm_num) (by norm_num) (by linarith) path heuler
  have hIS : Icc (0 : ℝ) 1 ⊆ S.path.domain := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero, Real.sqrt_one] using S.path.interval_subset
  have hS (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : S.path.curve s = path.curve (s ^ 2) :=
    S.path.agrees s (by simpa only [sqrtParameterInterval, Real.sqrt_zero, Real.sqrt_one] using hs)
  have hsqI (s : ℝ) (hs : s ∈ Icc 1 (Real.sqrt 2)) : s ^ 2 ∈ Icc (1 : ℝ) 2 := by
    constructor
    · nlinarith [hs.1]
    · exact (Real.le_sqrt (by linarith [hs.1]) (by norm_num)).mp hs.2
  let β : ℝ → M := fun s => q (s ^ 2)
  let V : Set ℝ := (fun s : ℝ => s ^ 2) ⁻¹' W
  have hV : IsOpen V := hW.preimage (continuous_id.pow 2)
  have hIV : Icc 1 (Real.sqrt 2) ⊆ V := fun s hs => hIW (hsqI s hs)
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β V :=
    hq.comp ((contDiff_id.pow 2).contMDiff.contMDiffOn) (fun _ hs => hs)
  have hmatch : S.path.curve 1 = β 1 := by
    have hs := hS 1 (by norm_num)
    simp only [one_pow] at hs
    simpa only [β, one_pow, hqone] using hs.trans hp1
  obtain ⟨γ, hγ, hleft, hright⟩ := exists_continuous_interval_join
    (by norm_num : (0 : ℝ) ≤ 1) hsqrt S.path.curve β
    (S.path.smooth.continuousOn.mono hIS) (hβ.continuousOn.mono hIV) hmatch
  have hγ0 : γ 0 = p := by
    rw [hleft (by norm_num), hS 0 (by norm_num)]
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hp0
  have hγend : γ (Real.sqrt 2) = y := by
    rw [hright ⟨hsqrt, le_rfl⟩]
    change q ((Real.sqrt 2) ^ 2) = y
    simpa only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] using hqtwo
  have hpotential : ContinuousOn (fun a : ℝ × M =>
      2 * a.1 ^ 2 * (F.connection (0 - a.1 ^ 2)).scalarCurvature a.2)
      (Icc 0 (Real.sqrt 2) ×ˢ univ) := by
    apply (continuousOn_const.mul (continuousOn_fst.pow 2)).mul
    apply hscalarRegular.comp
      ((continuousOn_const.sub (continuousOn_fst.pow 2)).prodMk continuousOn_snd)
    intro a ha
    exact ⟨hback _ ⟨sq_nonneg _,
      (Real.le_sqrt ha.1.1 (by norm_num)).mp ha.1.2⟩, mem_univ _⟩
  have hbound := reducedLength_le_two_smooth_pieces L (by norm_num) hmax
    ⟨by norm_num, hsqrt⟩ hzero hback hpotential γ S.path.curve β hγ
    S.path.open_domain hV hIS hIV S.path.smooth hβ hleft hright
  rw [hγ0, hγend] at hbound
  have haction : (∫ s in 0..1, regularizedLIntegrand F 0 S.path.curve s) =
      backwardLLength F 0 0 1 path.curve := by
    calc
      _ = ∫ s in 0..1, regularizedLIntegrand F 0 (fun r => path.curve (r ^ 2)) s := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
        intro s hs
        apply regularizedLIntegrand_congr_eventually
        exact eventually_of_mem (isOpen_Ioo.mem_nhds hs)
          (fun r hr => hS r (Ioo_subset_Icc_self hr))
      _ = _ := by simpa only [regularizedLAction, Real.sqrt_one] using (squarePath_action path).2
  rw [haction] at hbound
  have hseedAction : backwardLLength F 0 0 1 path.curve ≤ 6 := by
    rw [Real.sqrt_one] at hvalue
    norm_num at hvalue
    linarith
  have htail := terminal_square_action_le q hW hIW hq hscalar hspeed
  have htotal : 2 * Real.sqrt 2 * reducedLength F 0 p y 2 ≤ 14 + 4 * Real.exp 4 := by
    change (∫ s in 1..Real.sqrt 2, regularizedLIntegrand F 0 β s) ≤ _ at htail
    linarith
  have hconst : 14 + 4 * Real.exp 4 ≤ 2 * universalNoncollapseLength := by
    unfold universalNoncollapseLength
    nlinarith [Real.exp_pos (4 : ℝ)]
  have hscale : 2 * universalNoncollapseLength ≤
      (2 * Real.sqrt 2) * universalNoncollapseLength :=
    mul_le_mul_of_nonneg_right (by nlinarith) universalNoncollapseLength_pos.le
  exact (mul_le_mul_iff_right₀ (show 0 < 2 * Real.sqrt 2 by positivity)).mp
    (htotal.trans (hconst.trans hscale))

end LGeodesicTheory

end PoincareConjecture
