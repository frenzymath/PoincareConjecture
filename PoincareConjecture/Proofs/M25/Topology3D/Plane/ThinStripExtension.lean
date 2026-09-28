import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.SmallPerturbationFamily
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology NNReal

namespace PoincareConjecture.M25.Topology3D

theorem exists_uniform_axis_derivative_bound (F : ℝ × (ℝ × ℝ) → ℝ × ℝ)
    (hF : ContDiff ℝ ∞ F) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfix : ∀ z x, x ∉ K → F (z, x) = x)
    (hjet : ∀ z u, fderiv ℝ (fun x => F (z, x)) (u, 0) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x : ℝ × ℝ, |x.2| < ε → F (z, x) = x)
    {tol : ℝ} (htol : 0 < tol) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ < ε ∧ ∀ z u y, |y| ≤ 2 * δ →
      ‖fderiv ℝ (fun x => F (z, x)) (u, y) -
        ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤ tol := by
  have hunc : ContDiff ℝ ∞
      (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => F (q.1.1, q.2)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hD : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun x => F (p.1, x)) p.2) :=
    hunc.fderiv contDiff_snd (by simp)
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  let Z : Set (ℝ × (ℝ × ℝ)) := Icc 0 1 ×ˢ (Icc (-R) R ×ˢ {0})
  let W : Set (ℝ × (ℝ × ℝ)) := {p |
    ‖fderiv ℝ (fun x => F (p.1, x)) p.2 - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ < tol}
  have hZ : IsCompact Z := isCompact_Icc.prod (isCompact_Icc.prod isCompact_singleton)
  have hW : IsOpen W := isOpen_lt (hD.continuous.sub continuous_const).norm continuous_const
  have hZW : Z ⊆ W := by
    rintro ⟨z, u, y⟩ ⟨_, _, hy⟩
    have hy0 : y = 0 := hy
    subst y
    change ‖fderiv ℝ (fun x => F (z, x)) (u, 0) - _‖ < tol
    simpa only [hjet, sub_self, norm_zero] using htol
  obtain ⟨ρ, hρ, hρW⟩ := hZ.exists_thickening_subset_open hW hZW
  let δ := min (ε / 4) (ρ / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : 2 * δ < ε := by
    have hh : δ ≤ ε / 4 := min_le_left _ _
    linarith
  have hδρ : 2 * δ < ρ := by
    have hh : δ ≤ ρ / 4 := min_le_right _ _
    linarith
  refine ⟨δ, hδ, hδε, ?_⟩
  intro z u y hy
  by_cases hz : z ≤ 0 ∨ 1 ≤ z
  · have heq : (fun x => F (z, x)) =ᶠ[𝓝 (u, y)] id := by
      have hn : ∀ᶠ x : ℝ × ℝ in 𝓝 (u, y), |x.2| < ε :=
        (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (hy.trans_lt hδε)
      filter_upwards [hn] with x hx
      exact hstrip z hz x hx
    rw [heq.fderiv_eq, fderiv_id, sub_self, norm_zero]
    exact htol.le
  · by_cases hu : |u| ≤ R
    · have hp : (z, (u, y)) ∈ thickening ρ Z := by
        apply mem_thickening_iff.mpr
        refine ⟨(z, (u, 0)), ⟨?_, abs_le.mp hu, rfl⟩, ?_⟩
        · exact ⟨(lt_of_not_ge (not_or.mp hz).1).le,
            (lt_of_not_ge (not_or.mp hz).2).le⟩
        · simpa [Prod.dist_eq, Real.dist_eq] using hy.trans_lt hδρ
      exact (hρW hp).le
    · have hnot : (u, y) ∉ K := by
        intro hk
        have hh := (norm_fst_le (u, y)).trans_lt (hbound _ hk)
        rw [Real.norm_eq_abs] at hh
        exact hu hh.le
      have heq : (fun x => F (z, x)) =ᶠ[𝓝 (u, y)] id := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hnot] with x hx
        exact hfix z x hx
      rw [heq.fderiv_eq, fderiv_id, sub_self, norm_zero]
      exact htol.le

theorem exists_supported_strip_extension (F : ℝ × (ℝ × ℝ) → ℝ × ℝ)
    (hF : ContDiff ℝ ∞ F) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfix : ∀ z x, x ∉ K → F (z, x) = x)
    (haxis : ∀ z u, F (z, (u, 0)) = (u, 0))
    (hjet : ∀ z u, fderiv ℝ (fun x => F (z, x)) (u, 0) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x : ℝ × ℝ, |x.2| < ε → F (z, x) = x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ D : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => D p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (D p.1).symm p.2) ∧
      (∀ z x, |x.2| ≤ δ → D z x = F (z, x)) ∧
      (∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x, D z x = x) ∧
      (∀ z x, x ∉ K → D z x = x ∧ (D z).symm x = x) := by
  let β : ℝ → ℝ := fun y => Real.smoothTransition (2 - y ^ 2)
  have hβ : ContDiff ℝ ∞ β :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))
  have hβone (y : ℝ) (hy : |y| ≤ 1) : β y = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have hh := abs_le.mp hy
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith : 0 ≤ y + 1)]
  have hβzero (y : ℝ) (hy : 2 ≤ |y|) : β y = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    nlinarith [sq_abs y, mul_nonneg (sub_nonneg.mpr hy) (by positivity : 0 ≤ |y| + 2)]
  have hβK : HasCompactSupport β := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2))
    intro y hy
    apply hβzero
    by_contra hn
    exact hy (abs_le.mp (lt_of_not_ge hn).le)
  obtain ⟨C, hC⟩ := (hβK.fderiv ℝ).exists_bound_of_continuous
    (hβ.continuous_fderiv (by simp))
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right C 0]
  have hDb (y : ℝ) : ‖fderiv ℝ β y‖ ≤ B :=
    (hC y).trans (by dsimp [B]; linarith [le_max_left C 0])
  let tol := 1 / (4 * (1 + 2 * B))
  have htol : 0 < tol := by dsimp [tol]; positivity
  have htoleq : (1 + 2 * B) * tol = 1 / 4 := by dsimp [tol]; field_simp
  obtain ⟨δ, hδ, hδε, hsmall⟩ :=
    exists_uniform_axis_derivative_bound F hF hK hfix hjet hε hstrip htol
  let χ : ℝ × ℝ → ℝ := fun x => β (δ⁻¹ • x.2)
  have hχ : ContDiff ℝ ∞ χ := hβ.comp (contDiff_snd.const_smul δ⁻¹)
  have hχone (x : ℝ × ℝ) (hx : |x.2| ≤ δ) : χ x = 1 := by
    apply hβone
    change |δ⁻¹ * x.2| ≤ 1
    rw [abs_mul, abs_inv, abs_of_pos hδ, ← div_eq_inv_mul]
    exact (div_le_one hδ).mpr hx
  have hχzero (x : ℝ × ℝ) (hx : 2 * δ ≤ |x.2|) : χ x = 0 := by
    apply hβzero
    change 2 ≤ |δ⁻¹ * x.2|
    rw [abs_mul, abs_inv, abs_of_pos hδ, ← div_eq_inv_mul]
    exact (le_div_iff₀ hδ).mpr hx
  have hχbound (x : ℝ × ℝ) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hDχ (x : ℝ × ℝ) : ‖fderiv ℝ χ x‖ ≤ B / δ := by
    have hd := (hβ.differentiable (by simp) (δ⁻¹ • x.2)).hasFDerivAt.comp x
      ((hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) x).const_smul δ⁻¹)
    change HasFDerivAt χ ((fderiv ℝ β (δ⁻¹ • x.2)).comp
      (δ⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) x at hd
    rw [hd.fderiv]
    calc
      _ ≤ ‖fderiv ℝ β (δ⁻¹ • x.2)‖ * ‖δ⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * (δ⁻¹ * 1) := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
        exact mul_le_mul (hDb _) (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (inv_nonneg.mpr hδ.le))
          (mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg _)) hB.le
      _ = B / δ := by rw [mul_one, div_eq_mul_inv]
  let G : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun p => p.2 + χ p.2 • (F p - p.2)
  have hG : ContDiff ℝ ∞ G :=
    contDiff_snd.add ((hχ.comp contDiff_snd).smul (hF.sub contDiff_snd))
  have hdiff (z : ℝ) : Differentiable ℝ (fun x => F (z, x)) :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hdist (z : ℝ) (x : ℝ × ℝ) (hx : |x.2| ≤ 2 * δ) :
      ‖F (z, x) - x‖ ≤ tol * (2 * δ) := by
    let S : Set (ℝ × ℝ) := univ ×ˢ Icc (-2 * δ) (2 * δ)
    have hS : Convex ℝ S := convex_univ.prod (convex_Icc _ _)
    have hzero : (x.1, (0 : ℝ)) ∈ S := ⟨mem_univ _, by constructor <;> linarith⟩
    have hxS : x ∈ S := ⟨mem_univ _, by simpa using abs_le.mp hx⟩
    have hm := hS.norm_image_sub_le_of_norm_fderiv_le'
      (fun y _ => hdiff z y)
      (fun y hy => hsmall z y.1 y.2 (abs_le.mpr (by simpa using hy.2))) hzero hxS
    have heq : F (z, x) - F (z, (x.1, 0)) -
        ContinuousLinearMap.id ℝ (ℝ × ℝ) (x - (x.1, 0)) = F (z, x) - x := by
      rw [haxis, ContinuousLinearMap.id_apply]
      abel
    rw [heq] at hm
    have hn : ‖x - (x.1, 0)‖ = |x.2| := by
      rcases x with ⟨u, y⟩
      simp [Prod.norm_def, Real.norm_eq_abs]
    rw [hn] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left hx htol.le)
  have hclose (z : ℝ) (x : ℝ × ℝ) :
      ‖fderiv ℝ (fun y => G (z, y)) x - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤
        (1 / 2 : ℝ≥0) := by
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    by_cases hx : |x.2| ≤ 2 * δ
    · have ha := mul_le_mul (hχbound x) (hsmall z x.1 x.2 hx) (norm_nonneg _) zero_le_one
      have hb := mul_le_mul (hDχ x) (hdist z x hx) (norm_nonneg _) (div_nonneg hB.le hδ.le)
      have hcancel : B / δ * (tol * (2 * δ)) = 2 * B * tol := by field_simp
      calc
        _ ≤ ‖χ x‖ * ‖fderiv ℝ (fun y => F (z, y)) x -
              ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ + ‖fderiv ℝ χ x‖ * ‖F (z, x) - x‖ :=
          Poincare.Analysis.Calculus.norm_fderiv_cutoff_perturbation_sub_id_le
            (hχ.differentiable (by simp) x) (hdiff z x)
        _ ≤ 1 * tol + B / δ * (tol * (2 * δ)) := add_le_add ha hb
        _ = (1 + 2 * B) * tol := by rw [hcancel]; ring
        _ = 1 / 4 := htoleq
        _ ≤ 1 / 2 := by norm_num
    · have heq : (fun y => G (z, y)) =ᶠ[𝓝 x] id := by
        have hn : ∀ᶠ y : ℝ × ℝ in 𝓝 x, 2 * δ < |y.2| :=
          (isOpen_lt continuous_const continuous_snd.abs).mem_nhds (lt_of_not_ge hx)
        filter_upwards [hn] with y hy
        simp only [G, hχzero y hy.le, zero_smul, add_zero, id_eq]
      rw [heq.fderiv_eq, fderiv_id, sub_self, norm_zero]
      norm_num
  obtain ⟨D, hD, hDs, hDi⟩ := exists_smooth_diffeomorph_family_of_fderiv_close_id
    G hG (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  refine ⟨δ, hδ, D, hDs, hDi, ?_, ?_, ?_⟩
  · intro z x hx
    rw [hD]
    simp only [G, hχone x hx, one_smul, add_sub_cancel]
  · intro z hz x
    rw [hD]
    by_cases hx : |x.2| ≤ 2 * δ
    · simp only [G, hstrip z hz x (hx.trans_lt hδε), sub_self, smul_zero, add_zero]
    · simp only [G, hχzero x (lt_of_not_ge hx).le, zero_smul, add_zero]
  · intro z x hx
    have hf : D z x = x := by
      rw [hD]
      simp only [G, hfix z x hx, sub_self, smul_zero, add_zero]
    refine ⟨hf, ?_⟩
    have hi := congrArg (D z).symm hf
    simpa only [(D z).symm_apply_apply] using hi.symm

end PoincareConjecture.M25.Topology3D
