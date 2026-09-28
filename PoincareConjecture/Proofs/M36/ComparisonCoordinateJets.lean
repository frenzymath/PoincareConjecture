import PoincareConjecture.Proofs.M36.AdaptedPolar
import PoincareConjecture.Proofs.M36.RadialWeights
import PoincareConjecture.Proofs.M36.CenteredNeckChart
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M36

section Calculus

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem exists_compact_local_jet_bound {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : ℕ, j ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  classical
  have hc (i : Fin (m + 1)) : ContinuousOn (iteratedFDeriv ℝ (i : ℕ) f) K :=
    fun x hx => ((hf x hx).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)).continuousWithinAt
  choose C hC using fun i : Fin (m + 1) => hK.exists_bound_of_continuousOn (hc i)
  let B := 1 + ∑ i : Fin (m + 1), max (C i) 0
  have hsum : 0 ≤ ∑ i : Fin (m + 1), max (C i) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨B, by dsimp [B]; linarith only [hsum], ?_⟩
  intro j hj x hx
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  calc
    _ ≤ C i := hC i x hx
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ k : Fin (m + 1), max (C k) 0 :=
      Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
    _ ≤ B := by dsimp [B]; linarith

theorem norm_iteratedFDeriv_smul_uniform_at
    {f : E → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ)
    {A B : ℝ} (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B)
    (hA : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hB : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => f y • g y) x‖ ≤ 2 ^ m * A * B := by
  have hsum : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  apply (Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt hf hg m).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hA j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (Nat.cast_nonneg _))
        (hB (m - j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA0)
    _ = 2 ^ m * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

theorem norm_iteratedFDeriv_comp_uniform_at
    {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (m : ℕ)
    {A B : ℝ} (hB1 : 1 ≤ B)
    (hA : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A)
    (hB : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (g ∘ f) x‖ ≤ m.factorial * A * B ^ m := by
  apply Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_le_of_contDiffAt hf hg m hA
  intro j hj hjm
  exact (hB j hj hjm).trans (le_self_pow₀ hB1 (Nat.ne_of_gt hj))

theorem norm_iteratedFDeriv_bilinear_uniform_at
    (L : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ)
    (hL : ‖L‖ ≤ 1) {A B : ℝ} (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B)
    (hA : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hB : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤ 2 ^ m * A * B := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω))
    (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω))
    (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (Filter.inter_mem hs ht)
  have h := L.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω)) hL
  simp only [iteratedFDerivWithin_of_isOpen _ hvo hxv] at h
  have hsum : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  apply h.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hA j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (Nat.cast_nonneg _))
        (hB (m - j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA0)
    _ = 2 ^ m * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

end Calculus

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable def sphereChartProjection (theta : UnitTwoSphere) : E₃ →L[ℝ] E₂ :=
  letI : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere (-theta))).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ℝ ∙ (↑(-theta) : E₃))ᗮ.orthogonalProjectionOnto

theorem sphereChartProjection_norm_le (theta : UnitTwoSphere) :
    ‖sphereChartProjection theta‖ ≤ 1 := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  apply (sphereChartProjection theta).opNorm_le_bound zero_le_one
  intro x
  change ‖(OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere (-theta))).repr
      ((ℝ ∙ (↑(-theta) : E₃))ᗮ.orthogonalProjectionOnto x)‖ ≤ 1 * ‖x‖
  simpa only [LinearIsometryEquiv.norm_map, one_mul] using
    Submodule.norm_orthogonalProjectionOnto_apply_le
      (ℝ ∙ (↑(-theta) : E₃))ᗮ x

theorem sphere_chart_projection_formula (theta y : UnitTwoSphere) :
    chartAt E₂ theta y = (2 / (1 + inner ℝ (theta : E₃) (y : E₃))) •
      sphereChartProjection theta (y : E₃) := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  change (OrthonormalBasis.fromOrthogonalSpanSingleton 2
      (ne_zero_of_mem_unit_sphere (-theta))).repr
      (stereographic (norm_eq_of_mem_sphere (-theta)) y) = _
  rw [stereographic_apply, map_smul]
  congr 1
  change 2 / (1 - inner ℝ (-(theta : E₃)) (y : E₃)) = _
  rw [inner_neg_left, sub_neg_eq_add]

noncomputable def comparisonAngularAmbient (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) : E₃ := ((adaptedInverseCoordinates g₀ x).1 : E₃)

theorem comparisonAngularAmbient_contDiffAt (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (comparisonAngularAmbient g₀) x := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  have hA := (adaptedInverseCoordinates_contMDiffOn g₀ x (by simpa using hx)).contMDiffAt
    (isOpen_compl_singleton.mem_nhds (by simpa using hx))
  exact ((contMDiff_coe_sphere (n := 2) (m := ∞)
    (adaptedInverseCoordinates g₀ x).1).comp x hA.fst).contDiffAt

noncomputable def comparisonCenteredCoordinates (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) (p : StandardCapSpace) : E₃ :=
  cylinderEuclideanEquiv.symm
    ((chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1,
      standardSurgeryHeight g₀ p - s)

theorem comparisonCenteredCoordinates_self (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) :
    comparisonCenteredCoordinates g₀ (adaptedInverseCoordinates g₀ x).1
      (standardSurgeryHeight g₀ x) x = 0 := by
  simp [comparisonCenteredCoordinates, sphere_chart_center_zero]

theorem comparisonCenteredCoordinates_contDiffAt_of_mem (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) {x : StandardCapSpace} (hx : x ≠ 0)
    (hchart : (adaptedInverseCoordinates g₀ x).1 ∈ (chartAt E₂ theta).source) :
    ContDiffAt ℝ ∞ (comparisonCenteredCoordinates g₀ theta s) x := by
  have hA := (adaptedInverseCoordinates_contMDiffOn g₀ x (by simpa using hx)).contMDiffAt
    (isOpen_compl_singleton.mem_nhds (by simpa using hx))
  have hc := contMDiffAt_of_mem_maximalAtlas (I := 𝓡 2) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas theta) hchart
  have hfirst : ContDiffAt ℝ ∞
      (fun p => (chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1) x :=
    (hc.comp x hA.fst).contDiffAt
  exact cylinderEuclideanEquiv.symm.contDiff.contDiffAt.comp x
    (hfirst.prodMk ((standardSurgeryHeight_contDiffAt g₀ hx).sub contDiffAt_const))

theorem comparisonCenteredCoordinates_contDiffAt (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (comparisonCenteredCoordinates g₀
      (adaptedInverseCoordinates g₀ x).1 (standardSurgeryHeight g₀ x)) x :=
  comparisonCenteredCoordinates_contDiffAt_of_mem g₀ _ _ hx (mem_chart_source E₂ _)



theorem exists_comparisonCenteredCoordinates_jet_bound (g₀ : StandardInitialMetric)
    {K : Set StandardCapSpace} (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (comparisonCenteredCoordinates g₀
        (adaptedInverseCoordinates g₀ x).1 (standardSurgeryHeight g₀ x)) x‖ ≤ C := by
  obtain ⟨U, hU1, hU⟩ := exists_compact_local_jet_bound hK
    (fun x hx => comparisonAngularAmbient_contDiffAt g₀ (hK0 x hx)) m
  obtain ⟨V, hV1, hV⟩ := exists_compact_local_jet_bound hK
    (fun x hx => standardSurgeryHeight_contDiffAt g₀ (hK0 x hx)) m
  let r : ℝ → ℝ := fun t => 2 / (1 + t)
  have hr : ContDiffAt ℝ ∞ r 1 :=
    contDiffAt_const.div (contDiffAt_const.add contDiffAt_id) (by norm_num)
  obtain ⟨A, hA1, hA⟩ := exists_compact_local_jet_bound
    (isCompact_singleton (x := (1 : ℝ)))
    (f := r) (fun x hx => by simpa only [Set.mem_singleton_iff.mp hx] using hr) m
  let W : ℝ := m.factorial * A * U ^ m
  let T : ℝ := (2 : ℝ) ^ m * W * U + 2 * V
  have hU0 : 0 ≤ U := zero_le_one.trans hU1
  have hV0 : 0 ≤ V := zero_le_one.trans hV1
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨1 + ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ * T,
    le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) hT0), ?_⟩
  intro x hx j hj
  let theta : UnitTwoSphere := (adaptedInverseCoordinates g₀ x).1
  let u : StandardCapSpace → ℝ := fun p => inner ℝ (theta : E₃)
    (comparisonAngularAmbient g₀ p)
  let v : StandardCapSpace → E₂ := sphereChartProjection theta ∘ comparisonAngularAmbient g₀
  have hy : ContDiffAt ℝ ∞ (comparisonAngularAmbient g₀) x :=
    comparisonAngularAmbient_contDiffAt g₀ (hK0 x hx)
  have hus : ContDiffAt ℝ ∞ u x := (innerSL ℝ (theta : E₃)).contDiff.contDiffAt.comp x hy
  have hvs : ContDiffAt ℝ ∞ v x :=
    (sphereChartProjection theta).contDiff.contDiffAt.comp x hy
  have hux : u x = 1 := by
    change inner ℝ (theta : E₃) (theta : E₃) = 1
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow]
  have hub (l : ℕ) (hl : l ≤ m) : ‖iteratedFDeriv ℝ l u x‖ ≤ U := by
    have h := (innerSL ℝ (theta : E₃)).norm_iteratedFDeriv_comp_left hy
      (by exact_mod_cast le_top : (l : ℕ∞ω) ≤ ∞)
    simpa only [u, Function.comp_def, innerSL_apply_apply,
      innerSL_apply_norm, norm_eq_of_mem_sphere, one_mul] using
      h.trans (mul_le_mul_of_nonneg_left (hU l hl x hx) (norm_nonneg _))
  have hvb (l : ℕ) (hl : l ≤ m) : ‖iteratedFDeriv ℝ l v x‖ ≤ U := by
    apply ((sphereChartProjection theta).norm_iteratedFDeriv_comp_left hy
      (by exact_mod_cast le_top : (l : ℕ∞ω) ≤ ∞)).trans
    exact (mul_le_mul_of_nonneg_left (hU l hl x hx) (norm_nonneg _)).trans
      (mul_le_of_le_one_left hU0 (sphereChartProjection_norm_le theta))
  have hrs : ContDiffAt ℝ ∞ (r ∘ u) x := (hux ▸ hr).comp x hus
  have hrb (l : ℕ) (hl : l ≤ m) : ‖iteratedFDeriv ℝ l (r ∘ u) x‖ ≤ W := by
    apply (norm_iteratedFDeriv_comp_uniform_at hus (hux ▸ hr) l hU1
      (fun k hk => by rw [hux]; exact hA k (hk.trans hl) 1 rfl)
      (fun k _ hk => hub k (hk.trans hl))).trans
    dsimp [W]
    gcongr
  have hfirst : (fun p => (chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1) =
      fun p => (r ∘ u) p • v p := by
    funext p
    exact sphere_chart_projection_formula theta (adaptedInverseCoordinates g₀ p).1
  have hfirsts : ContDiffAt ℝ ∞
      (fun p => (chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1) x := by
    rw [hfirst]
    exact hrs.smul hvs
  have hfirstb : ‖iteratedFDeriv ℝ j
      (fun p => (chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1) x‖ ≤
      (2 : ℝ) ^ m * W * U := by
    rw [hfirst]
    apply (norm_iteratedFDeriv_smul_uniform_at hrs hvs j hW0 hU0
      (fun l hl => hrb l (hl.trans hj)) (fun l hl => hvb l (hl.trans hj))).trans
    gcongr
    norm_num
  have hseconds : ContDiffAt ℝ ∞
      (fun p => standardSurgeryHeight g₀ p - standardSurgeryHeight g₀ x) x :=
    (standardSurgeryHeight_contDiffAt g₀ (hK0 x hx)).sub contDiffAt_const
  have hsecondb : ‖iteratedFDeriv ℝ j
      (fun p => standardSurgeryHeight g₀ p - standardSurgeryHeight g₀ x) x‖ ≤ 2 * V := by
    rw [fun_iteratedFDeriv_sub_apply
      ((standardSurgeryHeight_contDiffAt g₀ (hK0 x hx)).of_le
        (by exact_mod_cast le_top)) contDiffAt_const]
    apply (norm_sub_le _ _).trans
    have hc : ‖iteratedFDeriv ℝ j
        (fun _ : StandardCapSpace => standardSurgeryHeight g₀ x) x‖ ≤ V := by
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero] using hV 0 (Nat.zero_le _) x hx
      | succ j => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using hV0
    linarith [hV j hj x hx]
  let pair := fun p => ((chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1,
    standardSurgeryHeight g₀ p - standardSurgeryHeight g₀ x)
  have hpairs : ContDiffAt ℝ ∞ pair x := hfirsts.prodMk hseconds
  have hpairb : ‖iteratedFDeriv ℝ j pair x‖ ≤ T := by
    rw [iteratedFDeriv_prodMk hfirsts hseconds (by exact_mod_cast le_top),
      ContinuousMultilinearMap.opNorm_prod]
    exact max_le (hfirstb.trans (le_add_of_nonneg_right (by positivity)))
      (hsecondb.trans (le_add_of_nonneg_left (by positivity)))
  have hcomp := cylinderEuclideanEquiv.symm.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    hpairs (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j
    (cylinderEuclideanEquiv.symm.toContinuousLinearMap ∘ pair) x‖ ≤ _
  exact hcomp.trans ((mul_le_mul_of_nonneg_left hpairb (norm_nonneg _)).trans (by linarith))



theorem norm_iteratedFDeriv_bilinearPullback_at
    {B : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ} {f : E₃ → E₃} {x : E₃}
    (hf : ContDiffAt ℝ ∞ f x) (hB : ContDiffAt ℝ ∞ B (f x)) (m : ℕ)
    {A C : ℝ} (hA0 : 0 ≤ A) (hC1 : 1 ≤ C)
    (hBj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j B (f x)‖ ≤ A)
    (hfj : ∀ j, 1 ≤ j → j ≤ m + 1 → ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (fun y => (B (f y)).bilinearComp
      (fderiv ℝ f y) (fderiv ℝ f y)) x‖ ≤
        (2 ^ m * 2 ^ m * m.factorial * C ^ m * C * C) * A := by
  let A0 : ℝ := m.factorial * A * C ^ m
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hA00 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hBs : ContDiffAt ℝ ∞ (B ∘ f) x := hB.comp x hf
  have hds : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (m := ∞) (by simp)
  have hBbound (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (B ∘ f) x‖ ≤ A0 := by
    apply (norm_iteratedFDeriv_comp_uniform_at hf hB j hC1
      (fun l hl => hBj l (hl.trans hj))
      (fun l hl hlm => hfj l hl (by omega))).trans
    dsimp [A0]
    gcongr
  have hdbound (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ ≤ C := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hfj (j + 1) (by omega) (by omega)
  let first : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
    fun y => (B (f y)).comp (fderiv ℝ f y)
  have hfirsts : ContDiffAt ℝ ∞ first x := hBs.clm_comp hds
  have hfirstb (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j first x‖ ≤ (2 : ℝ) ^ m * A0 * C := by
    apply (norm_iteratedFDeriv_bilinear_uniform_at
      (ContinuousLinearMap.compL ℝ E₃ E₃ (E₃ →L[ℝ] ℝ)) hBs hds j
      (ContinuousLinearMap.norm_compL_le _ _ _ _) hA00 hC0
      (fun l hl => hBbound l (hl.trans hj))
      (fun l hl => hdbound l (hl.trans hj))).trans
    gcongr
    norm_num
  let firstFlip : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y => (first y).flip
  have hflips : ContDiffAt ℝ ∞ firstFlip x :=
    (ContinuousLinearMap.flipₗᵢ ℝ E₃ E₃ ℝ).contDiff.contDiffAt.comp x hfirsts
  have hflipb (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j firstFlip x‖ ≤ (2 : ℝ) ^ m * A0 * C := by
    change ‖iteratedFDeriv ℝ j
      (ContinuousLinearMap.flipₗᵢ ℝ E₃ E₃ ℝ ∘ first) x‖ ≤ _
    rw [(ContinuousLinearMap.flipₗᵢ ℝ E₃ E₃ ℝ).norm_iteratedFDeriv_comp_left]
    exact hfirstb j hj
  let second : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
    fun y => (firstFlip y).comp (fderiv ℝ f y)
  have hsecond : ‖iteratedFDeriv ℝ m second x‖ ≤
      2 ^ m * (2 ^ m * A0 * C) * C :=
    norm_iteratedFDeriv_bilinear_uniform_at
      (ContinuousLinearMap.compL ℝ E₃ E₃ (E₃ →L[ℝ] ℝ)) hflips hds m
      (ContinuousLinearMap.norm_compL_le _ _ _ _) (by positivity) hC0 hflipb hdbound
  change ‖iteratedFDeriv ℝ m
    (ContinuousLinearMap.flipₗᵢ ℝ E₃ E₃ ℝ ∘ second) x‖ ≤ _
  rw [(ContinuousLinearMap.flipₗᵢ ℝ E₃ E₃ ℝ).norm_iteratedFDeriv_comp_left]
  exact hsecond.trans_eq (by dsimp [A0]; ring)

end PoincareConjecture.M36
