import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTransverseC1
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityDifferentialExtension










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture.M65Boundary

private def heinzProjection (j : Fin 3) : LoopAmbient →L[ℝ] LoopAmbient :=
  ContinuousLinearMap.id ℝ LoopAmbient -
    (EuclideanSpace.proj j).smulRight (EuclideanSpace.basisFun (Fin 3) ℝ j)

private theorem heinzProjection_apply (j : Fin 3) (v : LoopAmbient) (a : Fin 3) :
    heinzProjection j v a = if a = j then 0 else v a := by
  change v a - v j * (EuclideanSpace.basisFun (Fin 3) ℝ j) a = _
  by_cases haj : a = j
  · subst a; simp [EuclideanSpace.single]
  · simp [EuclideanSpace.single, haj]

private theorem heinzProjection_norm (j : Fin 3) (v : LoopAmbient) :
    ‖heinzProjection j v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro a _
  rw [heinzProjection_apply]
  split_ifs
  · simpa only [zero_pow two_ne_zero] using sq_nonneg (v a)
  · exact le_rfl

private def heinzWeakProjection {U : Set LoopPlane}
    (X : M65LocalWeakMap (id : LoopAmbient → LoopAmbient) U) (j : Fin 3) :
    M65LocalWeakMap (id : LoopAmbient → LoopAmbient) U where
  value z := heinzProjection j (X.value z)
  derivative i z := heinzProjection j (X.derivative i z)
  value_memLp K hc hs := (heinzProjection j).comp_memLp' (X.value_memLp K hc hs)
  derivative_memLp i K hc hs :=
    (heinzProjection j).comp_memLp' (X.derivative_memLp i K hc hs)
  weak_derivative test hc hs i a := by
    by_cases haj : a = j
    · simp only [heinzProjection_apply, if_pos haj, id_eq, mul_zero,
        integral_zero, neg_zero]
    · simpa only [heinzProjection_apply, if_neg haj, id_eq] using
        X.weak_derivative test hc hs i a

private theorem heinzProjection_fderiv (j : Fin 3) {f : LoopPlane → LoopAmbient}
    {z : LoopPlane} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (heinzProjection j ∘ f) z = (heinzProjection j).comp (fderiv ℝ f z) :=
  ((heinzProjection j).hasFDerivAt.comp z hf.hasFDerivAt).fderiv

private theorem heinzProjection_hessian (j : Fin 3) {f : LoopPlane → LoopAmbient}
    {U : Set LoopPlane} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {z : LoopPlane} (hz : z ∈ U) (u v : LoopPlane) :
    fderiv ℝ (fderiv ℝ (heinzProjection j ∘ f)) z u v =
      heinzProjection j (fderiv ℝ (fderiv ℝ f) z u v) := by
  have hnear : fderiv ℝ (heinzProjection j ∘ f) =ᶠ[𝓝 z]
      fun w => (heinzProjection j).comp (fderiv ℝ f w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact heinzProjection_fderiv j ((hf.contDiffAt (hU.mem_nhds hw)).differentiableAt
      (by simp))
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  rw [hnear.fderiv_eq]
  have hh := (ContinuousLinearMap.compL ℝ LoopPlane LoopAmbient LoopAmbient
    (heinzProjection j)).hasFDerivAt.comp z hD.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply] using
      congrArg (fun A : LoopPlane →L[ℝ] LoopPlane →L[ℝ] LoopAmbient => A u v) hh.fderiv

private theorem heinzProjection_energy (j : Fin 3) (v : Fin 2 → LoopAmbient) :
    (∑ i : Fin 2, ‖heinzProjection j (v i)‖ ^ 2) =
      ∑ a : Fin 3, if a = j then 0 else ∑ i : Fin 2, (v i a) ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, heinzProjection_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases haj : a = j
  · simp only [if_pos haj, zero_pow two_ne_zero, Finset.sum_const_zero]
  · simp only [if_neg haj]

private theorem heinz_halfDisk_unique {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) := by
  let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  have hK : Convex ℝ K := (convex_closedBall _ _).inter
    ((convex_Ici (0 : ℝ)).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hUK : U ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  apply uniqueDiffOn_convex hK
  let z := (r / 2) • EuclideanSpace.basisFun (Fin 2) ℝ 1
  have hz : z ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      change ‖(r / 2) • EuclideanSpace.basisFun (Fin 2) ℝ 1‖ < r
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr),
        (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one]
      exact half_lt_self hr
    · change 0 < z 1
      simpa [z, EuclideanSpace.single] using half_pos hr
  exact ⟨z, mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hU.mem_nhds hz) hUK)⟩





theorem heinz_quadratic_contDiffOn {R C H beta Λ : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (id : LoopAmbient → LoopAmbient) (ball (0 : LoopPlane) R))
    (hX : ContDiffOn ℝ ∞ X.value (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hXc : ContinuousOn X.value (closedBall (0 : LoopPlane) (R / 2)))
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hb : 0 < beta) (hΛ : 0 ≤ Λ)
    (hholder : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (R / 2),
      ‖X.value z - X.value x‖ ≤ H * dist z x ^ beta)
    (hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4), ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        Λ * r ^ (2 * beta))
    (j : Fin 3)
    (hzero : ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), z 1 = 0 →
      ∀ a : Fin 3, a ≠ j → X.value z a = 0)
    (G : LoopPlane → LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (hG : ContinuousOn G (closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1}))
    (hsymm : ∀ z ∈ closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1},
      ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1},
      ∀ v : LoopAmbient, v ≠ 0 → 0 < G z v v)
    (hdiag : ∀ z ∈ ball 0 (R / 2) ∩ {z | 0 < z 1},
      G z (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
        G z (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
    (hmixed : ∀ z ∈ ball 0 (R / 2) ∩ {z | 0 < z 1},
      G z (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = 0)
    (hgrowth : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤
        C * ∑ a : Fin 3, if a = j then 0 else ∑ i : Fin 2,
          (fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i) a) ^ 2) :
    ContDiffOn ℝ 1 X.value
      (closedBall (0 : LoopPlane) (R / 256) ∩ {z | 0 ≤ z 1}) := by
  classical
  let Y := heinzWeakProjection X j
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hYsmooth : ContDiffOn ℝ ∞ Y.value U :=
    (heinzProjection j).contDiff.comp_contDiffOn hX
  have hYcont : ContinuousOn Y.value (closedBall (0 : LoopPlane) (R / 2)) :=
    (heinzProjection j).continuous.comp_continuousOn hXc
  have hYholder : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (R / 2),
      ‖Y.value z - Y.value x‖ ≤ H * dist z x ^ beta := by
    intro x hx z hz
    calc
      _ = ‖heinzProjection j (X.value z - X.value x)‖ := by rw [map_sub]; rfl
      _ ≤ ‖X.value z - X.value x‖ := heinzProjection_norm j _
      _ ≤ _ := hholder x hx z hz
  have hYzero : ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), z 1 = 0 → Y.value z = 0 := by
    intro z hz he
    ext a
    change heinzProjection j (X.value z) a = 0
    rw [heinzProjection_apply]
    split_ifs with ha
    · rfl
    · exact hzero z hz he a ha
  have hfirst (z : LoopPlane) (hz : z ∈ U) :
      fderiv ℝ Y.value z = (heinzProjection j).comp (fderiv ℝ X.value z) :=
    heinzProjection_fderiv j ((hX.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  have hYgrowth (z : LoopPlane) (hz : z ∈ U) :
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ Y.value) z (b i) (b i)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ Y.value z (b i)‖ ^ 2 := by
    have hsecond (i : Fin 2) : fderiv ℝ (fderiv ℝ Y.value) z (b i) (b i) =
        heinzProjection j (fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) :=
      heinzProjection_hessian j hU hX hz (b i) (b i)
    calc
      _ = ‖heinzProjection j (∑ i : Fin 2,
          fderiv ℝ (fderiv ℝ X.value) z (b i) (b i))‖ := by rw [map_sum]; simp only [hsecond]
      _ ≤ ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)‖ :=
        heinzProjection_norm j _
      _ ≤ C * ∑ a : Fin 3, if a = j then 0 else ∑ i : Fin 2,
          (fderiv ℝ X.value z (b i) a) ^ 2 := hgrowth z hz
      _ = _ := by
        simp only [hfirst z hz, ContinuousLinearMap.comp_apply]
        rw [heinzProjection_energy]
  have hYdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4),
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2) ≤
        Λ * r ^ (2 * beta) := by
    intro x hx r hr hrr
    have hsub : closedBall x r ⊆ ball (0 : LoopPlane) R := by
      apply closedBall_subset_ball'
      rw [dist_zero_right]
      have hxn := mem_closedBall_zero_iff.mp hx
      linarith
    have hXI := integrable_finsetSum Finset.univ (fun i _ =>
      (X.derivative_memLp i _ (isCompact_closedBall _ _) hsub).norm.integrable_sq)
    have hYI := integrable_finsetSum Finset.univ (fun i _ =>
      (Y.derivative_memLp i _ (isCompact_closedBall _ _) hsub).norm.integrable_sq)
    apply (setIntegral_mono_on hYI hXI measurableSet_closedBall ?_).trans (hdecay x hx r hr hrr)
    intro z _
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (heinzProjection_norm j (X.derivative i z))
  have hYC1 := zero_trace_quadratic_contDiffOn hR Y hYsmooth hYcont hC hH hb hΛ
    hYholder hYzero hYgrowth hYdecay
  let r := R / 64
  let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let V := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrhalf : r ≤ R / 2 := by dsimp only [r]; linarith
  have hrR : r ≤ R := by dsimp only [r]; linarith
  have hVU : V ⊆ U := fun z hz => ⟨ball_subset_ball hrR hz.1, hz.2⟩
  have hVK : V ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hKhalf : K ⊆ closedBall (0 : LoopPlane) (R / 2) ∩ {z | 0 ≤ z 1} :=
    fun z hz => ⟨closedBall_subset_closedBall hrhalf hz.1, hz.2⟩
  have hVhalf : V ⊆ ball (0 : LoopPlane) (R / 2) ∩ {z | 0 < z 1} :=
    fun z hz => ⟨ball_subset_ball hrhalf hz.1, hz.2⟩
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hDY : ContinuousOn (fderivWithin ℝ Y.value K) K :=
    hYC1.continuousOn_fderivWithin (heinz_halfDisk_unique hr) le_rfl
  let T := fun z a => (fderivWithin ℝ Y.value K z (b 0) a : ℂ) -
    I * (fderivWithin ℝ Y.value K z (b 1) a : ℂ)
  have hT : ContinuousOn T K := by
    apply continuousOn_pi.mpr
    intro a
    have h0 := (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp_continuousOn
      (hDY.clm_apply (continuousOn_const (c := b 0)))
    have h1 := (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp_continuousOn
      (hDY.clm_apply (continuousOn_const (c := b 1)))
    exact (continuous_ofReal.comp_continuousOn h0).sub
      (continuousOn_const.mul (continuous_ofReal.comp_continuousOn h1))
  have hTeq (z : LoopPlane) (hz : z ∈ V) (a : Fin 3) (haj : a ≠ j) :
      T z a = (fderiv ℝ X.value z (b 0) a : ℂ) -
        I * (fderiv ℝ X.value z (b 1) a : ℂ) := by
    have hn : K ∈ 𝓝 z := mem_of_superset (hV.mem_nhds hz) hVK
    simp only [T, fderivWithin_of_mem_nhds hn, hfirst z (hVU hz),
      ContinuousLinearMap.comp_apply, heinzProjection_apply, if_neg haj]
  obtain ⟨D, hD, hDeq⟩ := exists_continuous_full_differential hr X.value
    ((hX.mono hVU).of_le (by simp)) G (hG.mono hKhalf)
    (fun z hz => hsymm z (hKhalf hz)) (fun z hz => hpos z (hKhalf hz))
    (fun z hz => hdiag z (hVhalf hz)) (fun z hz => hmixed z (hVhalf hz)) j T hT hTeq
  have hfinish := contDiffOn_halfDisk_of_continuous_differential hr X.value
    (hXc.mono (fun z hz => (hKhalf hz).1)) ((hX.mono hVU).of_le (by simp)) D hD hDeq
  have hquarter : r / 4 = R / 256 := by dsimp only [r]; ring
  simpa only [hquarter] using hfinish

end PoincareConjecture.M65Boundary
