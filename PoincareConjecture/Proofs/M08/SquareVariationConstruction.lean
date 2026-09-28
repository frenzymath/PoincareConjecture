import PoincareConjecture.Proofs.M08.VariationAction
import PoincareConjecture.Proofs.M08.SqrtRecovery
import PoincareConjecture.Proofs.M08.JacobiFieldPackaging

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

theorem exists_squareTube_radius {C : Set ℝ} (hC : IsCompact C)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hzero : C ×ˢ {(0 : ℝ)} ⊆ Ω)
    {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ C ×ˢ Ioo (-r) r ⊆ Ω := by
  obtain ⟨U, V, _, hV, hCU, hzeroV, hUV⟩ :=
    generalized_tube_lemma hC isCompact_singleton hΩ hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (hzeroV (mem_singleton (0 : ℝ))))
  refine ⟨min R ε, lt_min hR hε, min_le_left _ _, ?_⟩
  rintro ⟨s, v⟩ ⟨hs, hv⟩
  apply hUV ⟨hCU hs, hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
  exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right R ε)) hv.1,
    hv.2.trans_le (min_le_right R ε)⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem smoothSquareAction_intervalIntegrable {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τ₁ τ₂ : ℝ}
    (p : BackwardTimePath F T τ₁ τ₂) {U : Set ℝ} (hU : IsOpen U)
    (hCU : sqrtParameterInterval τ₁ τ₂ ⊆ U) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) :
    IntervalIntegrable (regularizedLIntegrand F T α) volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := by
  let C := sqrtParameterInterval τ₁ τ₂
  have hαC : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α C := hα.mono hCU
  have hA := (contMDiffOn_mfderiv_const_apply hU α hα (1 : ℝ)).mono hCU
  have ht : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun s : ℝ ↦ T - s ^ 2) C :=
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
  have hmem : MapsTo (fun s : ℝ ↦ T - s ^ 2) C J :=
    fun s hs ↦ p.time_mem (s ^ 2) (square_mem_backward_interval p hs)
  have hg := (movingMetric_pair_contMDiffOn F (fun s : ℝ ↦ T - s ^ 2) α
    (curveVelocity (n := n) α) (curveVelocity (n := n) α) ht hαC hA hA hmem).contDiffOn
  have hscalar := ((hM04.scalar_regular n M J F).comp (ht.prodMk hαC)
    (fun s hs ↦ ⟨hmem hs, mem_univ _⟩)).contDiffOn
  have hdensity : ContDiffOn ℝ ∞ (regularizedLIntegrand F T α) C :=
    ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul hscalar).add
      (contDiffOn_const.mul hg)
  exact hdensity.continuousOn.intervalIntegrable_of_Icc (Real.sqrt_le_sqrt p.ordered.le)

def backwardFamilyOfSquare {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) (H : ℝ × ℝ → M)
    (τ v : ℝ) : M := by
  classical
  exact if τ ∈ Icc τ₁ τ₂ then H (Real.sqrt τ, v) else p.curve τ

theorem backwardFamilyOfSquare_eq {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) (H : ℝ × ℝ → M)
    {τ : ℝ} (hτ : τ ∈ Icc τ₁ τ₂) (v : ℝ) :
    backwardFamilyOfSquare p H τ v = H (Real.sqrt τ, v) := by
  simp only [backwardFamilyOfSquare, if_pos hτ]

theorem backwardLIntegrand_congr_of_eventuallyEq {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {α β : ℝ → M} {τ : ℝ} (h : α =ᶠ[𝓝 τ] β) :
    backwardLIntegrand F T α τ = backwardLIntegrand F T β τ := by
  have hd := h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  simp only [backwardLIntegrand, curveVelocity, hd, h.eq_of_nhds]
  congr 2
  exact congrArg (fun x : M ↦ (F.metric (T - τ)).inner x
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) β τ) 1)
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) β τ) 1)) h.eq_of_nhds

def variationOfSquare {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τ₁ τ₂ : ℝ}
    (p : BackwardTimePath F T τ₁ τ₂) (H : ℝ × ℝ → M)
    (Ω : Set (ℝ × ℝ)) (hΩ : IsOpen Ω) (r : ℝ) (hr : 0 < r)
    (hCr : sqrtParameterInterval τ₁ τ₂ ×ˢ Ioo (-r) r ⊆ Ω)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ H Ω)
    (hzero : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, H (s, 0) = p.curve (s ^ 2)) :
    LVariation F T τ₁ τ₂ p where
  family := backwardFamilyOfSquare p H
  at_zero := by
    intro τ
    by_cases hτ : τ ∈ Icc τ₁ τ₂
    · rw [backwardFamilyOfSquare_eq p H hτ, hzero _ (sqrt_mem_sqrtParameterInterval hτ),
        Real.sq_sqrt (p.nonnegative.trans hτ.1)]
    · simp only [backwardFamilyOfSquare, if_neg hτ]
  radius := r
  radius_pos := hr
  squareFamily := fun s v ↦ H (s, v)
  squareDomain := Ω
  square_open := hΩ
  square_contains := hCr
  square_smooth := hH
  square_agrees := by
    intro s hs v _
    rw [backwardFamilyOfSquare_eq p H (square_mem_backward_interval p hs),
      Real.sqrt_sq ((Real.sqrt_nonneg τ₁).trans hs.1)]
  l_integrable := by
    intro v hv
    let U := (fun s : ℝ ↦ (s, v)) ⁻¹' Ω
    let α := fun s : ℝ ↦ H (s, v)
    have hU : IsOpen U := hΩ.preimage (continuous_id.prodMk continuous_const)
    have hCU : sqrtParameterInterval τ₁ τ₂ ⊆ U := fun s hs ↦ hCr ⟨hs, hv⟩
    have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U :=
      hH.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)
    have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α
        (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :=
      (hα.of_le (by simp)).mono (Ioo_subset_Icc_self.trans hCU)
    have hint := intervalIntegrable_of_square_transform p.nonnegative p.ordered.le
      (smoothSquareAction_intervalIntegrable hM04 p hU hCU α hα)
      (fun s hs ↦ regularizedLIntegrand_sqrtPullback F T p.nonnegative α hreg hs)
    apply hint.congr_uIoo
    intro τ hτ
    rw [uIoo_of_le p.ordered.le] at hτ
    apply backwardLIntegrand_congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
    exact (backwardFamilyOfSquare_eq p H (Ioo_subset_Icc_self ht) v).symm

def fixedVariationOfSquare {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τ₁ τ₂ : ℝ}
    (p : BackwardTimePath F T τ₁ τ₂) (H : ℝ × ℝ → M)
    (Ω : Set (ℝ × ℝ)) (hΩ : IsOpen Ω) (r : ℝ) (hr : 0 < r)
    (hCr : sqrtParameterInterval τ₁ τ₂ ×ˢ Ioo (-r) r ⊆ Ω)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ H Ω)
    (hzero : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, H (s, 0) = p.curve (s ^ 2))
    (hleft : ∀ v ∈ Ioo (-r) r, H (Real.sqrt τ₁, v) = p.curve τ₁)
    (hright : ∀ v ∈ Ioo (-r) r, H (Real.sqrt τ₂, v) = p.curve τ₂) :
    FixedEndpointLVariation F T τ₁ τ₂ p where
  toLVariation := variationOfSquare hM04 p H Ω hΩ r hr hCr hH hzero
  fixed_left v hv := (backwardFamilyOfSquare_eq p H ⟨le_rfl, p.ordered.le⟩ v).trans
    (hleft v hv)
  fixed_right v hv := (backwardFamilyOfSquare_eq p H ⟨p.ordered.le, le_rfl⟩ v).trans
    (hright v hv)

end PoincareConjecture.M08

