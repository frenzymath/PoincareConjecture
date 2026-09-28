import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Resolvent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Cutoffs
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Bundle

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

def EnergyTest.mulSmooth (f : EnergyTest D Ω) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) : EnergyTest D Ω :=
  ⟨fun x => χ x * f x, hχ.mul f.smooth, f.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans f.support_subset⟩

@[simp] theorem EnergyTest.mulSmooth_apply (f : EnergyTest D Ω) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (x : M) :
    f.mulSmooth χ hχ x = χ x * f x := rfl

theorem EnergyTest.mulSmooth_support_subset (f : EnergyTest D Ω) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) :
    tsupport (f.mulSmooth χ hχ : M → ℝ) ⊆ tsupport χ :=
  tsupport_mul_subset_left

@[simp] theorem EnergyTest.coe_sum {ι : Type*} (s : Finset ι) (f : ι → EnergyTest D Ω) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih => simp only [Finset.sum_insert hi, EnergyTest.coe_add, ih]; rfl

def mulSmoothLinear (D : LeviCivitaData g) (Ω : Set M) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) :
    EnergyTest D Ω →ₗ[ℝ] EnergyTest D Ω where
  toFun f := f.mulSmooth χ hχ
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change χ x * (c * f x) = c * (χ x * f x)
    ring

theorem gradient_mul_energy_le (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (f : EnergyTest D Ω) (x : M) :
    g.inner x (D.gradient (f.mulSmooth χ hχ) x) (D.gradient (f.mulSmooth χ hχ) x) ≤
      2 * χ x ^ 2 * g.inner x (D.gradient f x) (D.gradient f x) +
      2 * f x ^ 2 * g.inner x (D.gradient χ x) (D.gradient χ x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hmul := D.gradient_mul ((hχ x).mdifferentiableAt (by simp))
    ((f.smooth x).mdifferentiableAt (by simp))
  change inner ℝ (D.gradient (fun y => χ y * f y) x)
    (D.gradient (fun y => χ y * f y) x) ≤ _
  rw [hmul, real_inner_self_eq_norm_sq]
  change ‖χ x • D.gradient f x + f x • D.gradient χ x‖ ^ 2 ≤
    2 * χ x ^ 2 * inner ℝ (D.gradient f x) (D.gradient f x) +
    2 * f x ^ 2 * inner ℝ (D.gradient χ x) (D.gradient χ x)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h := norm_add_le (χ x • D.gradient f x) (f x • D.gradient χ x)
  have hs := sq_le_sq₀ (norm_nonneg (χ x • D.gradient f x + f x • D.gradient χ x))
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h
  rw [norm_smul, norm_smul] at hs
  have hsum : (‖χ x‖ * ‖D.gradient f x‖ + ‖f x‖ * ‖D.gradient χ x‖) ^ 2 ≤
      2 * (‖χ x‖ * ‖D.gradient f x‖) ^ 2 +
      2 * (‖f x‖ * ‖D.gradient χ x‖) ^ 2 := by
    nlinarith [sq_nonneg (‖χ x‖ * ‖D.gradient f x‖ - ‖f x‖ * ‖D.gradient χ x‖)]
  simpa only [mul_pow, Real.norm_eq_abs, sq_abs, mul_assoc] using hs.trans hsum

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem exists_mulSmooth_norm_bound (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C ≥ 0, ∀ f : EnergyTest D Ω, ‖f.mulSmooth χ hχ‖ ≤ C * ‖f‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a, ha⟩ := (hc.mul_right (f := χ)).exists_bound_of_continuous
    (hχ.continuous.mul hχ.continuous)
  obtain ⟨b, hb⟩ := (D.hasCompactSupport_inner_gradient hc χ).exists_bound_of_continuous
    (D.continuous_inner_gradient hχ hχ)
  have ha' (x : M) : χ x ^ 2 ≤ |a| := by
    have := (le_abs_self (χ x * χ x)).trans ((ha x).trans (le_abs_self a))
    simpa only [pow_two] using this
  have hb' (x : M) : g.inner x (D.gradient χ x) (D.gradient χ x) ≤ |b| :=
    (le_abs_self _).trans ((hb x).trans (le_abs_self b))
  let C := 1 + 3 * |a| + 2 * |b|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, fun f => ?_⟩
  have hpoint (x : M) :
      f.mulSmooth χ hχ x * f.mulSmooth χ hχ x +
        g.inner x (D.gradient (f.mulSmooth χ hχ) x) (D.gradient (f.mulSmooth χ hχ) x) ≤
      C * (f x * f x + g.inner x (D.gradient f x) (D.gradient f x)) := by
    have hg0 : 0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
      change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
      exact real_inner_self_nonneg
    have hval := mul_le_mul_of_nonneg_right (ha' x) (sq_nonneg (f x))
    have hgrad := gradient_mul_energy_le χ hχ f x
    have hgrad₁ := mul_le_mul_of_nonneg_right (ha' x) hg0
    have hgrad₂ := mul_le_mul_of_nonneg_left (hb' x) (sq_nonneg (f x))
    dsimp only [EnergyTest.mulSmooth_apply, C]
    nlinarith [mul_nonneg (abs_nonneg a) (sq_nonneg (f x)),
      mul_nonneg (abs_nonneg a) hg0, mul_nonneg (abs_nonneg b) hg0]
  have he : energyInner (f.mulSmooth χ hχ) (f.mulSmooth χ hχ) ≤ C * energyInner f f := by
    rw [energyInner, energyInner,
      ← integral_add ((f.mulSmooth χ hχ).integrable_mul _) ((f.mulSmooth χ hχ).integrable_gradient _),
      ← integral_add (f.integrable_mul f) (f.integrable_gradient f), ← integral_const_mul]
    exact integral_mono
      (((f.mulSmooth χ hχ).integrable_mul _).add ((f.mulSmooth χ hχ).integrable_gradient _))
      (((f.integrable_mul f).add (f.integrable_gradient f)).const_mul C) hpoint
  rw [← EnergyTest.norm_sq, ← EnergyTest.norm_sq] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg f))).mp
  simpa only [mul_pow, Real.sq_sqrt hC] using he

def mulSmoothCLM (D : LeviCivitaData g) (Ω : Set M) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hc : HasCompactSupport χ) :
    EnergyTest D Ω →L[ℝ] EnergyTest D Ω :=
  (mulSmoothLinear D Ω χ hχ).mkContinuous
    (exists_mulSmooth_norm_bound (D := D) (Ω := Ω) χ hχ hc).choose
    (exists_mulSmooth_norm_bound (D := D) (Ω := Ω) χ hχ hc).choose_spec.2

@[simp] theorem mulSmoothCLM_apply (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hc : HasCompactSupport χ)
    (f : EnergyTest D Ω) : mulSmoothCLM D Ω χ hχ hc f = f.mulSmooth χ hχ := rfl

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem EnergyTest.sum_mul_partition {ι : Type*} [Fintype ι] {K : Set M}
    (ρ : SmoothPartitionOfUnity ι (𝓡 n) M K) (hΩ : Ω ⊆ K)
    (f : EnergyTest D Ω) :
    ∑ i, f.mulSmooth (ρ i) (ρ i).contMDiff = f := by
  classical
  apply Subtype.ext
  rw [EnergyTest.coe_sum]
  funext x
  simp only [Finset.sum_apply, EnergyTest.mulSmooth_apply, ← Finset.sum_mul]
  by_cases hx : x ∈ K
  · have hsum : ∑ i, ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    rw [hsum, one_mul]
  · have hf : f x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hx (hΩ (f.support_subset hs)))
    simp only [hf, mul_zero]

theorem testToL2_sum_mul_partition {ι : Type*} [Fintype ι] {K : Set M}
    (ρ : SmoothPartitionOfUnity ι (𝓡 n) M K) (hΩ : Ω ⊆ K)
    (f : EnergyTest D Ω) :
    ∑ i, testToL2 D Ω (f.mulSmooth (ρ i) (ρ i).contMDiff) = testToL2 D Ω f := by
  rw [← map_sum, f.sum_mul_partition ρ hΩ]

end PoincareConjecture.LeviCivitaData.Dirichlet
