import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.AugmentedRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.OppositeValue
import PoincareConjecture.Proofs.Horizon.Topology.Maps.ProperRestriction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology BigOperators

namespace Poincare.CurvatureIntegral

theorem tilted_slab_margin_of_strainer_budget {k : ℕ} {Δ δ C q r : ℝ}
    (hΔ : 0 < Δ) (hsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hr : 0 < r) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    let τ := 1 / (1 + σ ^ 2 / 8)
    4 * Real.sqrt δ + 3 * q / r + 2 * C * r + σ ^ 2 / 8 ≤ ε / 2 →
      0 ≤ Δ / 4 ∧ Δ / 4 ≤ 1 / 64 ∧ 0 < τ * r / 1024 ∧
      4 * (Δ / 4) * Real.sqrt δ * r ≤ (τ * r / 1024) / 12 := by
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  let τ := 1 / (1 + σ ^ 2 / 8)
  change 4 * Real.sqrt δ + 3 * q / r + 2 * C * r + σ ^ 2 / 8 ≤ ε / 2 → _
  intro hbudget
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hΔ16 : Δ ≤ 1 / 16 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hsmall
    nlinarith [mul_nonneg hk hΔ.le]
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεeq : ε * (8 * ((k : ℝ) + 1)) = Δ := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hε128 : ε ≤ 1 / 128 := by nlinarith [mul_nonneg hε hk]
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := by
    dsimp [σ]
    nlinarith
  have hτ : 3 / 4 ≤ τ := by
    change 3 / 4 ≤ 1 / (1 + σ ^ 2 / 8)
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hother₁ : 0 ≤ 3 * q / r := by positivity
  have hother₂ : 0 ≤ 2 * C * r := by positivity
  have hroot : Real.sqrt δ ≤ 1 / 1024 := by
    nlinarith [sq_nonneg σ]
  have hprod : Δ * Real.sqrt δ ≤ 1 / 16384 := by
    nlinarith [mul_le_mul hΔ16 hroot (Real.sqrt_nonneg δ) (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  refine ⟨by positivity, by linarith, by nlinarith, ?_⟩
  have hp := mul_le_mul_of_nonneg_right hprod hr.le
  have ht := mul_le_mul_of_nonneg_right hτ hr.le
  nlinarith
end Poincare.CurvatureIntegral

namespace Poincare.CurvatureIntegral
theorem normalized_level_strip_subset_slab {r τ t : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (ht : t ∈ Icc (7 * r / 12) (9 * r / 10)) :
    Icc (2 * τ * t - (τ * r / 1024) / 4)
      (2 * τ * t + (τ * r / 1024) / 4) ⊆
      Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) := by
  intro z hz
  have hlo := mul_le_mul_of_nonneg_left ht.1 hτ.le
  have hhi := mul_le_mul_of_nonneg_left ht.2 hτ.le
  have hτr := mul_pos hτ hr
  constructor <;> nlinarith [hz.1, hz.2]
end Poincare.CurvatureIntegral



theorem PoincareConjecture.LeviCivitaData.proper_regular_tilted_slab_on_openFiber
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 1) + k))) M]
    [IsManifold (𝓡 ((m + 1) + k)) ∞ M]
    {g : PoincareConjecture.RiemannianMetric ((m + 1) + k) M}
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (f h : Fin k → M → ℝ) (u : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (h i))
    (hu : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ u)
    (p : M) {r s q a δ z : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 64) (hδ : 0 ≤ δ)
    (herror : 4 * a * Real.sqrt δ * r ≤ s / 12)
    (hcompact : IsCompact (u ⁻¹' Icc (z - s / 4) (z + s / 4)))
    (hball : ∀ x, u x ∈ Icc (z - s / 4) (z + s / 4) →
      (g.edist p x).toReal < 2 * r)
    (hpair : ∀ i x, g.edist p x ≤ ENNReal.ofReal (2 * r) →
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δ)
    (haug : ∀ x, u x ∈ Ioo (z - s / 4) (z + s / 4) →
      (∀ i, |f i x - f i p| < q) →
      Function.Surjective (mfderiv (𝓡 ((m + 1) + k))
        𝓘(ℝ, Fin (k + 1) → ℝ)
        (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ)
          ((1 - a) * u y + (a / ((k : ℝ) + 1)) * ∑ i, h i y)
          (fun i => f i y)) x)) :
    let β := a / ((k : ℝ) + 1)
    let F := fun y => (1 - a) * u y + β * ∑ i, h i y
    let b := (1 - a) * z + β * ∑ i, h i p
    let J := Ioo (b - s / 16) (b + s / 16)
    let S := {x | u x ∈ Ioo (z - s / 4) (z + s / 4) ∧
      ∀ i, |f i x - f i p| < q}
    ∃ (hS : IsOpen S)
      (hreg : ∀ x ∈ S, Function.Surjective (mfderiv (𝓡 ((m + 1) + k))
        𝓘(ℝ, Fin k → ℝ) (fun y i => f i y) x)),
      let U : TopologicalSpace.Opens M := ⟨S, hS⟩
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
        (m + 1) + k) := ⟨by simp⟩
      letI := Poincare.Geometry.Manifold.RegularFiber.openFiberChartedSpace
        (m := m + 1) (contMDiff_pi_space.mpr hf) U hreg (fun i => f i p)
      let incl := Poincare.Geometry.Manifold.RegularFiber.openFiberIncl
        (fun y i => f i y) U (fun i => f i p)
      ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (F ∘ incl) ∧
      IsProperMap (J.restrictPreimage (F ∘ incl)) ∧
      (∀ x, mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (F ∘ incl) x ≠ 0) ∧
      ∀ x, F (incl x) ∈ J →
        z - s / 6 < u (incl x) ∧ u (incl x) < z + s / 6 := by
  classical
  let β := a / ((k : ℝ) + 1)
  let F := fun y => (1 - a) * u y + β * ∑ i, h i y
  let b := (1 - a) * z + β * ∑ i, h i p
  let J := Ioo (b - s / 16) (b + s / 16)
  let S := {x | u x ∈ Ioo (z - s / 4) (z + s / 4) ∧
    ∀ i, |f i x - f i p| < q}
  let f₀ := fun y i => f i y
  have hf₀ : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f₀ :=
    contMDiff_pi_space.mpr hf
  have hF : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ F :=
    (contMDiff_const.mul hu).add (contMDiff_const.mul (ContMDiff.sum (fun i _ => hh i)))
  have hS : IsOpen S := by
    apply (isOpen_Ioo.preimage hu.continuous).inter
    have ht : IsOpen (⋂ i, {x | |f i x - f i p| < q}) :=
      isOpen_iInter_of_finite (fun i =>
        isOpen_lt (((hf i).continuous.sub continuous_const).abs) continuous_const)
    convert ht using 1
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  have hreg : ∀ x ∈ S, Surjective
      (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) f₀ x) := by
    intro x hx
    exact surjective_mfderiv_of_surjective_cons hf₀ hF x (haug x hx.1 hx.2)
  refine ⟨hS, hreg, ?_⟩
  let U : Opens M := ⟨S, hS⟩
  let c := fun i => f i p
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m + 1) hf₀ U hreg c
  let L := openFiber f₀ U c
  let incl : L → M := openFiberIncl f₀ U c
  change ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (F ∘ incl) ∧
    IsProperMap (J.restrictPreimage (F ∘ incl)) ∧
    (∀ x : L, mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (F ∘ incl) x ≠ 0) ∧
    ∀ x : L, F (incl x) ∈ J → z - s / 6 < u (incl x) ∧ u (incl x) < z + s / 6
  have hincl : ContMDiff (𝓡 (m + 1)) (𝓡 ((m + 1) + k)) ∞ incl :=
    contMDiff_openFiberIncl hf₀ U hreg c
  have hgap (x : L) (i : Fin k) : f i (incl x) = f i p := by
    exact congrFun x.2 i
  have hinclS (x : L) : incl x ∈ S := (x : U).2
  have herrorx (x : L) :
      |F (incl x) - (1 - a) * u (incl x) - β * ∑ i, h i p| ≤ s / 12 := by
    have hxstrip := (hinclS x).1
    have hxball := hball (incl x) ⟨hxstrip.1.le, hxstrip.2.le⟩
    have he := D.abs_centered_strainer_tilt_error_le hc f h u hf hh p (incl x)
      hδ (q := 0) (by norm_num) ha (fun i y hy => ?_) (fun i => by simp [hgap x i])
    · change |F (incl x) - (1 - a) * u (incl x) - β * ∑ i, h i p| ≤ _ at he
      calc
        _ ≤ a * (2 * Real.sqrt δ * (g.edist p (incl x)).toReal + 0) := he
        _ ≤ 4 * a * Real.sqrt δ * r := by
          nlinarith [mul_nonneg ha (Real.sqrt_nonneg δ),
            mul_le_mul_of_nonneg_left hxball.le (mul_nonneg ha (Real.sqrt_nonneg δ))]
        _ ≤ s / 12 := herror
    · apply hpair i y
      apply hy.trans
      apply (ENNReal.toReal_le_toReal (g.edist_ne_top p (incl x)) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * r)]
      exact hxball.le
  have hinner (x : L) (hx : F (incl x) ∈ J) :
      z - s / 6 < u (incl x) ∧ u (incl x) < z + s / 6 := by
    obtain ⟨he₁, he₂⟩ := abs_le.mp (herrorx x)
    have hx₁ : b - s / 16 < F (incl x) := hx.1
    have hx₂ : F (incl x) < b + s / 16 := hx.2
    dsimp only [b] at hx₁ hx₂
    have ha1 : 0 < 1 - a := by linarith
    have has : a * s ≤ s / 64 := by nlinarith
    constructor
    · by_contra! hn
      have hm := mul_le_mul_of_nonneg_left hn ha1.le
      nlinarith
    · by_contra! hn
      have hm := mul_le_mul_of_nonneg_left hn ha1.le
      nlinarith
  let K := {x : M | u x ∈ Icc (z - s / 6) (z + s / 6) ∧ f₀ x = c}
  have hK : IsCompact K := by
    apply hcompact.of_isClosed_subset
      ((isClosed_Icc.preimage hu.continuous).inter
        (isClosed_eq hf₀.continuous continuous_const))
    intro x hx
    exact ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  have hKS : K ⊆ S := by
    intro x hx
    refine ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, ?_⟩
    intro i
    have hi : f i x = f i p := congrFun hx.2 i
    simpa [hi] using hq
  have hKimage : incl '' (incl ⁻¹' K) = K := by
    apply Set.Subset.antisymm (image_preimage_subset _ _)
    intro x hx
    refine ⟨⟨⟨x, hKS hx⟩, hx.2⟩, hx, rfl⟩
  have hKL : IsCompact (incl ⁻¹' K) := by
    apply (isEmbedding_openFiberIncl f₀ U c).isCompact_iff.mpr
    rwa [hKimage]
  refine ⟨hF.comp hincl, ?_, ?_, hinner⟩
  · apply Poincare.isProperMap_real_restrictPreimage_of_isCompact
      (hF.continuous.comp hincl.continuous) J hKL
    intro x hx
    exact ⟨⟨(hinner x hx).1.le, (hinner x hx).2.le⟩, x.2⟩
  · intro x
    exact regular_openFiber_restriction_of_surjective_mfderiv_cons hf₀ hF U hreg c x
      (haug (incl x) (hinclS x).1 (hinclS x).2)
