import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ComponentSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Coefficients


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology
universe u
theorem PoincareConjecture.LeviCivitaData.exists_uniform_weighted_component_slab_bound_with_coefficient
    (m : ℕ) (hm : 1 ≤ m) {ℓ V H C L : ℝ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (N : ℕ) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧
      (∀ r : ℝ, 0 < r → ∀ t ∈ Icc (3 * (ℓ * r) / 64) (15 * (ℓ * r) / 128),
        2 * H / r ≤ α / t) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
        [IsManifold (𝓡 (m + 2)) ∞ M]
        (g : RiemannianMetric (m + 2) M) (D : LeviCivitaData g)
        (f : M → ℝ) (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
        (r : ℝ), 0 < r →
        let a := 3 * (ℓ * r) / 64
        let b := 5 * (ℓ * r) / 64
        let I := Ioo (0 : ℝ) (ℓ * r / 8)
        IsProperMap (I.restrictPreimage f) →
        (∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) →
        ∀ K : M → ℝ, ContinuousOn K (g.regularDomain hf) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2), 0 ≤ K x) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
          ∀ v w : TangentSpace (𝓡 (m + 2)) x, -K x ≤ D.sectionalCurvature x v w) →
        (∀ t ∈ Icc a (3 * b / 2), g.regularLevelArea hf t ≤ V * r ^ (m + 1)) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2), ∀ v : TangentSpace (𝓡 (m + 2)) x,
          D.hessian f x v v ≤ (H / r) * g.inner x v v) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
          1 / 2 ≤ g.tangentNorm x (g.gradient f x) ∧
            g.tangentNorm x (g.gradient f x) ≤ 1) →
        let U := g.regularDomain hf
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
          ⟨finrank_euclideanSpace_fin⟩
        let (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
        letI (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
        (∀ t ∈ Icc a (3 * b / 2),
          Nat.card (ConnectedComponents (openLevelSet f U t)) ≤ N) →
        (∀ t ∈ Icc a (3 * b / 2), ∀ p : openLevelSet f U t,
          let gL := RiemannianMetric.regularLevelMetric hf U (g.regularDomain_regular hf) t g
          (∫ z, max 0 ((gL.connectedComponentMetric p).leviCivitaData.scalarCurvature z)
            ∂(gL.connectedComponentMetric p).volumeMeasure) ≤
          C * ((L * r) ^ (m - 1) + ∫ z, D.levelSectionalError f K (α / t)
            (openLevelIncl f U t z) ∂(gL.connectedComponentMetric p).volumeMeasure)) →
        (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
          B * (r ^ m + ∫ x in f ⁻¹' Icc a (3 * b / 2), K x ∂g.volumeMeasure) := by
  obtain ⟨α, hα, hαspeed, hαbounds⟩ :=
    Poincare.CurvatureIntegral.exists_uniform_slab_coefficient (m + 1) hℓ hℓ1 hV hH
  let Q := α * C + ((m + 2 : ℕ) : ℝ) ^ 2
  let P := α * C * (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
    ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3)
  let T := 3 * α * C * (N : ℝ) * L ^ (m - 1) + 2 * P + 4 * α
  let B := 1 + 2 * Q + T
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨α, B, hα, by dsimp [B]; positivity,
    fun r hr t ht => (hαbounds r hr t ht).2, ?_⟩
  intro M _ _ _ _ _ _ g D f hf r hr
  dsimp only
  let a := 3 * (ℓ * r) / 64
  let b := 5 * (ℓ * r) / 64
  let I := Ioo (0 : ℝ) (ℓ * r / 8)
  intro hproper hreg K hKc hK hsec harea hhess hspeed
  let U := g.regularDomain hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  let (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
  let (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
  intro hcount hind
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a, b]; nlinarith [mul_pos hℓ hr]
  have hslab : Icc a (3 * b / 2) ⊆ I := by
    intro t ht
    change 0 < t ∧ t < ℓ * r / 8
    dsimp [a, b] at ht
    constructor <;> nlinarith [mul_pos hℓ hr, ht.1, ht.2]
  have hparameter (t : ℝ) (ht : t ∈ Icc a (3 * b / 2)) :
      V * r ^ (m + 1) ≤ α * t ^ (m + 1) ∧ 2 * H / r ≤ α / t := by
    apply hαbounds r hr t
    constructor
    · exact ht.1
    · dsimp [a, b] at ht
      linarith [ht.2]
  have hnormH (t : ℝ) (ht : t ∈ Icc a (3 * b / 2)) (x : M) (hfx : f x = t)
      (v : TangentSpace (𝓡 (m + 2)) x) :
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤
        (α / t) * g.inner x v v := by
    have hx : x ∈ f ⁻¹' Icc a (3 * b / 2) := by simpa only [mem_preimage, hfx] using ht
    have hs : 1 / 2 ≤ Real.sqrt (D.levelQ f x) := (hspeed x hx).1
    have hspos : 0 < Real.sqrt (D.levelQ f x) := lt_of_lt_of_le (by norm_num) hs
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 2)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hinner : 0 ≤ g.inner x v v := by
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg
    have hbnd : (H / r) * g.inner x v v ≤
        ((2 * H / r) * g.inner x v v) * Real.sqrt (D.levelQ f x) := by
      have hh := mul_le_mul_of_nonneg_left hs
        (by positivity : 0 ≤ (2 * H / r) * g.inner x v v)
      calc
        _ = (2 * H / r * g.inner x v v) * (1 / 2) := by ring
        _ ≤ _ := hh
    calc
      _ ≤ ((H / r) * g.inner x v v) / Real.sqrt (D.levelQ f x) :=
        div_le_div_of_nonneg_right (hhess x hx v) hspos.le
      _ ≤ (2 * H / r) * g.inner x v v := (div_le_iff₀ hspos).mpr hbnd
      _ ≤ _ := mul_le_mul_of_nonneg_right (hparameter t ht).2 hinner
  have hbound := D.integral_scalarCurvature_posPart_inner_slab_le_of_component_induction
    hf isOpen_Ioo hproper hreg ha hab (by omega) hα hC
    (pow_nonneg (mul_nonneg hL hr.le) _) N hslab hKc hK hsec
    (fun t ht => (harea t ht).trans (hparameter t ht).1)
    (fun t ht x hfx v _ => hnormH t ht x hfx v)
    (fun x hx => ⟨hαspeed.trans (hspeed x hx).1, (hspeed x hx).2⟩)
    hcount hind
  have hbr : 3 * b / 2 ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hℓ1 hr.le
    dsimp [b]
    nlinarith
  have herr := Poincare.CurvatureIntegral.scaled_component_slab_remainder_le
    hm hα.le hC hL hP (by dsimp [b]; positivity) hbr N
  let J := ∫ x in f ⁻¹' Icc a (3 * b / 2), K x ∂g.volumeMeasure
  have hJ : 0 ≤ J := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem ((isClosed_Icc.preimage hf.continuous).measurableSet)] with x hx
    exact hK x hx
  have hrpow : 0 ≤ r ^ m := pow_nonneg hr.le m
  change _ ≤ B * (r ^ m + J)
  change _ ≤ 2 * Q * J + 3 * α * C * ((N : ℝ) * (L * r) ^ (m - 1)) * b +
    2 * P * (3 * b / 2) ^ m + 4 * α * b ^ m at hbound
  change _ ≤ T * r ^ m at herr
  calc
    _ ≤ 2 * Q * J + T * r ^ m := by linarith only [hbound, herr]
    _ ≤ B * (r ^ m + J) := by
      dsimp [B]
      nlinarith [mul_nonneg hT hJ, mul_nonneg hQ hrpow]


theorem PoincareConjecture.LeviCivitaData.exists_uniform_weighted_component_slab_bound
    (m : ℕ) (hm : 1 ≤ m) {ℓ V H C L : ℝ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (N : ℕ) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
        [IsManifold (𝓡 (m + 2)) ∞ M]
        (g : RiemannianMetric (m + 2) M) (D : LeviCivitaData g)
        (f : M → ℝ) (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
        (r : ℝ), 0 < r →
        let a := 3 * (ℓ * r) / 64
        let b := 5 * (ℓ * r) / 64
        let I := Ioo (0 : ℝ) (ℓ * r / 8)
        IsProperMap (I.restrictPreimage f) →
        (∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) →
        ∀ K : M → ℝ, ContinuousOn K (g.regularDomain hf) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2), 0 ≤ K x) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
          ∀ v w : TangentSpace (𝓡 (m + 2)) x, -K x ≤ D.sectionalCurvature x v w) →
        (∀ t ∈ Icc a (3 * b / 2), g.regularLevelArea hf t ≤ V * r ^ (m + 1)) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2), ∀ v : TangentSpace (𝓡 (m + 2)) x,
          D.hessian f x v v ≤ (H / r) * g.inner x v v) →
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
          1 / 2 ≤ g.tangentNorm x (g.gradient f x) ∧
            g.tangentNorm x (g.gradient f x) ≤ 1) →
        let U := g.regularDomain hf
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
          ⟨finrank_euclideanSpace_fin⟩
        let (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
        letI (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
        (∀ t ∈ Icc a (3 * b / 2),
          Nat.card (ConnectedComponents (openLevelSet f U t)) ≤ N) →
        (∀ t ∈ Icc a (3 * b / 2), ∀ p : openLevelSet f U t,
          let gL := RiemannianMetric.regularLevelMetric hf U (g.regularDomain_regular hf) t g
          (∫ z, max 0 ((gL.connectedComponentMetric p).leviCivitaData.scalarCurvature z)
            ∂(gL.connectedComponentMetric p).volumeMeasure) ≤
          C * ((L * r) ^ (m - 1) + ∫ z, D.levelSectionalError f K (α / t)
            (openLevelIncl f U t z) ∂(gL.connectedComponentMetric p).volumeMeasure)) →
        (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
          B * (r ^ m + ∫ x in f ⁻¹' Icc a (3 * b / 2), K x ∂g.volumeMeasure) := by
  obtain ⟨α, B, hα, hB, _, hbound⟩ :=
    PoincareConjecture.LeviCivitaData.exists_uniform_weighted_component_slab_bound_with_coefficient
      m hm hℓ hℓ1 hV hH hC hL N
  exact ⟨α, B, hα, hB, hbound⟩
