import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.OppositeLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Proper
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.RadialAugmentation
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.DirectionalSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.DirectionalTubeSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ValueTube















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle Topology InnerProductSpace
universe u
namespace PoincareConjecture.RiemannianMetric
private theorem scalar_level_strip_parameters {r τ ε t z : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (hε : ε ≤ r / 65536)
    (ht : t ∈ Icc (7 * r / 12) (9 * r / 10))
    (hz : z ∈ Icc (2 * τ * t - (τ * r / 1024) / 4)
      (2 * τ * t + (τ * r / 1024) / 4)) :
    z ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) ∧
      ∀ d : ℝ, |z - τ * d| ≤ τ * ε → 9 * r / 8 < d ∧ d < 15 * r / 8 := by
  have hτr : 0 < τ * r := mul_pos hτ hr
  have hlo := mul_le_mul_of_nonneg_left ht.1 hτ.le
  have hhi := mul_le_mul_of_nonneg_left ht.2 hτ.le
  have he := mul_le_mul_of_nonneg_left hε hτ.le
  refine ⟨⟨by nlinarith only [hz.1, hlo, hτr], by nlinarith only [hz.2, hhi, hτr]⟩, ?_⟩
  intro d hd
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  constructor
  · apply (mul_lt_mul_iff_right₀ hτ).mp
    nlinarith only [hz.1, hlo, hdhi, he, hτr]
  · apply (mul_lt_mul_iff_right₀ hτ).mp
    nlinarith only [hz.2, hhi, hdlo, he, hτr]

private theorem normalized_opposite_pair_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256)
    (hul : 1 - δ ^ 2 ≤ ‖u‖) (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1 + δ ^ 2) (hsum : ‖u + v‖ ≤ 64 * δ) :
    (1 / 2 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 1 ∧
    (1 / 2 : ℝ) ≤ ‖(1 / (1 + δ ^ 2)) • v‖ ∧
    ‖(1 / (1 + δ ^ 2)) • v‖ ≤ 1 ∧
    inner ℝ u ((1 / (1 + δ ^ 2)) • v) ≤ -1 + 128 * δ := by
  let κ := 1 / (1 + δ ^ 2)
  have hden : 0 < 1 + δ ^ 2 := by positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hn : ‖κ • v‖ = κ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
  have hv1 : ‖κ • v‖ ≤ 1 := by
    rw [hn]
    calc
      _ ≤ κ * (1 + δ ^ 2) := mul_le_mul_of_nonneg_left hv hκ.le
      _ = 1 := by dsimp [κ]; field_simp
  have hsumInner : inner ℝ u (u + v) ≤ 64 * δ := by
    calc
      _ ≤ ‖u‖ * ‖u + v‖ := real_inner_le_norm _ _
      _ ≤ 1 * (64 * δ) := mul_le_mul hu hsum (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hu0 : 0 ≤ 1 - δ ^ 2 := by nlinarith
  have husq : (1 - δ ^ 2) ^ 2 ≤ ‖u‖ ^ 2 :=
    pow_le_pow_left₀ hu0 hul 2
  have huv : inner ℝ u v ≤ -1 + 64 * δ + 2 * δ ^ 2 := by
    rw [inner_add_right, real_inner_self_eq_norm_sq] at hsumInner
    nlinarith [sq_nonneg (δ ^ 2)]
  have hnum : -1 + 64 * δ + 2 * δ ^ 2 ≤
      (-1 + 128 * δ) * (1 + δ ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg δ) hδ.le]
  have hpair : inner ℝ u (κ • v) ≤ -1 + 128 * δ := by
    rw [inner_smul_right]
    change κ * inner ℝ u v ≤ _
    calc
      _ ≤ κ * (-1 + 64 * δ + 2 * δ ^ 2) := mul_le_mul_of_nonneg_left huv hκ.le
      _ ≤ κ * ((-1 + 128 * δ) * (1 + δ ^ 2)) :=
        mul_le_mul_of_nonneg_left hnum hκ.le
      _ = -1 + 128 * δ := by dsimp [κ]; field_simp
  have hlow : (1 / 2 : ℝ) ≤ ‖κ • v‖ := by
    have hneg : -inner ℝ u (κ • v) ≤ ‖κ • v‖ := by
      calc
        _ ≤ |inner ℝ u (κ • v)| := neg_le_abs _
        _ ≤ ‖u‖ * ‖κ • v‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖κ • v‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
        _ = _ := one_mul _
    linarith
  exact ⟨by nlinarith, hu, hlow, hv1, hpair⟩

private theorem gradient_real_const_mul
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (c : ℝ) (f : M → ℝ) (x : M) :
    D.gradient (fun y => c * f y) x = c • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient, mvfderiv_const_mul]
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]


private theorem exists_partner_of_prescribed_slab
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r σ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 256)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u) :
    let τ := 1 / (1 + σ ^ 2 / 8)
    let ε₀ := σ ^ 4 * r / 1048576
    let s := τ * r / 1024
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    IsProperMap (I.restrictPreimage u) →
    (∀ x : M, u x ∈ I →
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) →
    (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
      |u x - τ * (g.edist p x).toReal| ≤ τ * ε₀ ∧
      1 - σ ^ 2 ≤ g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      ∀ w : TangentSpace (𝓡 n) x, D.hessian u x w w ≤ (5 / r) * g.inner x w w) →
    letI := g.toMetricSpace
    ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
      IsCompact (u ⁻¹' Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)) ∧
      ∃ v : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v ∧
        let V := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
        (∀ x : M, u x = 2 * τ * t → Metric.closedBall x (s / 16) ⊆ V) ∧
        ∀ x ∈ V,
          r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r ∧
          (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient u x) ∧
          g.tangentNorm x (D.gradient u x) ≤ 1 ∧
          (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient v x) ∧
          g.tangentNorm x (D.gradient v x) ≤ 1 ∧
          g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + 128 * σ ∧
          ∀ w : TangentSpace (𝓡 n) x,
            D.hessian u x w w ≤ (3 / s) * g.inner x w w ∧
            D.hessian v x w w ≤ (3 / s) * g.inner x w w := by
  dsimp only
  let := g.toMetricSpace
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let τ := 1 / (1 + σ ^ 2 / 8)
  let ε₀ := σ ^ 4 * r / 1048576
  let s := τ * r / 1024
  let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
  intro hproper hband hcore t ht
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg σ]
  have hσ4 : σ ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ hσ.le (show σ ≤ 1 by linarith) 4
    norm_num at h
    exact h
  have hε : ε₀ ≤ r / 65536 := by
    have h := mul_le_mul_of_nonneg_right hσ4 hr.le
    dsimp [ε₀]
    linarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hτ1 hr.le
    dsimp [s]
    nlinarith
  have h4s : 4 * s ≤ r / 256 := by
    have h := mul_le_mul_of_nonneg_right hτ1 hr.le
    dsimp [s]
    nlinarith
  have hHs : (5 / r) * s ≤ 1 := by
    have he : (5 / r) * s = 5 * τ / 1024 := by dsimp [s]; field_simp
    rw [he]
    linarith
  let T := u ⁻¹' Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)
  have hTband : Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4) ⊆ I := by
    intro z hz
    exact (scalar_level_strip_parameters hr hτ hε ht hz).1
  have hT : IsCompact T :=
    Poincare.Coarea.isCompact_slab_of_isProperMap hproper hTband
  have hTrange (x : M) (hx : x ∈ T) :
      9 * r / 8 < dist p x ∧ dist p x < 15 * r / 8 := by
    have hxc := hband x (hTband hx)
    exact (scalar_level_strip_parameters hr hτ hε ht hx).2
      ((g.edist p x).toReal) (hcore x hxc.1 hxc.2).1
  have hbuffer (x : M) (hx : x ∈ T) (y : M) (hy : y ∈ Metric.closedBall x (4 * s)) :
      1 - σ ^ 2 ≤ g.tangentNorm y (D.gradient u y) ∧
      g.tangentNorm y (D.gradient u y) ≤ 1 ∧
      ∀ w : TangentSpace (𝓡 n) y,
        D.hessian u y w w ≤ (5 / r) * g.inner y w w := by
    have hxy : dist x y ≤ 4 * s := by
      simpa only [Metric.mem_closedBall, dist_comm] using hy
    have hxc := hTrange x hx
    have hlo : r < (g.edist p y).toReal := by
      change r < dist p y
      have htri := dist_triangle p y x
      rw [dist_comm y x] at htri
      linarith
    have hhi : (g.edist p y).toReal < 2 * r := by
      change dist p y < 2 * r
      have htri := dist_triangle p x y
      linarith
    exact (hcore y hlo hhi).2
  have hgap (x : M) (hx : x ∈ T) :
      s ≤ (2 * τ * t + 3 * s / 2) - u x ∧
        (2 * τ * t + 3 * s / 2) - u x ≤ 2 * s := by
    change u x ∈ Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4) at hx
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨v, hv, hpair⟩ := g.exists_near_opposite_smoothing_of_upper_level D hc hsec hu hT
    hs hs1 hσ (by linarith : σ ≤ 1 / 16) (by positivity : 0 ≤ 5 / r) hHs hgap hbuffer
  let ν := 1 / (1 + σ ^ 2)
  let h := fun x => ν * v x
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hν1 : ν ≤ 1 := by
    dsimp [ν]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg σ]
  have hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h := contMDiff_const.mul hv
  have hH3 : 5 / r ≤ 3 / s := (le_div_iff₀ hs).mpr (by linarith)
  refine ⟨hT, h, hh, ?_, ?_⟩
  · intro x hux y hy
    have hxT : x ∈ T := by
      change u x ∈ Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)
      rw [hux]
      constructor <;> linarith
    have hxy : (g.edist x y).toReal ≤ s / 16 := by
      change dist x y ≤ s / 16
      simpa only [Metric.mem_closedBall, dist_comm] using hy
    have hvalue := g.abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall hc hu x y
      (L := 1) (by
        intro z hz
        exact (hbuffer x hxT z (by
          apply Metric.mem_closedBall.mpr
          have hz' : dist z x ≤ (g.edist x y).toReal := hz
          linarith)).2.1)
    simp only [NNReal.coe_one, one_mul] at hvalue
    have habs := hvalue.trans hxy
    rw [hux] at habs
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    change 2 * τ * t - s / 4 < u y ∧ u y < 2 * τ * t + s / 4
    constructor <;> linarith
  · intro x hx
    have hxT : x ∈ T := ⟨hx.1.le, hx.2.le⟩
    have huall := hbuffer x hxT x (Metric.mem_closedBall.mpr (by simp; positivity))
    have hp := hpair x hxT
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hgrad : D.gradient h x = ν • D.gradient v x := gradient_real_const_mul D ν v x
    have hb := normalized_opposite_pair_bounds
      (D.gradient u x) (D.gradient v x) hσ hσsmall huall.1 huall.2.1 hp.2.1 hp.2.2.2
    have hxcore := hband x (hTband hxT)
    refine ⟨hxcore.1, hxcore.2, ?_⟩
    change (1 / 2 : ℝ) ≤ ‖D.gradient u x‖ ∧ ‖D.gradient u x‖ ≤ 1 ∧
      (1 / 2 : ℝ) ≤ ‖D.gradient h x‖ ∧ ‖D.gradient h x‖ ≤ 1 ∧
      inner ℝ (D.gradient u x) (D.gradient h x) ≤ -1 + 128 * σ ∧ _
    rw [hgrad]
    refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2, ?_⟩
    intro w
    have hw : 0 ≤ g.inner x w w := by
      change 0 ≤ inner ℝ w w
      exact real_inner_self_nonneg
    refine ⟨(huall.2.2 w).trans (mul_le_mul_of_nonneg_right hH3 hw), ?_⟩
    change D.hessian (fun y => ν * v y) x w w ≤ _
    rw [D.hessian_const_mul]
    calc
      _ ≤ ν * ((3 / s) * g.inner x w w) :=
        mul_le_mul_of_nonneg_left (hp.2.2.1 w) hν.le
      _ ≤ 1 * ((3 / s) * g.inner x w w) :=
        mul_le_mul_of_nonneg_right hν1 (mul_nonneg (by positivity) hw)
      _ = _ := one_mul _



theorem exists_directional_slab_with_augmented_level_strainers
    {n k : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) (f h : Fin k → M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    {δold C : ℝ} (hδold : 0 ≤ δold) (hC : 0 ≤ C)
    (hpair : ∀ i x, x ∈ U →
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δold)
    (hhess : ∀ i x, x ∈ U → ∀ v : TangentSpace (𝓡 n) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v ∧
      D.hessian (h i) x v v ≤ C * g.inner x v v)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    {r Δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hΔ : 0 < Δ) (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (hball : ∀ x, g.edist p x ≤ ENNReal.ofReal (4 * r) → x ∈ U) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    (4 * Real.sqrt δold + 2 * C * r + σ ^ 2 / 8 ≤ ε / 2) →
    (∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ ε) →
    (∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ a : ℝ, 0 < a →
        ∃ z : M, (g.edist y z).toReal < a ∧
          (1 - σ ^ 2 / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) →
    letI := g.toMetricSpace
    let τ := 1 / (1 + σ ^ 2 / 8)
    let ε₀ := σ ^ 4 * r / 1048576
    let s := τ * r / 1024
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    ∃ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      IsProperMap (I.restrictPreimage u) ∧
      (∀ x : M, u x ∈ I → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      (∀ x : M, u x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |u x - τ * (g.edist p x).toReal| ≤ τ * ε₀ ∧
        1 - σ ^ 2 ≤ g.tangentNorm x (D.gradient u x) ∧
        g.tangentNorm x (D.gradient u x) ≤ 1 ∧
        (∀ v : TangentSpace (𝓡 n) x,
          D.hessian u x v v ≤ (5 / r) * g.inner x v v) ∧
        ((∀ i, f i x = f i p) → ∀ i,
          |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε / 2 ∧
          |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε / 2)) ∧
      ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
        IsCompact (u ⁻¹' Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)) ∧
        ∃ v : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v ∧
          let V := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
          let S := {x : M | x ∈ V ∧ ∀ i, f i x = f i p}
          let H := max C (3 / s)
          let a := Δ / 4
          let β := a / ((k : ℝ) + 1)
          let F := fun x => (1 - a) * u x + β * ∑ i, h i x
          let G := fun x => (1 - a) * v x + β * ∑ i, h i x
          let f' := Fin.cons F f
          let h' := Fin.cons G h
          (∀ x : M, u x = 2 * τ * t → Metric.closedBall x (s / 16) ⊆ V) ∧
          (∀ x ∈ V,
            r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r ∧
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient u x) ∧
            g.tangentNorm x (D.gradient u x) ≤ 1 ∧
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient v x) ∧
            g.tangentNorm x (D.gradient v x) ≤ 1 ∧
            g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + ε ^ 2 / 8 ∧
            ∀ w : TangentSpace (𝓡 n) x,
              D.hessian u x w w ≤ (3 / s) * g.inner x w w ∧
              D.hessian v x w w ≤ (3 / s) * g.inner x w w) ∧
          (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f' i)) ∧
          (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h' i)) ∧
          (∀ x ∈ S,
            (∀ i,
              (1 - 2 * Δ ≤ g.tangentNorm x (D.gradient (f' i) x) ∧
                g.tangentNorm x (D.gradient (f' i) x) ≤ 1) ∧
              (1 - 2 * Δ ≤ g.tangentNorm x (D.gradient (h' i) x) ∧
                g.tangentNorm x (D.gradient (h' i) x) ≤ 1) ∧
              g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1 + 2 * Δ) ∧
            (∀ i j, i ≠ j →
              |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ Δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ Δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (h' j) x)| ≤ Δ ∧
              g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) ∧
            (∀ i : Fin k,
              g.inner x (D.gradient (f' 0) x) (D.gradient (f' i.succ) x) < 0) ∧
            ∀ w : TangentSpace (𝓡 n) x, ∀ i,
              D.hessian (f' i) x w w ≤ H * g.inner x w w ∧
              D.hessian (h' i) x w w ≤ H * g.inner x w w) ∧
          ∀ x ∈ S, Function.Surjective
            (mfderiv (𝓡 n) 𝓘(ℝ, Fin (k + 1) → ℝ) (fun y i => f' i y) x) := by
  dsimp only
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  intro hbudget holdcross hascent
  let := g.toMetricSpace
  let τ := 1 / (1 + σ ^ 2 / 8)
  let ε₀ := σ ^ 4 * r / 1048576
  let s := τ * r / 1024
  let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hΔ16 : Δ ≤ 1 / 16 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hΔsmall
    nlinarith [mul_nonneg hk hΔ.le]
  have hεΔ : ε ≤ Δ := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < 8 * ((k : ℝ) + 1))).mpr
    nlinarith [mul_nonneg hk hΔ.le]
  have hε1 : ε ≤ 1 := by linarith
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσsmall : σ ≤ 1 / 256 := by
    have he2 : ε ^ 2 ≤ 1 := by nlinarith
    dsimp [σ]
    linarith
  have hσ2 : σ ^ 2 ≤ 1 / 4 := by nlinarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg σ]
  have hs : 0 < s := by dsimp [s]; positivity
  have hδoldε : δold ≤ ε := by
    have hsq := Real.sq_sqrt hδold
    have hsqnonneg := Real.sqrt_nonneg δold
    have hCr := mul_nonneg hC hr.le
    have hroot : Real.sqrt δold ≤ ε / 8 := by
      nlinarith [sq_nonneg σ]
    nlinarith [sq_nonneg (ε - Real.sqrt δold)]
  obtain ⟨u, hu, hproper, hreg, hband, hcore₀⟩ :=
    g.exists_proper_regular_slab_with_near_unit_gradient_and_common_level_constraints
      D hc hsec p f h hU hf hh hδold hC hpair hhess
      hr hr1 (sq_pos_of_pos hσ) hσ2 hball hascent
  have hεeq : (σ ^ 2) ^ 2 * r / 1048576 = ε₀ := by dsimp [ε₀]; ring
  have hcore (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      |u x - τ * (g.edist p x).toReal| ≤ τ * ε₀ ∧
      1 - σ ^ 2 ≤ g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      (∀ w : TangentSpace (𝓡 n) x,
        D.hessian u x w w ≤ (5 / r) * g.inner x w w) ∧
      ((∀ i, f i x = f i p) → ∀ i,
        |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε / 2 ∧
        |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε / 2) := by
    have hb := hcore₀ x hx hx'
    rw [hεeq] at hb
    refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
    intro hlevel i
    have hcross := hb.2.2.2.2 hlevel i
    have hBnonneg : 0 ≤ 4 * Real.sqrt δold + 2 * C * r + σ ^ 2 / 8 := by positivity
    have hB : τ * (4 * Real.sqrt δold + 2 * C * r + σ ^ 2 / 8) ≤ ε / 2 :=
      (mul_le_mul_of_nonneg_right hτ1 hBnonneg).trans (by simpa only [one_mul] using hbudget)
    exact ⟨hcross.1.trans hB, hcross.2.trans hB⟩
  refine ⟨u, hu, hproper, hreg, hband, hcore, ?_⟩
  intro t ht
  obtain ⟨hcompact, v, hv, hbuffer, hb₀⟩ :=
    exists_partner_of_prescribed_slab g D hc hsec p hr hr1 hσ hσsmall hu
      hproper hband
      (fun x hx hx' => ⟨(hcore x hx hx').1, (hcore x hx hx').2.1,
        (hcore x hx hx').2.2.1, (hcore x hx hx').2.2.2.1⟩) t ht
  let V := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
  let S := {x : M | x ∈ V ∧ ∀ i, f i x = f i p}
  let H := max C (3 / s)
  have hb (x : M) (hx : x ∈ V) :
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r ∧
      (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient v x) ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + ε ^ 2 / 8 ∧
      ∀ w : TangentSpace (𝓡 n) x,
        D.hessian u x w w ≤ (3 / s) * g.inner x w w ∧
        D.hessian v x w w ≤ (3 / s) * g.inner x w w := by
    obtain ⟨hlo, hhi, hul, huu, hvl, hvu, hop, hhes⟩ := hb₀ x hx
    refine ⟨hlo, hhi, hul, huu, hvl, hvu, ?_, hhes⟩
    dsimp [σ] at hop
    linarith [sq_nonneg ε]
  have hxU (x : M) (hx : x ∈ S) : x ∈ U := by
    apply hball
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top p x)]
    apply ENNReal.ofReal_le_ofReal
    have hhi := (hb x hx.1).2.1
    linarith
  have hH : 0 ≤ H := hC.trans (le_max_left _ _)
  have hunit : ∀ x ∈ S,
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      ∀ i, g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
        g.tangentNorm x (D.gradient (h i) x) ≤ 1 := by
    intro x hx
    obtain ⟨_, _, _, huu, _, hvu, _, _⟩ := hb x hx.1
    exact ⟨huu, hvu, fun i => ⟨(hpair i x (hxU x hx)).1,
      (hpair i x (hxU x hx)).2.1⟩⟩
  have hHess : ∀ x ∈ S, ∀ w : TangentSpace (𝓡 n) x,
      D.hessian u x w w ≤ H * g.inner x w w ∧
      D.hessian v x w w ≤ H * g.inner x w w ∧
      ∀ i, D.hessian (f i) x w w ≤ H * g.inner x w w ∧
        D.hessian (h i) x w w ≤ H * g.inner x w w := by
    intro x hx w
    have hw : 0 ≤ g.inner x w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (g.pos x w hw).le
    obtain ⟨_, _, _, _, _, _, _, hhes⟩ := hb x hx.1
    exact ⟨(hhes w).1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw),
      (hhes w).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw),
      fun i => ⟨(hhess i x (hxU x hx) w).1.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw),
        (hhess i x (hxU x hx) w).2.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)⟩⟩
  have haug := D.augmented_strainer_pair_full_bounds_of_radial_cross f h u v hf hh hu hv
    hΔ hΔsmall hH hunit (fun x hx => htight x (hxU x hx)) hHess
    (fun x hx => ⟨(hb x hx.1).2.2.2.2.2.2.1, fun i =>
      (hpair i x (hxU x hx)).2.2.trans (by linarith)⟩)
    (fun x hx i j hij => ⟨(holdcross x (hxU x hx) i j hij).1,
      (holdcross x (hxU x hx) i j hij).2.1⟩)
    (fun x hx i j hij => (holdcross x (hxU x hx) i j hij).2.2)
    (fun x hx => (hcore x (hb x hx.1).1 (hb x hx.1).2.1).2.2.2.2 hx.2)
  exact ⟨hcompact, v, hv, hbuffer, hb, haug⟩




theorem exists_directional_slab_with_augmented_level_strainers_in_value_tube
    {n k : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) (f h : Fin k → M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    {δold C q : ℝ} (hδold : 0 ≤ δold) (hC : 0 ≤ C) (hq : 0 < q)
    (hpair : ∀ i x, x ∈ U →
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δold)
    (hhess : ∀ i x, x ∈ U → ∀ v : TangentSpace (𝓡 n) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v ∧
      D.hessian (h i) x v v ≤ C * g.inner x v v)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    {r Δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hΔ : 0 < Δ) (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (hball : ∀ x, g.edist p x ≤ ENNReal.ofReal (4 * r) → x ∈ U) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    (4 * Real.sqrt δold + 3 * q / r + 2 * C * r + σ ^ 2 / 8 ≤ ε / 2) →
    (∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ ε) →
    (∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ a : ℝ, 0 < a →
        ∃ z : M, (g.edist y z).toReal < a ∧
          (1 - σ ^ 2 / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) →
    letI := g.toMetricSpace
    let τ := 1 / (1 + σ ^ 2 / 8)
    let ε₀ := σ ^ 4 * r / 1048576
    let s := τ * r / 1024
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    ∃ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      IsProperMap (I.restrictPreimage u) ∧
      (∀ x : M, u x ∈ I → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      (∀ x : M, u x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |u x - τ * (g.edist p x).toReal| ≤ τ * ε₀ ∧
        1 - σ ^ 2 ≤ g.tangentNorm x (D.gradient u x) ∧
        g.tangentNorm x (D.gradient u x) ≤ 1 ∧
        (∀ v : TangentSpace (𝓡 n) x,
          D.hessian u x v v ≤ (5 / r) * g.inner x v v) ∧
        ((∀ i, |f i x - f i p| ≤ q) → ∀ i,
          |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε / 2 ∧
          |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε / 2)) ∧
      ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
        IsCompact (u ⁻¹' Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)) ∧
        ∃ v : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v ∧
          let V := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
          let S := {x : M | x ∈ V ∧ ∀ i, |f i x - f i p| < q}
          let H := max C (3 / s)
          let a := Δ / 4
          let β := a / ((k : ℝ) + 1)
          let F := fun x => (1 - a) * u x + β * ∑ i, h i x
          let G := fun x => (1 - a) * v x + β * ∑ i, h i x
          let f' := Fin.cons F f
          let h' := Fin.cons G h
          IsOpen S ∧
          (∀ x : M, u x = 2 * τ * t → (∀ i, f i x = f i p) →
            Metric.closedBall x (min (s / 16) (q / 2)) ⊆ S) ∧
          (∀ x : M, u x = 2 * τ * t → Metric.closedBall x (s / 16) ⊆ V) ∧
          (∀ x ∈ V,
            r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r ∧
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient u x) ∧
            g.tangentNorm x (D.gradient u x) ≤ 1 ∧
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient v x) ∧
            g.tangentNorm x (D.gradient v x) ≤ 1 ∧
            g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + ε ^ 2 / 8 ∧
            ∀ w : TangentSpace (𝓡 n) x,
              D.hessian u x w w ≤ (3 / s) * g.inner x w w ∧
              D.hessian v x w w ≤ (3 / s) * g.inner x w w) ∧
          (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f' i)) ∧
          (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h' i)) ∧
          (∀ x ∈ S,
            (∀ i,
              (1 - 2 * Δ ≤ g.tangentNorm x (D.gradient (f' i) x) ∧
                g.tangentNorm x (D.gradient (f' i) x) ≤ 1) ∧
              (1 - 2 * Δ ≤ g.tangentNorm x (D.gradient (h' i) x) ∧
                g.tangentNorm x (D.gradient (h' i) x) ≤ 1) ∧
              g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1 + 2 * Δ) ∧
            (∀ i j, i ≠ j →
              |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ Δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ Δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (h' j) x)| ≤ Δ ∧
              g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) ∧
            (∀ i : Fin k,
              g.inner x (D.gradient (f' 0) x) (D.gradient (f' i.succ) x) < 0) ∧
            ∀ w : TangentSpace (𝓡 n) x, ∀ i,
              D.hessian (f' i) x w w ≤ H * g.inner x w w ∧
              D.hessian (h' i) x w w ≤ H * g.inner x w w) ∧
          ∀ x ∈ S, Function.Surjective
            (mfderiv (𝓡 n) 𝓘(ℝ, Fin (k + 1) → ℝ) (fun y i => f' i y) x) := by
  dsimp only
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  intro hbudget holdcross hascent
  let := g.toMetricSpace
  let τ := 1 / (1 + σ ^ 2 / 8)
  let ε₀ := σ ^ 4 * r / 1048576
  let s := τ * r / 1024
  let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hΔ16 : Δ ≤ 1 / 16 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hΔsmall
    nlinarith [mul_nonneg hk hΔ.le]
  have hεΔ : ε ≤ Δ := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < 8 * ((k : ℝ) + 1))).mpr
    nlinarith [mul_nonneg hk hΔ.le]
  have hε1 : ε ≤ 1 := by linarith
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσsmall : σ ≤ 1 / 256 := by
    have he2 : ε ^ 2 ≤ 1 := by nlinarith
    dsimp [σ]
    linarith
  have hσ2 : σ ^ 2 ≤ 1 / 4 := by nlinarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg σ]
  have hs : 0 < s := by dsimp [s]; positivity
  have hδoldε : δold ≤ ε := by
    have hsq := Real.sq_sqrt hδold
    have hsqnonneg := Real.sqrt_nonneg δold
    have hCr := mul_nonneg hC hr.le
    have hqnonneg : 0 ≤ 3 * q / r := by positivity
    have hroot : Real.sqrt δold ≤ ε / 8 := by
      nlinarith [sq_nonneg σ]
    nlinarith [sq_nonneg (ε - Real.sqrt δold)]
  obtain ⟨u, hu, hproper, hreg, hband, hcore₀⟩ :=
    g.exists_proper_regular_slab_with_near_unit_gradient_and_value_tube_constraints
      D hc hsec p f h hU hf hh hδold hC hq.le hpair hhess
      hr hr1 (sq_pos_of_pos hσ) hσ2 hball hascent
  have hεeq : (σ ^ 2) ^ 2 * r / 1048576 = ε₀ := by dsimp [ε₀]; ring
  have hcore (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      |u x - τ * (g.edist p x).toReal| ≤ τ * ε₀ ∧
      1 - σ ^ 2 ≤ g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      (∀ w : TangentSpace (𝓡 n) x,
        D.hessian u x w w ≤ (5 / r) * g.inner x w w) ∧
      ((∀ i, |f i x - f i p| ≤ q) → ∀ i,
        |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε / 2 ∧
        |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε / 2) := by
    have hb := hcore₀ x hx hx'
    rw [hεeq] at hb
    refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
    intro hlevel i
    have hcross := hb.2.2.2.2 hlevel i
    have hBnonneg : 0 ≤ 4 * Real.sqrt δold + 3 * q / r + 2 * C * r + σ ^ 2 / 8 := by positivity
    have hB : τ * (4 * Real.sqrt δold + 3 * q / r + 2 * C * r + σ ^ 2 / 8) ≤ ε / 2 :=
      (mul_le_mul_of_nonneg_right hτ1 hBnonneg).trans (by simpa only [one_mul] using hbudget)
    exact ⟨hcross.1.trans hB, hcross.2.trans hB⟩
  refine ⟨u, hu, hproper, hreg, hband, hcore, ?_⟩
  intro t ht
  obtain ⟨hcompact, v, hv, hbuffer, hb₀⟩ :=
    exists_partner_of_prescribed_slab g D hc hsec p hr hr1 hσ hσsmall hu
      hproper hband
      (fun x hx hx' => ⟨(hcore x hx hx').1, (hcore x hx hx').2.1,
        (hcore x hx hx').2.2.1, (hcore x hx hx').2.2.2.1⟩) t ht
  let V := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
  let S := {x : M | x ∈ V ∧ ∀ i, |f i x - f i p| < q}
  let H := max C (3 / s)
  have hb (x : M) (hx : x ∈ V) :
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r ∧
      (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient v x) ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + ε ^ 2 / 8 ∧
      ∀ w : TangentSpace (𝓡 n) x,
        D.hessian u x w w ≤ (3 / s) * g.inner x w w ∧
        D.hessian v x w w ≤ (3 / s) * g.inner x w w := by
    obtain ⟨hlo, hhi, hul, huu, hvl, hvu, hop, hhes⟩ := hb₀ x hx
    refine ⟨hlo, hhi, hul, huu, hvl, hvu, ?_, hhes⟩
    dsimp [σ] at hop
    linarith [sq_nonneg ε]
  have hxU (x : M) (hx : x ∈ S) : x ∈ U := by
    apply hball
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top p x)]
    apply ENNReal.ofReal_le_ofReal
    have hhi := (hb x hx.1).2.1
    linarith
  have hH : 0 ≤ H := hC.trans (le_max_left _ _)
  have hunit : ∀ x ∈ S,
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      ∀ i, g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
        g.tangentNorm x (D.gradient (h i) x) ≤ 1 := by
    intro x hx
    obtain ⟨_, _, _, huu, _, hvu, _, _⟩ := hb x hx.1
    exact ⟨huu, hvu, fun i => ⟨(hpair i x (hxU x hx)).1,
      (hpair i x (hxU x hx)).2.1⟩⟩
  have hHess : ∀ x ∈ S, ∀ w : TangentSpace (𝓡 n) x,
      D.hessian u x w w ≤ H * g.inner x w w ∧
      D.hessian v x w w ≤ H * g.inner x w w ∧
      ∀ i, D.hessian (f i) x w w ≤ H * g.inner x w w ∧
        D.hessian (h i) x w w ≤ H * g.inner x w w := by
    intro x hx w
    have hw : 0 ≤ g.inner x w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (g.pos x w hw).le
    obtain ⟨_, _, _, _, _, _, _, hhes⟩ := hb x hx.1
    exact ⟨(hhes w).1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw),
      (hhes w).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw),
      fun i => ⟨(hhess i x (hxU x hx) w).1.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw),
        (hhess i x (hxU x hx) w).2.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)⟩⟩
  have haug := D.augmented_strainer_pair_full_bounds_of_radial_cross f h u v hf hh hu hv
    hΔ hΔsmall hH hunit (fun x hx => htight x (hxU x hx)) hHess
    (fun x hx => ⟨(hb x hx.1).2.2.2.2.2.2.1, fun i =>
      (hpair i x (hxU x hx)).2.2.trans (by linarith)⟩)
    (fun x hx i j hij => ⟨(holdcross x (hxU x hx) i j hij).1,
      (holdcross x (hxU x hx) i j hij).2.1⟩)
    (fun x hx i j hij => (holdcross x (hxU x hx) i j hij).2.2)
    (fun x hx => (hcore x (hb x hx.1).1 (hb x hx.1).2.1).2.2.2.2 (fun i => (hx.2 i).le))
  have hopenS : IsOpen S := by
    have ho : IsOpen {x : M | ∀ i, |f i x - f i p| < q} := by
      simpa only [ofPred_forall, Pi.sub_apply] using isOpen_iInter_of_finite (fun i =>
        isOpen_lt (((hf i).continuous.sub continuous_const).abs) continuous_const)
    exact (hu.continuous.isOpen_preimage _ isOpen_Ioo).inter ho
  have hqsmall : q ≤ r := by
    have hqr : 3 * q / r ≤ ε / 2 := by
      have hCr := mul_nonneg hC hr.le
      nlinarith [Real.sqrt_nonneg δold, sq_nonneg σ]
    have hm := (div_le_iff₀ hr).mp hqr
    nlinarith [mul_le_mul_of_nonneg_right hε1 hr.le]
  have hbufferS (x : M) (hux : u x = 2 * τ * t)
      (hlevel : ∀ i, f i x = f i p) :
      Metric.closedBall x (min (s / 16) (q / 2)) ⊆ S := by
    have hxV : x ∈ V := by
      change 2 * τ * t - s / 4 < u x ∧ u x < 2 * τ * t + s / 4
      rw [hux]
      constructor <;> linarith
    have hxcore := hb x hxV
    have hgap := g.value_gap_le_of_mem_closedBall_common_level hc f hf p x
      (q := q / 2) (R := 4 * r) (by positivity) hlevel
      (by linarith [hxcore.2.1])
      (fun i z hz => (hpair i z (hball z hz)).1)
    intro y hy
    have hxy : dist x y ≤ min (s / 16) (q / 2) := by
      simpa only [Metric.mem_closedBall, dist_comm] using hy
    refine ⟨hbuffer x hux (by
      apply Metric.mem_closedBall.mpr
      simpa only [dist_comm] using hxy.trans (min_le_left _ _)), ?_⟩
    have he : g.edist x y ≤ ENNReal.ofReal (q / 2) := by
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top x y)]
      exact ENNReal.ofReal_le_ofReal (hxy.trans (min_le_right _ _))
    intro i
    exact (hgap y he i).trans_lt (by linarith)
  exact ⟨hcompact, v, hv, hopenS, hbufferS, hbuffer, hb, haug⟩

end PoincareConjecture.RiemannianMetric
