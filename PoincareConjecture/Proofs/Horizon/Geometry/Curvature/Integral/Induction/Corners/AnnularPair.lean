import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.DistancePair










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



theorem exists_annular_slab_with_level_opposite_partners
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ a : ℝ, 0 < a →
        ∃ z : M, (g.edist y z).toReal < a ∧
          (1 - δ ^ 2 / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    letI := g.toMetricSpace
    let τ := 1 / (1 + δ ^ 2 / 8)
    let ε := δ ^ 4 * r / 1048576
    let s := τ * r / 1024
    let I := Ioo (9 * r / 16) (15 * r / 16)
    ∃ F u : M → ℝ,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ x, F x = u x / (2 * τ)) ∧
      IsProperMap (I.restrictPreimage F) ∧
      (∀ x : M, F x ∈ I → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) F x ≠ 0) ∧
      (∀ x : M, F x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |F x - (g.edist p x).toReal / 2| ≤ ε / 2 ∧
        (1 / 4 : ℝ) ≤ g.tangentNorm x (D.gradient F x) ∧
        g.tangentNorm x (D.gradient F x) ≤ 1 ∧
        (∀ v : TangentSpace (𝓡 n) x,
          D.hessian F x v v ≤ (5 / r) * g.inner x v v) ∧
        1 - δ ^ 2 ≤ g.tangentNorm x (D.gradient u x) ∧
        g.tangentNorm x (D.gradient u x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 n) x,
          D.hessian u x v v ≤ (5 / r) * g.inner x v v) ∧
      F ⁻¹' Icc (55 * r / 96) (9 * r / 10) ⊆ g.ball p (2 * r) ∧
      {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
        F ⁻¹' Icc (7 * r / 12) (3 * r / 5) ∧
      ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
        IsCompact (F ⁻¹' {t}) ∧
        ∃ h : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h ∧
          let U := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
          (∀ x : M, F x = t → Metric.closedBall x (s / 16) ⊆ U) ∧
          ∀ x ∈ U,
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient u x) ∧
            g.tangentNorm x (D.gradient u x) ≤ 1 ∧
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient h x) ∧
            g.tangentNorm x (D.gradient h x) ≤ 1 ∧
            g.inner x (D.gradient u x) (D.gradient h x) ≤ -1 + 128 * δ ∧
            ∀ v : TangentSpace (𝓡 n) x,
              D.hessian u x v v ≤ (3 / s) * g.inner x v v ∧
              D.hessian h x v v ≤ (3 / s) * g.inner x v v := by
  classical
  let := g.toMetricSpace
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let τ := 1 / (1 + δ ^ 2 / 8)
  let ε := δ ^ 4 * r / 1048576
  let s := τ * r / 1024
  let I := Ioo (9 * r / 16) (15 * r / 16)
  let κ := 1 / (2 * τ)
  have hd2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hd4 : δ ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ hδ.le (show δ ≤ 1 by linarith) 4
    norm_num at h
    exact h
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg δ]
  have hτhalf : (1 / 2 : ℝ) ≤ τ := by
    dsimp [τ]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ1 : κ ≤ 1 := by
    dsimp [κ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hκhalf : (1 / 2 : ℝ) ≤ κ := by
    dsimp [κ]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hκτ : κ * τ = 1 / 2 := by dsimp [κ]; field_simp
  have hε : ε ≤ r / 65536 := by
    have h := mul_le_mul_of_nonneg_right hd4 hr.le
    dsimp [ε]
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
  obtain ⟨u, hu, hproperu, hregu, hbandu, hcoreu₀⟩ :=
    g.exists_proper_regular_slab_with_near_unit_gradient D hc hsec p
      hr hr1 (sq_pos_of_pos hδ) hd2 hascent
  have hεeq : (δ ^ 2) ^ 2 * r / 1048576 = ε := by dsimp [ε]; ring
  have hcoreu (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      |u x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
      1 - δ ^ 2 ≤ g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      ∀ v : TangentSpace (𝓡 n) x,
        D.hessian u x v v ≤ (5 / r) * g.inner x v v := by
    simpa only [hεeq] using hcoreu₀ x hx hx'
  let F := fun x => κ * u x
  have hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F := contMDiff_const.mul hu
  have hnorm (x : M) :
      g.tangentNorm x (D.gradient F x) = κ * g.tangentNorm x (D.gradient u x) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    rw [show D.gradient F x = κ • D.gradient u x from gradient_real_const_mul D κ u x]
    change ‖κ • D.gradient u x‖ = κ * ‖D.gradient u x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
  have hleft : κ * (τ * (9 * r / 8)) = 9 * r / 16 := by
    rw [← mul_assoc, hκτ]
    ring
  have hright : κ * (τ * (15 * r / 8)) = 15 * r / 16 := by
    rw [← mul_assoc, hκτ]
    ring
  have hinterval (x : ℝ) :
      x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) ↔ κ * x ∈ I := by
    dsimp only [I]
    rw [← hleft, ← hright]
    simp only [mem_Ioo, mul_lt_mul_iff_right₀ hκ]
  have hproperF : IsProperMap (I.restrictPreimage F) := by
    let target : Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) ≃ₜ I :=
      (Homeomorph.mulLeft₀ κ hκ.ne').subtype hinterval
    let source : (F ⁻¹' I) ≃ₜ (u ⁻¹' Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))) :=
      (Homeomorph.refl M).subtype (fun x => (hinterval (u x)).symm)
    exact (target.isProperMap.comp hproperu).comp source.isProperMap
  have hbandF (x : M) (hx : F x ∈ I) :
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r :=
    hbandu x ((hinterval (u x)).mpr hx)
  have hcoreF (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      |F x - (g.edist p x).toReal / 2| ≤ ε / 2 ∧
      (1 / 4 : ℝ) ≤ g.tangentNorm x (D.gradient F x) ∧
      g.tangentNorm x (D.gradient F x) ≤ 1 ∧
      ∀ v : TangentSpace (𝓡 n) x,
        D.hessian F x v v ≤ (5 / r) * g.inner x v v := by
    obtain ⟨herr, hl, hupp, hess⟩ := hcoreu x hx hx'
    refine ⟨?_, ?_, ?_, ?_⟩
    · have he : F x - (g.edist p x).toReal / 2 =
          κ * (u x - τ * (g.edist p x).toReal) := by
        dsimp [F]
        rw [mul_sub, ← mul_assoc, hκτ]
        ring
      rw [he, abs_mul, abs_of_pos hκ]
      have h := mul_le_mul_of_nonneg_left herr hκ.le
      simpa only [← mul_assoc, hκτ, one_div_mul_eq_div] using h
    · rw [hnorm]
      have h := mul_le_mul_of_nonneg_left hl hκ.le
      have hlow := mul_le_mul_of_nonneg_right hκhalf (show 0 ≤ 1 - δ ^ 2 by linarith)
      nlinarith
    · rw [hnorm]
      exact (mul_le_mul_of_nonneg_left hupp hκ.le).trans (by simpa using hκ1)
    · intro v
      change D.hessian (fun y => κ * u y) x v v ≤ _
      rw [D.hessian_const_mul]
      have hv : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (g.pos x v hv).le
      calc
        _ ≤ κ * ((5 / r) * g.inner x v v) := mul_le_mul_of_nonneg_left (hess v) hκ.le
        _ ≤ 1 * ((5 / r) * g.inner x v v) :=
          mul_le_mul_of_nonneg_right hκ1 (mul_nonneg (by positivity) hv)
        _ = _ := one_mul _
  have hregF (x : M) (hx : F x ∈ I) :
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) F x ≠ 0 :=
    (g.tangentNorm_gradient_pos_iff F x).mp
      ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
        (hcoreF x (hbandF x hx).1 (hbandF x hx).2).2.1)
  have hinside : Icc (55 * r / 96) (9 * r / 10) ⊆ I := by
    intro t ht
    change 9 * r / 16 < t ∧ t < 15 * r / 16
    constructor <;> linarith [ht.1, ht.2]
  have hball : F ⁻¹' Icc (55 * r / 96) (9 * r / 10) ⊆ g.ball p (2 * r) := by
    intro x hx
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm]
    exact (hbandF x (hinside hx)).2
  have hradial : {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
      F ⁻¹' Icc (7 * r / 12) (3 * r / 5) := by
    intro x hx
    have hxlo : r < (g.edist p x).toReal := by linarith [hx.1]
    have hxhi : (g.edist p x).toReal < 2 * r := by linarith [hx.2]
    have h := abs_le.mp (hcoreF x hxlo hxhi).1
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨F, u, hF, hu, ?_, hproperF, hregF, hbandF, ?_, hball, hradial, ?_⟩
  · intro x
    dsimp [F, κ]
    ring
  · intro x hx hx'
    exact ⟨(hcoreF x hx hx').1, (hcoreF x hx hx').2.1,
      (hcoreF x hx hx').2.2.1, (hcoreF x hx hx').2.2.2,
      (hcoreu x hx hx').2⟩
  · intro t ht
    have htwide : t ∈ Icc (55 * r / 96) (9 * r / 10) := by
      exact ⟨by linarith [ht.1], ht.2⟩
    have hwide : IsCompact (F ⁻¹' Icc (55 * r / 96) (9 * r / 10)) :=
      Poincare.Coarea.isCompact_slab_of_isProperMap hproperF hinside
    have hlevel : IsCompact (F ⁻¹' {t}) := hwide.of_isClosed_subset
      (isClosed_singleton.preimage hF.continuous) (by
        intro x hx
        have hxt : F x = t := hx
        simpa only [mem_preimage, hxt] using htwide)
    let T := u ⁻¹' Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)
    have hTband : Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4) ⊆
        Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) := by
      intro z hz
      exact (scalar_level_strip_parameters hr hτ hε ht hz).1
    have hT : IsCompact T :=
      Poincare.Coarea.isCompact_slab_of_isProperMap hproperu hTband
    have hTrange (x : M) (hx : x ∈ T) :
        9 * r / 8 < dist p x ∧ dist p x < 15 * r / 8 := by
      have hxc := hbandu x (hTband hx)
      exact (scalar_level_strip_parameters hr hτ hε ht hx).2
        ((g.edist p x).toReal) (hcoreu x hxc.1 hxc.2).1
    have hbuffer (x : M) (hx : x ∈ T) (y : M) (hy : y ∈ Metric.closedBall x (4 * s)) :
        1 - δ ^ 2 ≤ g.tangentNorm y (D.gradient u y) ∧
        g.tangentNorm y (D.gradient u y) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 n) y,
          D.hessian u y v v ≤ (5 / r) * g.inner y v v := by
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
      exact (hcoreu y hlo hhi).2
    have hgap (x : M) (hx : x ∈ T) :
        s ≤ (2 * τ * t + 3 * s / 2) - u x ∧
          (2 * τ * t + 3 * s / 2) - u x ≤ 2 * s := by
      change u x ∈ Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4) at hx
      constructor <;> linarith [hx.1, hx.2]
    obtain ⟨v, hv, hpair⟩ := g.exists_near_opposite_smoothing_of_upper_level D hc hsec hu hT
      hs hs1 hδ (by linarith : δ ≤ 1 / 16) (by positivity : 0 ≤ 5 / r) hHs hgap hbuffer
    let ν := 1 / (1 + δ ^ 2)
    let h := fun x => ν * v x
    have hν : 0 < ν := by dsimp [ν]; positivity
    have hν1 : ν ≤ 1 := by
      dsimp [ν]
      apply (div_le_one (by positivity)).mpr
      nlinarith [sq_nonneg δ]
    have hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h := contMDiff_const.mul hv
    have hH3 : 5 / r ≤ 3 / s := (le_div_iff₀ hs).mpr (by linarith)
    refine ⟨hlevel, h, hh, ?_, ?_⟩
    · intro x hx y hy
      have hux : u x = 2 * τ * t := by
        have hx' : u x / (2 * τ) = t := by
          simpa only [F, κ, div_eq_mul_inv, mul_comm, one_mul] using hx
        have he := (div_eq_iff (by positivity : 2 * τ ≠ 0)).mp hx'
        simpa only [mul_comm, mul_left_comm, mul_assoc] using he
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
        (D.gradient u x) (D.gradient v x) hδ hδsmall huall.1 huall.2.1 hp.2.1 hp.2.2.2
      change (1 / 2 : ℝ) ≤ ‖D.gradient u x‖ ∧ ‖D.gradient u x‖ ≤ 1 ∧
        (1 / 2 : ℝ) ≤ ‖D.gradient h x‖ ∧ ‖D.gradient h x‖ ≤ 1 ∧
        inner ℝ (D.gradient u x) (D.gradient h x) ≤ -1 + 128 * δ ∧ _
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

end PoincareConjecture.RiemannianMetric
