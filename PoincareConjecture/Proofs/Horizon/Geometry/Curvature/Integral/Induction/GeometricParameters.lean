import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.AreaGrowth









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData



theorem regularLevel_annular_bounds_of_gradient_hessian_bounds
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    {g : RiemannianMetric (m + 2) M}
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m + 2)) x),
      -1 ≤ D.sectionalCurvature x v w)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I) (hproper : IsProperMap (I.restrictPreimage f))
    {l H a₀ a b R : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (ha : 0 < a) (ha₀a : a₀ < a) (hab : a < b)
    (hslab : Icc a₀ (3 * b / 2) ⊆ I) (hR : 0 < R) (p : M)
    (hspeed : ∀ x : M, f x ∈ I →
      l ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1)
    (hhess : ∀ x : M, f x ∈ I → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      D.hessian f x v v ≤ H * g.inner x v v)
    (hball : f ⁻¹' Icc a₀ (3 * b / 2) ⊆ g.ball p R) :
    let C := RiemannianMetric.modelVolume (m + 2) 1 R / (a - a₀) *
      Real.exp ((((m + 1 : ℕ) : ℝ) * H / l ^ 2) * (3 * b / 2 - a₀))
    let α := max 1 (max (1 / l) (max ((H / l) * (3 * b / 2)) (C / a ^ (m + 1))))
    0 < α ∧
      (∀ t ∈ Icc a (3 * b / 2), g.regularLevelArea hf t ≤ α * t ^ (m + 1)) ∧
      (∀ t ∈ Icc a (3 * b / 2), ∀ x, f x = t →
        ∀ v : TangentSpace (𝓡 (m + 2)) x,
          g.inner x (D.gradient f x) v = 0 →
          D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v) ∧
      ∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
        1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
          g.tangentNorm x (g.gradient f x) ≤ 1 := by
  let C := RiemannianMetric.modelVolume (m + 2) 1 R / (a - a₀) *
    Real.exp ((((m + 1 : ℕ) : ℝ) * H / l ^ 2) * (3 * b / 2 - a₀))
  let α := max 1 (max (1 / l) (max ((H / l) * (3 * b / 2)) (C / a ^ (m + 1))))
  have hα : 0 < α := zero_lt_one.trans_le (le_max_left _ _)
  have hlα : 1 / l ≤ α := (le_max_left _ _).trans (le_max_right _ _)
  have hHα : (H / l) * (3 * b / 2) ≤ α :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCα : C / a ^ (m + 1) ≤ α :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hinside : Icc a (3 * b / 2) ⊆ I :=
    fun t ht => hslab ⟨ha₀a.le.trans ht.1, ht.2⟩
  have harea : ∀ t ∈ Icc a (3 * b / 2), g.regularLevelArea hf t ≤ C := by
    simpa only [one_mul] using D.regularLevelArea_le_of_gradient_hessian_bounds
      hc hsec hf hI hproper hl (show (0 : ℝ) ≤ 1 by norm_num) hH ha₀a
      (show a ≤ 3 * b / 2 by linarith) hslab hR p hspeed hhess hball
  refine ⟨hα, ?_, ?_, ?_⟩
  · intro t ht
    have hC : C ≤ α * a ^ (m + 1) := (div_le_iff₀ (pow_pos ha _)).mp hCα
    exact (harea t ht).trans (hC.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le ht.1 _) hα.le))
  · intro t ht x hxt v _
    have hx : f x ∈ I := hxt ▸ hinside ht
    have hs : l ≤ Real.sqrt (D.levelQ f x) := (hspeed x hx).1
    have hspos : 0 < Real.sqrt (D.levelQ f x) := hl.trans_le hs
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 2)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hv : 0 ≤ g.inner x v v := by
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg
    have hHt : H / l ≤ α / t := (le_div_iff₀ (ha.trans_le ht.1)).mpr
      ((mul_le_mul_of_nonneg_left ht.2 (div_nonneg hH hl.le)).trans hHα)
    calc
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤
          (H * g.inner x v v) / Real.sqrt (D.levelQ f x) :=
        div_le_div_of_nonneg_right (hhess x hx v) hspos.le
      _ ≤ (H * g.inner x v v) / l :=
        div_le_div_of_nonneg_left (mul_nonneg hH hv) hl hs
      _ = (H / l) * g.inner x v v := by ring
      _ ≤ (α / t) * g.inner x v v := mul_le_mul_of_nonneg_right hHt hv
  · intro x hx
    exact ⟨((one_div_le hl hα).mp hlα).trans (hspeed x (hinside hx)).1,
      (hspeed x (hinside hx)).2⟩

end PoincareConjecture.LeviCivitaData
