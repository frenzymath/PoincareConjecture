import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

theorem cap_inverse_edist_lt_of_target_edist_lt
    {n m : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N] [T3Space M]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 n) 1 e.symm e.target)
    {o : M} (ho : o ∈ e.source) {r C : ℝ} (hC : 0 < C)
    (hcover : h.ball (e o) r ⊆ e.target)
    (hbound : ∀ x ∈ e.source, g.edist o x ≤ ENNReal.ofReal (C * r) →
      ∀ v : TangentSpace (𝓡 n) x,
        g.tangentNorm x v ≤ C * h.tangentNorm (e x)
          (mfderiv (𝓡 n) (𝓡 m) e x v))
    {y : N} (hy : h.edist (e o) y < ENNReal.ofReal r) :
    g.edist o (e.symm y) < ENNReal.ofReal (C * r) := by
  have hyball : y ∈ h.ball (e o) r := by
    exact hy
  have himage := g.ball_subset_image_ball_of_forward_tangentNorm_le
    h e hf hi ho hC hcover hbound hyball
  obtain ⟨x, hx, hxy⟩ := himage
  have hy_target : y ∈ e.target := hcover hyball
  have hxeq : x = e.symm y := by
    apply e.injOn hx.2 (e.map_target hy_target)
    calc
      e x = y := hxy
      _ = e (e.symm y) := (e.right_inv hy_target).symm
  rw [hxeq] at hx
  exact hx.1

theorem cap_inverse_toReal_edist_lt_of_target_edist_lt
    {n m : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N] [T3Space M]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 n) 1 e.symm e.target)
    {o : M} (ho : o ∈ e.source) {r C : ℝ} (hC : 0 < C) (_hr : 0 < r)
    (hcover : h.ball (e o) r ⊆ e.target)
    (hbound : ∀ x ∈ e.source, g.edist o x ≤ ENNReal.ofReal (C * r) →
      ∀ v : TangentSpace (𝓡 n) x,
        g.tangentNorm x v ≤ C * h.tangentNorm (e x)
          (mfderiv (𝓡 n) (𝓡 m) e x v))
    {y : N} (hy : h.edist (e o) y < ENNReal.ofReal r) :
    (g.edist o (e.symm y)).toReal < C * r := by
  exact ENNReal.toReal_lt_of_lt_ofReal
    (cap_inverse_edist_lt_of_target_edist_lt g h e hf hi ho hC hcover hbound hy)



theorem cap_inverse_toReal_edist_le
    {n m : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N] [T3Space M]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 n) 1 e.symm e.target)
    {o : M} (ho : o ∈ e.source) {A C : ℝ} (hC : 0 < C)
    (hcover : h.ball (e o) A ⊆ e.target)
    (hbound : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm (e x)
        (mfderiv (𝓡 n) (𝓡 m) e x v))
    {x : M} (hx : x ∈ e.source)
    (himage : h.edist (e o) (e x) < ENNReal.ofReal A) :
    (g.edist o x).toReal ≤ C * (h.edist (e o) (e x)).toReal := by
  let d := (h.edist (e o) (e x)).toReal
  have hdA : d < A := ENNReal.toReal_lt_of_lt_ofReal himage
  have hdnonneg : 0 ≤ d := ENNReal.toReal_nonneg
  have hfinite : h.edist (e o) (e x) ≠ ⊤ := ne_top_of_lt himage
  by_contra hnot
  have hquot : d < (g.edist o x).toReal / C := by
    apply (lt_div_iff₀ hC).mpr
    simpa only [mul_comm] using lt_of_not_ge hnot
  obtain ⟨r, hdr, hr⟩ := exists_between (lt_min hdA hquot)
  have hrA : r < A := hr.trans_le (min_le_left _ _)
  have hrquot : r < (g.edist o x).toReal / C := hr.trans_le (min_le_right _ _)
  have hyr : h.edist (e o) (e x) < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff (hdnonneg.trans_lt hdr)).mpr hdr
  have hcoverr : h.ball (e o) r ⊆ e.target := by
    intro y hy
    exact hcover (hy.trans_le (ENNReal.ofReal_le_ofReal hrA.le))
  have hs := cap_inverse_edist_lt_of_target_edist_lt g h e hf hi ho hC hcoverr
    (fun z hz _ => hbound z hz) hyr
  rw [e.left_inv hx] at hs
  have hsreal := ENNReal.toReal_lt_of_lt_ofReal hs
  have hsmaller := (lt_div_iff₀ hC).mp hrquot
  nlinarith only [hsreal, hsmaller]

end PoincareConjecture.M47
