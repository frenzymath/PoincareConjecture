import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric












set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem pathELength_eq_lintegral_tangentNorm
    (g : RiemannianMetric n M) (γ : ℝ → M) (a b : ℝ) :
    g.pathELength γ a b = ∫⁻ u in Icc a b,
      ENNReal.ofReal (g.tangentNorm (γ u) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [pathELength, Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  congr 1
  funext u
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl


theorem pathELength_le_of_tangentNorm_le
    (g h : RiemannianMetric n M) (γ : ℝ → M) (a b C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ u ∈ Icc a b, ∀ v : TangentSpace (𝓡 n) (γ u),
      h.tangentNorm (γ u) v ≤ C * g.tangentNorm (γ u) v) :
    h.pathELength γ a b ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  rw [pathELength_eq_lintegral_tangentNorm, pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro u hu
  exact (ENNReal.ofReal_le_ofReal (hbound u hu _)).trans_eq
    (ENNReal.ofReal_mul hC)


theorem ball_subset_ball_of_tangentNorm_le
    (g h : RiemannianMetric n M) (p : M) (r C : ℝ) (hC : 0 < C)
    (hbound : ∀ x ∈ g.ball p r, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm x v ≤ C * g.tangentNorm x v) :
    g.ball p r ⊆ h.ball p (C * r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro x hx
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hx
  have hγball : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ g.ball p r := by
    intro u hu
    apply lt_of_le_of_lt _ hγlength
    exact (Manifold.riemannianEDist_le_pathELength
      (hγsmooth.mono (Icc_subset_Icc le_rfl hu.2)) hγ0 rfl hu.1).trans
      (Manifold.pathELength_mono le_rfl hu.2)
  have hlength := pathELength_le_of_tangentNorm_le g h γ 0 1 C hC.le
    (fun u hu ↦ hbound (γ u) (hγball u hu))
  have hdist : h.edist p x ≤ h.pathELength γ 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hγsmooth hγ0 hγ1 zero_le_one
  change h.edist p x < ENNReal.ofReal (C * r)
  rw [ENNReal.ofReal_mul hC.le]
  exact (hdist.trans hlength).trans_lt
    (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
      ENNReal.ofReal_ne_top hγlength)



theorem edist_le_mul_edist_of_tangentNorm_le_on_ball
    (g h : RiemannianMetric n M) (p : M) (r C : ℝ) (hr : 0 < r) (hC : 0 < C)
    (hbound : ∀ z ∈ g.ball p (3 * r), ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm z v ≤ C * g.tangentNorm z v)
    {x y : M} (hx : x ∈ g.ball p r) (hy : y ∈ g.ball p r) :
    h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hxy : g.edist x y < ENNReal.ofReal (2 * r) := by
    calc
      g.edist x y ≤ g.edist x p + g.edist p y := Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal r + ENNReal.ofReal r :=
        ENNReal.add_lt_add (by simpa [ball, edist, Manifold.riemannianEDist_comm] using hx) hy
      _ = ENNReal.ofReal (2 * r) := by rw [← ENNReal.ofReal_add hr.le hr.le]; congr 1; ring
  have hdiv : h.edist x y / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (lt_min hb hxy)
    have hγball : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ g.ball p (3 * r) := by
      intro u hu
      have hxu : g.edist x (γ u) < ENNReal.ofReal (2 * r) := by
        exact ((Manifold.riemannianEDist_le_pathELength
          (hγsmooth.mono (Icc_subset_Icc le_rfl hu.2)) hγ0 rfl hu.1).trans
          (Manifold.pathELength_mono le_rfl hu.2)).trans_lt
          (hγlength.trans_le (min_le_right _ _))
      calc
        g.edist p (γ u) ≤ g.edist p x + g.edist x (γ u) :=
          Manifold.riemannianEDist_triangle
        _ < ENNReal.ofReal r + ENNReal.ofReal (2 * r) := ENNReal.add_lt_add hx hxu
        _ = ENNReal.ofReal (3 * r) := by
          rw [← ENNReal.ofReal_add hr.le (by positivity : 0 ≤ 2 * r)]; congr 1; ring
    have hlength := pathELength_le_of_tangentNorm_le g h γ 0 1 C hC.le
      (fun u hu ↦ hbound (γ u) (hγball u hu))
    have hdist : h.edist x y ≤ h.pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨h.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hγsmooth hγ0 hγ1 zero_le_one
    apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
      ENNReal.ofReal_ne_top).mpr
    calc
      h.edist x y ≤ ENNReal.ofReal C * g.pathELength γ 0 1 := hdist.trans hlength
      _ ≤ b * ENNReal.ofReal C := by
        rw [mul_comm b]
        exact mul_le_mul_right (hγlength.le.trans (min_le_left _ _)) _
  simpa only [mul_comm] using (ENNReal.div_le_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top).mp hdiv

end PoincareConjecture.RiemannianMetric
