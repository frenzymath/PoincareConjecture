import PoincareConjecture.Proofs.M04.LocalMetricComparison










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem metric_edist_le_pathELength_local
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hab : a ≤ b) :
    g.edist (γ a) (γ b) ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist (𝓡 n) (γ a) (γ b) ≤
    Manifold.pathELength (𝓡 n) γ a b
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

theorem initial_pathELength_le_of_mapsTo_initial_ball
    {T K α r : ℝ} (F : RicciFlow n M (Icc 0 T))
    (hK : 0 < K) (hT0 : 0 ≤ T) (hT : T ≤ α / K) (p : M)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {t a b : ℝ} (ht : t ∈ Icc 0 T) (hab : a ≤ b)
    {γ : ℝ → M}
    (hγ : MapsTo γ (Icc a b) ((F.metric 0).ball p r)) :
    (F.metric 0).pathELength γ a b ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * α)) *
        (F.metric t).pathELength γ a b := by
  apply pathELength_le_of_tangentNorm_le (F.metric 0) (F.metric t)
    (C := Real.exp ((n : ℝ) * α)) (by positivity)
  · intro x hx v
    have hcomp := tangentNorm_comparison_on_initial_ball F hK hT0 hT p hRm ht
      hx v
    exact hcomp.1
  · exact hγ

theorem initial_distance_le_of_pathELength_lt
    {T K α r : ℝ} (F : RicciFlow n M (Icc 0 T))
    (hK : 0 < K) (hT0 : 0 ≤ T) (hT : T ≤ α / K) (p : M)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {t a b : ℝ} (ht : t ∈ Icc 0 T) (hab : a ≤ b)
    {x : M} {γ : ℝ → M} (hγ0 : γ a = p) (hγ1 : γ b = x)
    (hpath : MapsTo γ (Icc a b) ((F.metric 0).ball p r))
    (hγsmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hshort : (F.metric t).pathELength γ a b <
      ENNReal.ofReal (Real.exp (-(n : ℝ) * α) * r)) :
    (F.metric 0).edist p x < ENNReal.ofReal r := by
  have hlen := initial_pathELength_le_of_mapsTo_initial_ball F hK hT0 hT p hRm
    ht hab hpath
  have hscale :
      ENNReal.ofReal (Real.exp ((n : ℝ) * α)) *
          ENNReal.ofReal (Real.exp (-(n : ℝ) * α) * r) =
        ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp ((n : ℝ) * α))]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hinitial : (F.metric 0).pathELength γ a b < ENNReal.ofReal r := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * α)) *
          (F.metric t).pathELength γ a b := hlen
      _ < ENNReal.ofReal (Real.exp ((n : ℝ) * α)) *
          ENNReal.ofReal (Real.exp (-(n : ℝ) * α) * r) := by
        simpa [mul_comm] using ENNReal.mul_lt_mul_left
          (a := ENNReal.ofReal (Real.exp ((n : ℝ) * α)))
          (b := (F.metric t).pathELength γ a b)
          (c := ENNReal.ofReal (Real.exp (-(n : ℝ) * α) * r))
          (ne_of_gt (by positivity)) ENNReal.ofReal_ne_top hshort
      _ = ENNReal.ofReal r := hscale
  have hed := metric_edist_le_pathELength_local (F.metric 0)
    (hγsmooth.contMDiffOn) hab
  rw [hγ0, hγ1] at hed
  exact hed.trans_lt hinitial

end PoincareConjecture.M04
