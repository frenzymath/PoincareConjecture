import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem pathELength_subtype_val_of_contMDiffAt {U : TopologicalSpace.Opens M}
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (γ : ℝ → U) {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 γ t) :
    gU.pathELength γ a b = g.pathELength (Subtype.val ∘ γ) a b := by
  rw [pathELength_eq_lintegral_tangentNorm, pathELength_eq_lintegral_tangentNorm]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [mfderiv_comp t ((contMDiff_subtype_val (n := 1)).mdifferentiable one_ne_zero (γ t))
    ((hγ t ht).mdifferentiableAt one_ne_zero)]
  change ENNReal.ofReal (Real.sqrt (gU.inner (γ t) _ _)) =
    ENNReal.ofReal (Real.sqrt (g.inner (γ t : M) _ _))
  rw [hinner]
  rfl



theorem ball_subtype_val_of_subset {U : TopologicalSpace.Opens M}
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (p : U) (r : ℝ) (hball : g.ball p r ⊆ U) :
    gU.ball p r = Subtype.val ⁻¹' g.ball (p : M) r := by
  classical
  ext q
  constructor
  · intro hq
    exact (gU.edist_map_le_of_metric_pullback g contMDiff_subtype_val hinner p q).trans_lt hq
  · intro hq
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hq zero_lt_one
    have hγball : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ g.ball (p : M) r := by
      intro t ht
      exact ((Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn h0 rfl ht.1).trans
        (Manifold.pathELength_mono le_rfl ht.2)).trans_lt hlen
    let γU : ℝ → U := fun t => if ht : γ t ∈ U then ⟨γ t, ht⟩ else p
    have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        (Subtype.val ∘ γU) =ᶠ[𝓝 t] γ := by
      have hmem := (hγ.continuous.tendsto t).eventually
        (U.isOpen.mem_nhds (hball (hγball t ht)))
      filter_upwards [hmem] with s hs
      change γ s ∈ U at hs
      simp only [Function.comp_apply, γU, dif_pos hs]
    have hγU : ∀ t ∈ Icc (0 : ℝ) 1,
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 γU t := by
      intro t ht
      apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℝ, ℝ) (𝓡 n) 1) γU univ t).mp
      exact (hγ t).congr_of_eventuallyEq (heq t ht)
    have h0U : γU 0 = p := by
      apply Subtype.ext
      exact ((heq 0 (by simp)).eq_of_nhds).trans h0
    have h1U : γU 1 = q := by
      apply Subtype.ext
      exact ((heq 1 (by simp)).eq_of_nhds).trans h1
    have hlength : gU.pathELength γU 0 1 = g.pathELength γ 0 1 := by
      rw [g.pathELength_subtype_val_of_contMDiffAt gU hinner γU hγU]
      exact Manifold.pathELength_congr (fun t ht => (heq t ht).eq_of_nhds)
    have hdist : gU.edist p q ≤ gU.pathELength γU 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
        ⟨gU.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength
        (fun t ht => (hγU t ht).contMDiffWithinAt) h0U h1U zero_le_one
    exact hdist.trans_lt (hlength.trans_lt hlen)

end PoincareConjecture.RiemannianMetric
