import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Jacobi








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem radialVariation_jacobi_on_domain
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {R : ℝ} {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (w : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t • v ∈ Metric.ball 0 R) :
    let γ : ℝ → M := fun τ => e (τ • v)
    let J : (τ : ℝ) → TangentSpace (𝓡 n) (γ τ) :=
      fun τ => mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
        (fun s : ℝ => e (τ • (v + s • w))) 0 1
    ConnectionVariation.manifoldCovDerivAlong g γ
        (ConnectionVariation.manifoldCovDerivAlong g γ J 1) 1 t +
      D.curvature (γ t) (J t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) = 0 := by
  have hnear : {z : ℝ × ℝ | v + z.1 • w ∈ Metric.ball 0 R ∧
      z.2 • (v + z.1 • w) ∈ Metric.ball 0 R} ∈ 𝓝 (0, t) := by
    apply IsOpen.mem_nhds
    · exact (Metric.isOpen_ball.preimage (by fun_prop)).inter
        (Metric.isOpen_ball.preimage (by fun_prop))
    · change v + (0 : ℝ) • w ∈ Metric.ball 0 R ∧
        t • (v + (0 : ℝ) • w) ∈ Metric.ball 0 R
      simpa only [zero_smul, add_zero] using And.intro hv ht
  obtain ⟨S, I, hS, h0, hI, htI, hsub⟩ := mem_nhds_prod_iff'.mp hnear
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z : ℝ × ℝ => e (z.2 • (v + z.1 • w))) (S ×ˢ I) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact fun z hz => (hsub hz).2
  have hvariation : ∀ s ∈ S,
      g.IsGeodesicOn (fun r : ℝ => e (r • (v + s • w))) I := by
    intro s hs r hr
    have hvary : v + s • w ∈ Metric.ball 0 R :=
      (hsub (show (s, t) ∈ S ×ˢ I from ⟨hs, htI⟩)).1
    have hdom : r • (v + s • w) ∈ Metric.ball 0 R :=
      (hsub (show (s, r) ∈ S ×ˢ I from ⟨hs, hr⟩)).2
    exact hgeo (v + s • w) hvary r hdom
  have hj := ConnectionVariation.manifoldVariation_jacobi g D hS hI h0
    hsmooth hvariation htI
  dsimp only at hj
  rw [show v + (0 : ℝ) • w = v by simp] at hj
  exact hj

end PoincareConjecture.RiemannianMetric
