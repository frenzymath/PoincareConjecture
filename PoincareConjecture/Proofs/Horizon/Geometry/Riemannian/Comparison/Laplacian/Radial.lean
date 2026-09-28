import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Radial









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem inner_gradient_radial_coordinate (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) (hx0 : x ≠ 0)
    (hgauss : ∀ v : EuclideanSpace ℝ (Fin n),
      g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) = inner ℝ x v) :
    g.inner (e x) (D.gradient (fun y => ‖e.symm y‖) (e x))
      (D.gradient (fun y => ‖e.symm y‖) (e x)) = 1 := by
  rw [D.gradient_radial_coordinate e he hei hx hx0 hgauss]
  simp only [map_smul, smul_apply, smul_eq_mul, hgauss, real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hx0]



theorem laplacian_radial_coordinate (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) (hx0 : x ≠ 0)
    (hgauss : ∀ᶠ y in 𝓝 x, ∀ v : EuclideanSpace ℝ (Fin n),
      g.inner (e y) (mfderiv (𝓡 n) (𝓡 n) e y y)
        (mfderiv (𝓡 n) (𝓡 n) e y v) = inner ℝ y v) :
    D.laplacian (fun y => ‖e.symm y‖) (e x) =
      ((n : ℝ) - 1) / ‖x‖ +
        fderiv ℝ (g.pullbackVolumeDensity e) x x /
          (‖x‖ * g.pullbackVolumeDensity e x) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  have hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ‖e.symm y‖) (e x) := by
    have hn := (contDiffAt_norm ℝ
      (show e.symm (e x) ≠ 0 by simpa only [e.left_inv hx] using hx0) (n := ∞)).contMDiffAt
    exact hn.comp (e x) (hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hx)))
  have hgrad : mpullback (𝓡 n) (𝓡 n) e
      (D.gradient (fun y => ‖e.symm y‖)) =ᶠ[𝓝 x]
        (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖⁻¹ • y) := by
    filter_upwards [e.open_source.mem_nhds hx, eventually_ne_nhds hx0, hgauss]
      with y hy hy0 hgy
    rw [mpullback, D.gradient_radial_coordinate e he hei hy hy0 hgy]
    exact (show (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible from
      ⟨hD.mfderiv hy, rfl⟩).inverse_apply_self _
  have hflux (i : Fin n) :
      (fun y => g.pullbackVolumeDensity e y * WithLp.ofLp
        (mpullback (𝓡 n) (𝓡 n) e (D.gradient (fun z => ‖e.symm z‖)) y) i) =ᶠ[𝓝 x]
      (fun y => (g.pullbackVolumeDensity e y / ‖y‖) * WithLp.ofLp y i) := by
    filter_upwards [hgrad] with y hy
    rw [hy]
    simp [div_eq_mul_inv, mul_assoc]
  have hlap := D.density_mul_laplacian_eq_coordinate_divergence e he hei hx hu
  simp_rw [(hflux _).fderiv_eq] at hlap
  rw [sum_fderiv_density_radial (hρ.1.differentiableAt (by simp)) hx0] at hlap
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  apply (mul_left_inj' hρ.2.ne').mp
  calc
    D.laplacian (fun y => ‖e.symm y‖) (e x) * g.pullbackVolumeDensity e x =
        fderiv ℝ (g.pullbackVolumeDensity e) x x / ‖x‖ +
          ((n : ℝ) - 1) * g.pullbackVolumeDensity e x / ‖x‖ := by
      simpa only [mul_comm] using hlap
    _ = (((n : ℝ) - 1) / ‖x‖ +
        fderiv ℝ (g.pullbackVolumeDensity e) x x /
          (‖x‖ * g.pullbackVolumeDensity e x)) * g.pullbackVolumeDensity e x := by
      field_simp [hρ.2.ne']
      ring

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullbackVolumeDensity_congr_nhds (g : RiemannianMetric n M)
    {e f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (h : e =ᶠ[𝓝 x] f) : g.pullbackVolumeDensity e =ᶠ[𝓝 x] g.pullbackVolumeDensity f := by
  filter_upwards [eventually_eventually_nhds.mpr h] with y hy
  change e =ᶠ[𝓝 y] f at hy
  unfold pullbackVolumeDensity
  rw [hy.mfderiv_eq, hy.self_of_nhds]

theorem inner_gradient_inverse_branch (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (heB : EqOn e B B.source)
    (hB : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ B.source) (hv0 : v ≠ 0)
    (hgauss : ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = inner ℝ v w) :
    g.inner (e v) (D.gradient (fun y => ‖B.symm y‖) (e v))
      (D.gradient (fun y => ‖B.symm y‖) (e v)) = 1 := by
  have hlocal : e =ᶠ[𝓝 v] B :=
    Filter.eventuallyEq_of_mem (B.open_source.mem_nhds hv) heB
  rw [hlocal.mfderiv_eq, heB hv] at hgauss
  rw [heB hv]
  exact D.inner_gradient_radial_coordinate B hB hBi hv hv0 hgauss



theorem laplacian_inverse_branch (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (heB : EqOn e B B.source)
    (hB : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B.source) (hx0 : x ≠ 0)
    (hgauss : ∀ᶠ y in 𝓝 x, ∀ v : EuclideanSpace ℝ (Fin n),
      g.inner (e y) (mfderiv (𝓡 n) (𝓡 n) e y y)
        (mfderiv (𝓡 n) (𝓡 n) e y v) = inner ℝ y v) :
    D.laplacian (fun y => ‖B.symm y‖) (e x) =
      ((n : ℝ) - 1) / ‖x‖ + fderiv ℝ (g.pullbackVolumeDensity e) x x /
        (‖x‖ * g.pullbackVolumeDensity e x) := by
  have hlocal : e =ᶠ[𝓝 x] B :=
    Filter.eventuallyEq_of_mem (B.open_source.mem_nhds hx) heB
  have hBgauss : ∀ᶠ y in 𝓝 x, ∀ v : EuclideanSpace ℝ (Fin n),
      g.inner (B y) (mfderiv (𝓡 n) (𝓡 n) B y y)
        (mfderiv (𝓡 n) (𝓡 n) B y v) = inner ℝ y v := by
    filter_upwards [eventually_eventually_nhds.mpr hlocal, hgauss] with y hy hgy
    change e =ᶠ[𝓝 y] B at hy
    rw [hy.mfderiv_eq, hy.self_of_nhds] at hgy
    exact hgy
  have hdensity := g.pullbackVolumeDensity_congr_nhds hlocal
  rw [heB hx, D.laplacian_radial_coordinate B hB hBi hx hx0 hBgauss,
    hdensity.fderiv_eq, hdensity.self_of_nhds]

end PoincareConjecture.RiemannianMetric
