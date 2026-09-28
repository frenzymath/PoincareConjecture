import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem exists_local_chart_realization
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (heDiff : e.MDifferentiable (𝓡 n) (𝓡 n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g') (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ x ∈ V ∧ V ⊆ e.source ∧
        ∀ y ∈ V, g'.euclideanCoefficients y = g.pullbackCoefficients e y := by
  apply RiemannianMetric.exists_local_realization e.open_source hx
    (g.pullbackCoefficients e)
  · intro y hy
    exact (g.contDiffAt_pullbackCoefficients
      ((he y hy).contMDiffAt (e.open_source.mem_nhds hy))).contDiffWithinAt
  · intro y hy v w
    exact g.symm (e y) _ _
  · intro y hy v hv
    apply g.pos (e y)
    intro hz
    apply hv
    apply heDiff.mfderiv_injective hy
    rw [map_zero]
    convert! hz using 1

theorem density_mul_laplacian_eq_coordinate_divergence
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u : M → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ e.source)
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (e x)) :
    g.pullbackVolumeDensity e x * D.laplacian u (e x) =
      ∑ i, fderiv ℝ (fun y => g.pullbackVolumeDensity e y *
        WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) y) i) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have heDiff : e.MDifferentiable (𝓡 n) (𝓡 n) := ⟨
    fun y hy => (he y hy).mdifferentiableWithinAt (by simp),
    fun y hy => (he' y hy).mdifferentiableWithinAt (by simp)⟩
  obtain ⟨g', D', V, hVo, hxV, _, hcoeff⟩ :=
    exists_local_chart_realization (g := g) e he heDiff hx
  have hef := (he x hx).contMDiffAt (e.open_source.mem_nhds hx)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.source) :
      (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible := ⟨heDiff.mfderiv hy, rfl⟩
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact hi y hy
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g'.inner y a b = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y a) (mfderiv (𝓡 n) (𝓡 n) e y b) := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    have hc := hcoeff y hy
    intro a b
    rw [show g'.inner y a b = g'.euclideanCoefficients y a b by rfl, hc]
    rfl
  have hgrad : D'.gradient (u ∘ e) =ᶠ[𝓝 x]
      mpullback (𝓡 n) (𝓡 n) e (D.gradient u) := by
    have hu1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (hu.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞))
    filter_upwards [e.open_source.mem_nhds hx, hef.continuousAt.eventually hu1, hmetric]
      with y hye huy hmy
    exact D'.gradient_comp_eq_mpullback D (heDiff.mdifferentiableAt hye)
      (huy.mdifferentiableAt (by simp)) (hi y hye) hmy
  have hlap := D'.laplacian_comp_of_metric_pullback D hef hinv hmetric hu
  have hden : g'.pullbackVolumeDensity id =ᶠ[𝓝 x] g.pullbackVolumeDensity e := by
    filter_upwards [hmetric] with y hy
    unfold RiemannianMetric.pullbackVolumeDensity
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
    congr 2
    ext i j
    exact hy _ _
  rw [← hden.self_of_nhds, ← hlap,
    D'.density_mul_laplacian_eq_divergence
      (contMDiffAt_iff_contDiffAt.mp (hu.comp x hef))]
  apply Finset.sum_congr rfl
  intro i _
  have hflux : (fun y => g'.pullbackVolumeDensity id y *
      WithLp.ofLp (D'.gradient (u ∘ e) y) i) =ᶠ[𝓝 x]
      (fun y => g.pullbackVolumeDensity e y *
        WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) y) i) := by
    filter_upwards [hden, hgrad] with y hyd hyg
    rw [hyd, hyg]
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin n) ℝ i)) hflux.fderiv_eq

theorem contDiffAt_coordinateGradient
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ e.source) (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e x)) :
    ContDiffAt ℝ ∞ (mpullback (𝓡 n) (𝓡 n) e (D.gradient f)) x := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have h := (D.contMDiffAt_gradient hf).mpullback_vectorField_preimage
    (he.contMDiffAt (e.open_source.mem_nhds hx))
    (show (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible from ⟨hD.mfderiv hx, rfl⟩)
    (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  exact contMDiffAt_iff_contDiffAt.mp (by
    simpa using (Bundle.contMDiffAt_totalSpace.mp h).2)

theorem contDiffAt_coordinateGradientFlux
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ e.source) (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e x))
    (i : Fin n) :
    ContDiffAt ℝ ∞ (fun y => g.pullbackVolumeDensity e y *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient f) y) i) x := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ := (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).1
  have hcoord : ContDiffAt ℝ ∞
      (fun y => WithLp.ofLp
        (mpullback (𝓡 n) (𝓡 n) e (D.gradient f) y) i) x := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp x
      (D.contDiffAt_coordinateGradient e he hei hx hf)
  exact hρ.mul hcoord

theorem contDiffAt_laplacian_comp_chart
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    ContDiffAt ℝ ∞ (fun y => D.laplacian f (e y)) x := by
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i y =>
    g.pullbackVolumeDensity e y *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient f) y) i
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.source) :=
    g.contDiffAt_pullbackVolumeDensity (he.contMDiffAt (e.open_source.mem_nhds hy))
      (hD.mfderiv_injective hy)
  have hs : ContDiffAt ℝ ∞ (fun y =>
      ∑ i, fderiv ℝ (V i) y (EuclideanSpace.basisFun (Fin n) ℝ i)) x := by
    apply ContDiffAt.sum
    intro i _
    exact ((D.contDiffAt_coordinateGradientFlux e he hei hx (hf (e x)) i).fderiv_right
      (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiffAt_const
  apply (hs.div (hρ x hx).1 (hρ x hx).2.ne').congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  apply (eq_div_iff (hρ y hy).2.ne').mpr
  rw [mul_comm, D.density_mul_laplacian_eq_coordinate_divergence e he hei hy (hf (e y))]

end PoincareConjecture.LeviCivitaData
