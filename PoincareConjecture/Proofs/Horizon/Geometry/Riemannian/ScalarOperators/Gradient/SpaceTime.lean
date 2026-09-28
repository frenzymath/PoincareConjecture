import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.SpatialDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Matrix
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricDuality








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma eventually_basis_extend {ι : Type} (x : M)
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    ∀ᶠ y in nhds x, ∃ c : Module.Basis ι ℝ (TangentSpace (𝓡 n) y),
      ∀ i, c i = FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E V x
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  let L := (e.continuousLinearEquivAt ℝ x hx).trans
    (e.continuousLinearEquivAt ℝ y hy).symm
  refine ⟨b.map L.toLinearEquiv, fun i => ?_⟩
  change (e.continuousLinearEquivAt ℝ y hy).symm
    ((e.continuousLinearEquivAt ℝ x hx) (b i)) = _
  rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq,
    Bundle.Trivialization.symmL_apply _ hy]
  rfl


theorem contMDiffAt_gradient_normSq_spacetime (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ g.inner p.2 (D.gradient (fun y ↦ F (p.1, y)) p.2)
        (D.gradient (fun y ↦ F (p.1, y)) p.2)) (t, x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let e := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let G : ℝ × M → Matrix _ _ ℝ := fun p i j => g.inner p.2 (e i p.2) (e j p.2)
  have he (i) : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (e i)) x := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) _ (b i)
  have hG (i j) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ G p i j) (t, x) := by
    have h := ((g.contMDiff x).clm_bundle_apply (he i)).clm_bundle_apply (he j)
    have hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y ↦ g.inner y (e i y) (e j y)) x := by
      simpa using (contMDiffAt_totalSpace.mp h).2
    exact hs.comp (t, x) (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)))
  have hGx : G (t, x) = 1 := by
    ext i j
    change g.inner x (e i x) (e j x) = _
    simp only [e, FiberBundle.extend_apply_self]
    exact b.inner_eq_ite i j
  have hi := Poincare.Manifold.contMDiffAt_matrix_inv_entry G (t, x) hG (by simp [hGx])
  have hd (i) := Poincare.Manifold.contMDiffAt_mvfderiv_spatial hF (he i)
  have hsum := ContMDiffAt.sum (t := Finset.univ) fun i _ =>
    ContMDiffAt.sum (t := Finset.univ) fun j _ => (hi i j).mul ((hd i).mul (hd j))
  apply hsum.congr_of_eventuallyEq
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (nhds (t, x)) (nhds x) := continuousAt_snd
  filter_upwards [hsnd.eventually (eventually_basis_extend x b.toBasis)] with p hp
  obtain ⟨c, hc⟩ := hp
  have h := linear_apply_eq_inverse_gram
    (mvfderiv (𝓡 n) (fun y ↦ F (p.1, y)) p.2).toLinearMap
    (D.gradient (fun y ↦ F (p.1, y)) p.2) c (g.orthonormalBasis p.2)
  change mvfderiv (𝓡 n) (fun y ↦ F (p.1, y)) p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner p.2 (c i) (c j)))⁻¹ i j *
      (g.inner p.2 (D.gradient (fun y ↦ F (p.1, y)) p.2) (c i) *
        mvfderiv (𝓡 n) (fun y ↦ F (p.1, y)) p.2 (c j)) at h
  rw [← D.inner_gradient] at h
  simp only [hc, OrthonormalBasis.coe_toBasis] at h
  simp_rw [D.inner_gradient] at h
  rw [D.inner_gradient]
  exact h

end PoincareConjecture.LeviCivitaData
