import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateJacobian
import PoincareConjecture.Proofs.M60.Mathlib.UniformizationLocalInverse














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)








theorem exists_local_annular_harmonic_coordinates {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) {x : Plane}
    (hx : x ∈ scalarAnnulus) (hgrad : D.gradient H x ≠ 0) :
    ∃ e : OpenPartialHomeomorph Plane Plane,
      x ∈ e.source ∧ e.source ⊆ scalarAnnulus ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (∀ y ∈ e.source, e y 0 = H y) ∧
      ∀ y ∈ e.source, fderiv ℝ (fun z => e z 1) y = scalarConjugateForm D H y := by
  obtain ⟨r, V, hr, hball, hVs, hdV⟩ := exists_local_annular_conjugate D hHs hHlap hx
  obtain ⟨U, hUs, -, -, hUH⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hHs hx
  have hgradc : ContinuousAt (D.gradient H) x :=
    (D.contDiffAt_gradient_euclidean (contMDiffAt_iff_contDiffAt.mp
      (hHs.contMDiffAt (scalarAnnulus_isOpen.mem_nhds hx)))).continuousAt
  have hne : ∀ᶠ y in 𝓝 x, D.gradient H y ≠ 0 :=
    hgradc.eventually (eventually_ne_nhds hgrad)
  obtain ⟨S, hSsub, hS, hxS⟩ := mem_nhds_iff.mp (inter_mem
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    (inter_mem hUH.eventually_nhds hne))
  let F : Plane → Plane := fun y =>
    U y • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      V y • EuclideanSpace.basisFun (Fin 2) ℝ 1
  have hFs : ContDiff ℝ ∞ F :=
    ((contMDiff_iff_contDiff.mp hUs).smul contDiff_const).add
      (hVs.smul contDiff_const)
  have hdF (y : Plane) (hy : y ∈ S) : HasFDerivAt F (scalarConjugateLinear D H y) y := by
    have huH : U =ᶠ[𝓝 y] H := (hSsub hy).2.1
    have hu : HasFDerivAt U (fderiv ℝ H y) y := by
      rw [← huH.fderiv_eq]
      exact ((contMDiff_iff_contDiff.mp hUs).differentiable (by simp) y).hasFDerivAt
    exact (hu.smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 0)).add
      ((hdV y (hSsub hy).1).smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hinv (y : Plane) (hy : y ∈ S) : (mfderiv (𝓡 2) (𝓡 2) F y).IsInvertible := by
    rw [mfderiv_eq_fderiv, (hdF y hy).fderiv]
    exact scalarConjugateLinear_invertible D H (hSsub hy).2.2
  obtain ⟨e, hxe, heS, heF, hes, heis⟩ := M60.exists_local_smooth_inverse_surface F hS
    (contMDiffOn_iff_contDiffOn.mpr hFs.contDiffOn) hinv hxS
  refine ⟨e, hxe, fun y hy => hball (hSsub (heS hy)).1, hes, heis, ?_, ?_⟩
  · intro y hy
    rw [heF hy]
    simpa [F] using (hSsub (heS hy)).2.1.self_of_nhds
  · intro y hy
    have hloc : (fun z => e z 1) =ᶠ[𝓝 y] V := by
      filter_upwards [e.open_source.mem_nhds hy] with z hz
      rw [heF hz]
      simp [F]
    rw [hloc.fderiv_eq]
    exact (hdV y (hSsub (heS hy)).1).fderiv








theorem exists_annular_harmonic_coordinate_pair :
    ∃ (H : Plane → ℝ) (w : H1Zero D scalarAnnulus) (x : Plane)
        (e : OpenPartialHomeomorph Plane Plane),
      x ∈ e.source ∧ e.source ⊆ scalarAnnulus ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ) ∧
      (∀ y ∈ scalarAnnulus, D.laplacian H y = 0) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (∀ y ∈ e.source, e y 0 = H y) ∧
      ∀ y ∈ e.source, fderiv ℝ (fun z => e z 1) y = scalarConjugateForm D H y := by
  obtain ⟨H, w, hHs, hHae, hHlap, hnon, -⟩ :=
    exists_annular_nonconstant_smooth_harmonic_potential D
  obtain ⟨x, hx, hgrad⟩ := exists_nonzero_annular_gradient D hHs hnon
  obtain ⟨e, hxe, hea, hes, heis, he0, he1⟩ :=
    exists_local_annular_harmonic_coordinates D hHs hHlap hx hgrad
  exact ⟨H, w, x, e, hxe, hea, hHs, hHae, hHlap, hes, heis, he0, he1⟩

end PoincareConjecture.M64Uniformization
