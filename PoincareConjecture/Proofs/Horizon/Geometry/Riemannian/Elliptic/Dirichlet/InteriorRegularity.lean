import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.DivergenceEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateRepresentative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.SmoothRepresentative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.LocalChart
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Eigenfunction













open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

universe u

namespace PoincareConjecture.LeviCivitaData.Dirichlet

theorem exists_smooth_eigenfunction_representative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) {Ω : Set M} (hΩ : IsOpen Ω)
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ) :
    ∃ U : M → ℝ,
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D Ω u : M → ℝ) ∧
      ∀ x ∈ Ω, -D.laplacian U x = lambda * U x := by
  have hrepresentative : ∃ U : M → ℝ,
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D Ω u : M → ℝ) := by
    apply exists_smooth_representative_of_local hΩ (toL2 D Ω u)
    intro x hx
    obtain ⟨e, he, hei, K, hK, hKs, O, hO, hOK, hxO, hOΩ, -⟩ :=
      exists_precompact_coordinate_neighborhood (n := n) hΩ hx
    have hOs := hOK.trans hKs
    let p (i : Fin n) := localCoordinateDerivative (D := D) (Ω := Ω)
      e he hei hK hKs hOK (EuclideanSpace.single i 1) u
    have huL2 : MemLp (fun y => toL2 D Ω u (e y)) 2 (volume.restrict O) :=
      (g.memLp_pullback_on_compact e he hei (toL2 D Ω u) hK hKs).mono_measure
        (Measure.restrict_mono hOK le_rfl)
    have hpL2 (i : Fin n) : MemLp (p i) 2 (volume.restrict O) := Lp.memLp (p i)
    have hweak (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
        (∫ y in O, toL2 D Ω u (e y) * fderiv ℝ φ y (EuclideanSpace.single i 1)) =
          -(∫ y in O, p i y * φ y) :=
      localCoordinateDerivative_weak e he hei hK hKs hOK hO u i hφ hc hs
    have hdiv (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
        (∫ y in O, ∑ i, ∑ j, divergenceCoefficients g e y i j * p j y *
          fderiv ℝ φ y (EuclideanSpace.single i 1)) =
          ∫ y in O, (lambda * g.pullbackVolumeDensity e y) * toL2 D Ω u (e y) * φ y :=
      weakEigen_divergence_local e he hei hK hKs hOK hOΩ u lambda heigen hφ hc hs
    obtain ⟨V, hVs, hVae⟩ : ∃ V : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiffOn ℝ ∞ V O ∧
          V =ᵐ[volume.restrict O] (fun y => toL2 D Ω u (e y)) := by
      apply Poincare.Analysis.Elliptic.exists_smooth_representative hn hO
        (divergenceCoefficients g e) (fun y => lambda * g.pullbackVolumeDensity e y)
        (fun y => toL2 D Ω u (e y)) (fun i y => p i y)
      · intro i j
        exact (contDiffOn_divergenceCoefficients e he hei i j).mono hOs
      · intro y hy
        apply Matrix.PosDef.of_dotProduct_mulVec_pos
        · ext i j
          change divergenceCoefficients g e y j i = divergenceCoefficients g e y i j
          exact divergenceCoefficients_symm e he hei (hOs hy) j i
        · intro v hv
          have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
            intro hz
            apply hv
            exact congrArg WithLp.ofLp hz
          have hpos := divergenceCoefficients_pos (g := g) e he hei (hOs hy)
            (WithLp.toLp 2 v) hv'
          simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
            Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hpos
      · intro y hy
        have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
          ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
        exact (contDiffAt_const.mul
          (g.contDiffAt_pullbackVolumeDensity
            (he.contMDiffAt (e.open_source.mem_nhds (hOs hy)))
            (hD.mfderiv_injective (hOs hy))).1).contDiffWithinAt
      · intro K _ hKO
        exact huL2.mono_measure (Measure.restrict_mono hKO le_rfl)
      · intro i K _ hKO
        exact (hpL2 i).mono_measure (Measure.restrict_mono hKO le_rfl)
      · exact hweak
      · exact hdiv
    obtain ⟨F, hFs, hFae⟩ := g.exists_smooth_representative_on_coordinate_image
      e he hei hO hOs (toL2 D Ω u) hVs hVae
    exact ⟨e '' O, e.isOpen_image_of_subset_source hO hOs, hxO, hOΩ, F, hFs, hFae⟩
  obtain ⟨U, hUs, hU⟩ := hrepresentative
  exact ⟨U, hUs, hU, laplacian_eq_of_smooth_representative hΩ u lambda heigen hUs hU⟩

end PoincareConjecture.LeviCivitaData.Dirichlet
