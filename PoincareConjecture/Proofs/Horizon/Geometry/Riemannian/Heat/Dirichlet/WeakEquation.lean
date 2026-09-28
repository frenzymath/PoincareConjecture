import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Resolvent

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem inner_test_eq_inner_oneSubLaplacian (u : H1Zero D Ω) (φ : EnergyTest D Ω) :
    ⟪u, (φ : H1Zero D Ω)⟫_ℝ = ⟪toL2 D Ω u, φ.oneSubLaplacian⟫_ℝ := by
  rw [← resolvent_oneSubLaplacian φ]
  exact (toL2 D Ω).adjoint_inner_right u φ.oneSubLaplacian

theorem resolvent_distribution (f : Lp ℝ 2 g.volumeMeasure) (φ : EnergyTest D Ω) :
    ⟪l2Resolvent D Ω f, φ.oneSubLaplacian⟫_ℝ = ⟪f, testToL2 D Ω φ⟫_ℝ := by
  change ⟪toL2 D Ω (resolvent D Ω f), φ.oneSubLaplacian⟫_ℝ = _
  rw [← inner_test_eq_inner_oneSubLaplacian, resolvent_inner, toL2_coe]

def EnergyTest.laplacianLp (φ : EnergyTest D Ω) : Lp ℝ 2 g.volumeMeasure :=
  testToL2 D Ω φ - φ.oneSubLaplacian

omit [PreconnectedSpace M] in
theorem EnergyTest.laplacianLp_ae (φ : EnergyTest D Ω) :
    (φ.laplacianLp : M → ℝ) =ᵐ[g.volumeMeasure] D.laplacian φ := by
  filter_upwards [Lp.coeFn_sub (testToL2 D Ω φ) φ.oneSubLaplacian,
    φ.memLp.coeFn_toLp, φ.oneSubLaplacian_memLp.coeFn_toLp] with x hsub hφ hΔ
  change (testToL2 D Ω φ - φ.oneSubLaplacian) x = D.laplacian φ x
  rw [hsub]
  change (testToL2 D Ω φ) x - φ.oneSubLaplacian x = D.laplacian φ x
  change (testToL2 D Ω φ) x = φ x at hφ
  change φ.oneSubLaplacian x = φ x - D.laplacian φ x at hΔ
  rw [hφ, hΔ]
  ring

theorem weak_eigenfunction_distribution (u : H1Zero D Ω) {lam : ℝ}
    (hu : ∀ v : H1Zero D Ω, ⟪u, v⟫_ℝ =
      (1 + lam) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ) (φ : EnergyTest D Ω) :
    ⟪toL2 D Ω u, φ.laplacianLp⟫_ℝ = -lam * ⟪toL2 D Ω u, testToL2 D Ω φ⟫_ℝ := by
  have h := hu (φ : H1Zero D Ω)
  rw [inner_test_eq_inner_oneSubLaplacian, toL2_coe] at h
  rw [EnergyTest.laplacianLp, inner_sub_right, h]
  ring

theorem weak_eigenvalue_nonneg {u : H1Zero D Ω} (hne : u ≠ 0) {lam : ℝ}
    (hu : ∀ v : H1Zero D Ω, ⟪u, v⟫_ℝ =
      (1 + lam) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ) : 0 ≤ lam := by
  have hJ : toL2 D Ω u ≠ 0 := by
    intro hz
    apply hne
    apply toL2_injective
    simpa using hz
  have hpos := (real_inner_self_pos (x := toL2 D Ω u)).mpr hJ
  have hn := norm_toL2_le u
  have hsq : ‖toL2 D Ω u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hsq
  have he := hu u
  nlinarith

end PoincareConjecture.LeviCivitaData.Dirichlet
