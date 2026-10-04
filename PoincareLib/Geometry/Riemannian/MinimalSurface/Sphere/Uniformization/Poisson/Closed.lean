import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Uniformization.Poisson.Smooth

/-!
# Mean-zero smooth Poisson solvability on a closed surface

The spectral inverse, genuine energy lift, chart regularity, smooth
representative gluing, and Green identity yield an actual classical
solution. Source: Moroianu, arXiv:1101.2355, Theorem 5, Poisson step;
MT Lemma 18.10, printed pp. 424-426, sphere uniformization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareMT.M60

open LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

/-- Every actual smooth mean-zero source on a closed connected surface
is the negative Laplacian of a smooth function. Source: Moroianu,
Theorem 5, Poisson step; MT Lemma 18.10, pp. 424-426. -/
theorem exists_smooth_negative_laplacian_closed_surface (D : LeviCivitaData g)
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hmean : (∫ x, f x ∂g.volumeMeasure) = 0) :
    ∃ U : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ U ∧
      ∀ x, -D.laplacian U x = f x := by
  let s : EnergyTest D univ :=
    ⟨f, hf, HasCompactSupport.of_compactSpace _, subset_univ _⟩
  let F := toDomainL2 D univ (s : H1Zero D univ)
  have hFae : (F : M → ℝ) =ᵐ[g.volumeMeasure] f := by
    have h := toDomainL2_ae (s : H1Zero D univ)
    simp only [Measure.restrict_univ, toL2_coe] at h
    exact h.trans s.memLp.coeFn_toLp
  have hFmean : (∫ x, F x ∂g.volumeMeasure) = 0 :=
    (integral_congr_ae hFae).trans hmean
  obtain ⟨u, hu⟩ := exists_weak_poisson_closed_surface D F hFmean
  have hforce (v : H1Zero D univ) :
      ⟪u, v⟫_ℝ - ⟪toL2 D univ u, toL2 D univ v⟫_ℝ =
        ⟪testToL2 D univ s, toL2 D univ v⟫_ℝ := by
    have h := hu v
    change ⟪u, v⟫_ℝ - ⟪toDomainL2 D univ u, toDomainL2 D univ v⟫_ℝ =
      ⟪toDomainL2 D univ (s : H1Zero D univ), toDomainL2 D univ v⟫_ℝ at h
    rw [inner_toDomainL2 MeasurableSet.univ, inner_toDomainL2 MeasurableSet.univ,
      toL2_coe] at h
    exact h
  obtain ⟨U, hUs, hUae⟩ := exists_smooth_poisson_representative (D := D)
    (by norm_num) isOpen_univ u (testToL2 D univ s) f hf s.memLp.coeFn_toLp hforce
  have hUs' := contMDiffOn_univ.mp hUs
  have hUae' : U =ᵐ[g.volumeMeasure] (toL2 D univ u : M → ℝ) := by
    simpa only [Measure.restrict_univ] using hUae
  exact ⟨U, hUs', laplacian_eq_of_closed_smooth_poisson u (testToL2 D univ s) f hf
    s.memLp.coeFn_toLp hforce hUs' hUae'⟩

/-- The actual smooth Laplacian is surjective onto smooth mean-zero
functions on a closed connected surface. Source: Moroianu, Theorem 5,
Poisson step; MT Lemma 18.10, pp. 424-426. -/
theorem exists_smooth_poisson_closed_surface (D : LeviCivitaData g)
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hmean : (∫ x, f x ∂g.volumeMeasure) = 0) :
    ∃ U : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ U ∧
      ∀ x, D.laplacian U x = f x := by
  obtain ⟨U, hU, hEq⟩ := exists_smooth_negative_laplacian_closed_surface D
    (fun x => -f x) hf.neg (by rw [integral_neg, hmean, neg_zero])
  refine ⟨U, hU, fun x => ?_⟩
  have h := hEq x
  linarith

end PoincareMT.M60
