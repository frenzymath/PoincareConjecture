import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Poisson.SmoothEigenbasis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

def closedLaplacianTest (D : LeviCivitaData g) :
    EnergyTest D univ →ₗ[ℝ] EnergyTest D univ where
  toFun f := ⟨D.laplacian f, D.contMDiff_laplacian f.smooth,
    HasCompactSupport.of_compactSpace _, subset_univ _⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact D.laplacian_add f.smooth h.smooth x
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact D.laplacian_const_mul c f x

def closedLaplacianToL2 (D : LeviCivitaData g) :
    EnergyTest D univ →ₗ[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict univ) :=
  (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 univ).toLinearMap.comp
    ((testToL2 D univ).comp (closedLaplacianTest D))

omit [PreconnectedSpace M] in
theorem closedLaplacianToL2_ae (D : LeviCivitaData g) (f : EnergyTest D univ) :
    (closedLaplacianToL2 D f : M → ℝ) =ᵐ[g.volumeMeasure.restrict univ]
      D.laplacian f := by
  have htest := ((closedLaplacianTest D f).memLp.coeFn_toLp).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (univ : Set M))))
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ univ
    (testToL2 D univ (closedLaplacianTest D f)), htest] with x hx hy
  exact hx.trans hy

omit [PreconnectedSpace M] in

theorem eigenbasis_mem_range_closedLaplacian (D : LeviCivitaData g)
    (i : EigenIndex D univ) (hi : eigenvalue D univ i ≠ 0) :
    eigenbasis D univ (by norm_num) isOpen_univ (by simpa using isCompact_univ) i ∈
      LinearMap.range (closedLaplacianToL2 D) := by
  obtain ⟨U, hU, hUae, hUeq⟩ := exists_smooth_eigenbasis_representative D i
  let f : EnergyTest D univ :=
    ⟨U, hU, HasCompactSupport.of_compactSpace _, subset_univ _⟩
  refine ⟨(-(eigenvalue D univ i)⁻¹) • f, ?_⟩
  apply Lp.ext
  have hUae' : U =ᵐ[g.volumeMeasure.restrict univ]
      (eigenbasis D univ (by norm_num) isOpen_univ
        (by simpa using isCompact_univ) i : M → ℝ) :=
    hUae.filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [closedLaplacianToL2_ae D (-(eigenvalue D univ i)⁻¹ • f), hUae']
    with x hx hy
  rw [hx]
  change D.laplacian (fun y => -(eigenvalue D univ i)⁻¹ * U y) x = _
  rw [D.laplacian_const_mul]
  have he := hUeq x
  rw [← hy]
  field_simp
  nlinarith

theorem mem_closure_range_closedLaplacian_of_integral_eq_zero (D : LeviCivitaData g)
    (F : Lp ℝ 2 (g.volumeMeasure.restrict univ))
    (hF : (∫ x, F x ∂g.volumeMeasure) = 0) :
    F ∈ closure (Set.range (closedLaplacianToL2 D)) := by
  classical
  let b := eigenbasis D univ (by norm_num) isOpen_univ (by simpa using isCompact_univ)
  apply mem_closure_of_tendsto (b.hasSum_repr F)
  apply Eventually.of_forall
  intro s
  change ∑ i ∈ s, b.repr F i • b i ∈ LinearMap.range (closedLaplacianToL2 D)
  apply Submodule.sum_mem
  intro i _
  by_cases hi : eigenvalue D univ i = 0
  · have hz := eigenbasis_repr_eq_zero_of_eigenvalue_eq_zero D F hF i hi
    change b.repr F i = 0 at hz
    rw [hz, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (eigenbasis_mem_range_closedLaplacian D i hi)

end PoincareConjecture.LeviCivitaData.Dirichlet
