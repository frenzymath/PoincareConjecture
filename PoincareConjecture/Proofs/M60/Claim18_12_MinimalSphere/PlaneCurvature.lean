import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RicciTraceTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem m60SphereCurvatureContribution_plane (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f) (hc : M60WeaklyConformal g f)
    (z : LoopPlane) (hz : 0 < m60SphereAreaDensity g f z) :
    let v := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 3) (f ∘ m60SphereParameter) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
    D.curvatureTensor (f (m60SphereParameter z)) (v 0) (v 1) (v 0) (v 1) /
        m60SphereAreaDensity g f z =
      m60SphereCurvatureContribution D f (m60SphereParameter z) *
        (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  dsimp only
  let v := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 3) (f ∘ m60SphereParameter) z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hg (i j : Fin 2) : g.inner (f (m60SphereParameter z)) (v i) (v j) =
      if i = j then m60SphereAreaDensity g f z else 0 := by
    have h := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G i j)
      (m60AreaGram_eq_diagonal_of_weaklyConformal g f hf hc z)
    simpa only [m60AreaGram, Matrix.diagonal_apply, Function.comp_apply, v] using h
  have h00 : g.inner (f (m60SphereParameter z)) (v 0) (v 0) =
      m60SphereAreaDensity g f z := by simpa only [ite_true] using hg 0 0
  have h11 : g.inner (f (m60SphereParameter z)) (v 1) (v 1) =
      m60SphereAreaDensity g f z := by simpa only [ite_true] using hg 1 1
  have h01 : g.inner (f (m60SphereParameter z)) (v 0) (v 1) = 0 := by
    simpa using hg 0 1
  have htrace := m60Ricci_plane_trace_equal_length D hD _ _ _ hz h00 h11 h01
  have ht := m60SphereRicciTraceDensity_eq_intrinsic_mul D hD f hf hc z
  rw [m60SphereRicciTraceDensity_eq_of_weaklyConformal D hD f hf hc,
    Fin.sum_univ_two] at ht
  change D.ricci _ (v 0) (v 0) + D.ricci _ (v 1) (v 1) = _ at ht
  rw [m60SphereAreaDensity_eq_conformalFactor_mul g f hf hc] at htrace
  change D.curvatureTensor _ (v 0) (v 1) (v 0) (v 1) /
    m60SphereAreaDensity g f z = _
  rw [m60SphereAreaDensity_eq_conformalFactor_mul g f hf hc]
  unfold m60SphereCurvatureContribution
  dsimp only [Function.comp_apply] at ht ⊢
  nlinarith

end PoincareConjecture
