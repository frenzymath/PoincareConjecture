import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.IntrinsicRicciTrace










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem m60SphereCurvatureContribution_eq_of_pos (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hc : M60WeaklyConformal g f) (p : UnitTwoSphere)
    (hp : 0 < m60SphereConformalFactor g f p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
      ⟨m60RoundSphereMetric.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) p),
      m60SphereCurvatureContribution D f p =
        D.curvatureTensor (f p)
          (mfderiv (𝓡 2) (𝓡 3) f p (b 0)) (mfderiv (𝓡 2) (𝓡 3) f p (b 1))
          (mfderiv (𝓡 2) (𝓡 3) f p (b 0)) (mfderiv (𝓡 2) (𝓡 3) f p (b 1)) /
            m60SphereConformalFactor g f p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨m60RoundSphereMetric.toRiemannianMetric⟩
  intro b
  have hinner (i j : Fin 2) :
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 3) f p (b i)) (mfderiv (𝓡 2) (𝓡 3) f p (b j)) =
        m60SphereConformalFactor g f p * (if i = j then 1 else 0) := by
    rw [m60SphereConformalFactor_spec g f hc]
    congr 1
    exact b.inner_eq_ite i j
  have h0 : g.inner (f p) (mfderiv (𝓡 2) (𝓡 3) f p (b 0))
      (mfderiv (𝓡 2) (𝓡 3) f p (b 0)) = m60SphereConformalFactor g f p := by
    simpa only [ite_true, mul_one] using hinner 0 0
  have h1 : g.inner (f p) (mfderiv (𝓡 2) (𝓡 3) f p (b 1))
      (mfderiv (𝓡 2) (𝓡 3) f p (b 1)) = m60SphereConformalFactor g f p := by
    simpa only [ite_true, mul_one] using hinner 1 1
  have h01 : g.inner (f p) (mfderiv (𝓡 2) (𝓡 3) f p (b 0))
      (mfderiv (𝓡 2) (𝓡 3) f p (b 1)) = 0 := by
    simpa using hinner 0 1
  have h := m60Ricci_plane_trace_equal_length D hD (f p) _ _ hp h0 h1 h01
  unfold m60SphereCurvatureContribution
  rw [m60SphereIntrinsicRicciTrace_eq_basis D hD f p b, Fin.sum_univ_two]
  linarith

omit [T2Space M] in



theorem m60SphereCurvatureContribution_eq_zero_of_branch (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M) (p : UnitTwoSphere)
    (hp : p ∈ m60SphereBranchSet (n := 3) f) :
    m60SphereCurvatureContribution D f p = 0 := by
  change mfderiv (𝓡 2) (𝓡 3) f p = 0 at hp
  obtain ⟨B, hB⟩ := m60Ricci_exists_bilinear D hD (f p)
  have hzero : D.ricci (f p) 0 0 = 0 := by rw [← hB]; simp
  simp only [m60SphereCurvatureContribution, m60SphereIntrinsicRicciTrace,
    RiemannianMetric.tensorTrace, M60.tensorPullbackEvaluation,
    LeviCivitaData.ricciEvaluation, hp, zero_apply, hzero, Finset.sum_const_zero,
    m60SphereConformalFactor, map_zero, mul_zero, sub_zero]

end PoincareConjecture
