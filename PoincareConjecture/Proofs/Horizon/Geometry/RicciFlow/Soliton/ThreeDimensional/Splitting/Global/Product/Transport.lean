import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.Certificate







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {M N : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)



def productSphereLineCertificateOfRawProduct
    (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (h : ℝ → RiemannianMetric 2 N) (D : ∀ t, LeviCivitaData (h t))
    (hround : ∀ t, t < 0 → ConstantPositiveSectionalCurvature (h t) (D t))
    (hinner : ∀ t, t < 0 → ∀ (p : N) (v w : TangentSpace (𝓡 2) p),
      (h t).inner p v w = (-2 * t) * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p v)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p w))
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hraw : ∀ t : ℝ, t < 0 → ∀ (z : N × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (G.flow.metric t).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          (h t).inner z.1 v.1 w.1 + v.2 * w.2) :
    SphereLineProductCertificate G := by
  apply sphereLineProductCertificateOfSurface G s h D hround hinner e.symm
  intro t ht p v w
  obtain ⟨z, rfl⟩ := e.surjective p
  let L := e.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) z
  obtain ⟨v', hv⟩ := L.surjective v
  obtain ⟨w', hw⟩ := L.surjective w
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v' = v at hv
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w' = w at hw
  have hinverse (u : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z u) = u := by
    have he := mfderiv_comp z (e.symm.contMDiff.mdifferentiable (by simp) (e z))
      (e.contMDiff.mdifferentiable (by simp) z)
    have hcomp : e.symm ∘ e = id := funext e.symm_apply_apply
    rw [hcomp, mfderiv_id] at he
    exact (congrArg (fun T => T u) he).symm
  rw [← hv, ← hw]
  change (G.flow.metric t).inner (e z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v')
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w') =
      (h t).inner (e.symm (e z)).1
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v')).1
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w')).1 +
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v')).2 *
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w')).2
  rw [hinverse, hinverse, e.symm_apply_apply]
  exact hraw t ht z v' w'

end PoincareConjecture.RicciFlow.Splitting
