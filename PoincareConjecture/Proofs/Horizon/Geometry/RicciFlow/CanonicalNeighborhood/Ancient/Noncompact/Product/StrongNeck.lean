import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.FactorFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.Evolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.Normalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27SphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem exists_strongEvolvingNeck (C : M27SphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hεhalf : epsilon < 1 / 2)
    (x : M) : ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
  obtain ⟨hR, a, ha⟩ := C.exists_scalarNormalized_sphere ht x
  let R := (K.flow.connection t).scalarCurvature x
  let ℓ := scalarNormalizedCylinderLine R (C.identification.symm x).2 hR
  let b := a.prodCongr ℓ
  let Φ := centeredScalarNormalizedCylinderDiffeomorph a C.identification R hR x
  have hcenter : Φ (a.symm (C.identification.symm x).1, 0) = x := by
    change C.identification
      (a (a.symm (C.identification.symm x).1), (C.identification.symm x).2 + 0 / Real.sqrt R) = x
    rw [a.apply_symm_apply, zero_div, add_zero, Prod.mk.eta, C.identification.apply_symm_apply]
  have hscalar : R = (C.sphere.connection t).scalarCurvature (C.identification.symm x).1 := by
    simpa only [C.identification.apply_symm_apply] using
      (C.sphere.metric t).scalarCurvature_eq_of_line_product (K.flow.metric t)
        (C.sphere.connection t) (K.flow.connection t) C.identification
        (C.metric_transport t ht) (C.identification.symm x)
  have hmodel : ∀ u ∈ Ioc (-1 : ℝ) 0,
      (fun z v w => R * roundCylinderPullback (K.flow.metric (t + u / R)) Φ z v w) =
        EvolvingRoundCylinderMetric u := by
    intro u hu
    funext z v w
    have hdb (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) b z v =
          (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2 / Real.sqrt R) := by
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (Prod.map a ℓ) z v = _
      rw [mfderiv_prodMap (a.mdifferentiable (by simp) _)
        (ℓ.mdifferentiable (by simp) _)]
      change (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1,
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℓ z.2 v.2) = _
      rw [mfderiv_scalarNormalizedCylinderLine]
    have hdΦ (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.identification (b z)
            (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2 / Real.sqrt R) := by
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (C.identification ∘ b) z v = _
      rw [mfderiv_comp z (C.identification.mdifferentiable (by simp) _)
        (b.mdifferentiable (by simp) _)]
      exact congrArg (fun q =>
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.identification (b z) q) (hdb v)
    change R * (K.flow.metric (t + u / R)).inner (Φ z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z w) = _
    rw [hdΦ, hdΦ]
    change R * (K.flow.metric (t + u / R)).inner (C.identification (b z)) _ _ = _
    rw [C.metric_transport _ (add_nonpos ht (div_nonpos_of_nonpos_of_nonneg hu.2 hR.le))]
    change R * ((C.sphere.metric (t + u / R)).inner (a z.1)
      (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1) (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1) +
        (v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = _
    have he := RicciFlow.Splitting.round_surface_inner_backward C.sphereFlow
      C.sphere.round ht (C.identification.symm x).1 hu.2 (a z.1)
      (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1) (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1)
    dsimp only [sphereFlow] at he
    rw [← hscalar] at he
    rw [he, mul_add]
    have hline : R * ((v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = v.2 * w.2 := by
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hR.le]
      exact mul_div_cancel₀ _ hR.ne'
    rw [hline, ← mul_assoc, mul_comm R (1 - u), mul_assoc, ha]
    change (1 - u) * (2 * _) + v.2 * w.2 = 2 * (1 - u) * _ + v.2 * w.2
    rw [← mul_assoc, mul_comm (1 - u) 2]
    rfl
  obtain ⟨N, hN, _⟩ := exists_strongEvolvingNeck_of_exactCylinder K ht hε hεhalf
    x hR Φ (a.symm (C.identification.symm x).1) hcenter hmodel
  exact ⟨N, hN⟩

end PoincareConjecture.M27SphereLineFlowCertificate
