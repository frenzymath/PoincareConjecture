import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Quotient.Topology








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

noncomputable section

universe u

namespace PoincareConjecture

theorem m27TwistedProductInvolution_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ∞ m27TwistedProductInvolution := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact (contMDiff_neg_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).prodMap
    (contMDiff_neg 𝓘(ℝ, ℝ) ∞ (G := ℝ))

theorem m27TwistedProductInvolution_free (p : UnitTwoSphere × ℝ) :
    m27TwistedProductInvolution p ≠ p := by
  intro h
  exact (ne_neg_of_mem_unit_sphere ℝ p.1) (congrArg Prod.fst h).symm

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}


def M27ProjectivePlaneLineFlowCertificate.ofCover
    (F : M27RoundSphereFamily) (q : UnitTwoSphere × ℝ → M)
    (hq : Function.Surjective q)
    (hd : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
    (hfib : ∀ p p', q p = q p' ↔ p' = p ∨ p' = (-p.1, p.2))
    (hmetric : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
      ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
        (K.flow.metric t).inner (q p)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p w) =
          F.productInner t p v w) : M27ProjectivePlaneLineFlowCertificate K := by
  let h := AncientCylinderQuotient.exists_projectivePlaneCoordinates q hq hd hfib
  let e := h.choose
  have he := h.choose_spec
  exact
    { sphere := F
      cover := q
      cover_surjective := hq
      cover_local_diffeomorph := hd
      cover_fibers := hfib
      product_homeomorph := e
      product_coordinates := he
      metric_transport := hmetric }


def M27TwistedSphereLineFlowCertificate.ofCover
    (F : M27RoundSphereFamily) (q : UnitTwoSphere × ℝ → M)
    (hq : Function.Surjective q)
    (hd : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
    (hfib : ∀ p p', q p = q p' ↔ p' = p ∨ p' = m27TwistedProductInvolution p)
    (hmetric : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
      ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
        (K.flow.metric t).inner (q p)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p w) =
          F.productInner t p v w) : M27TwistedSphereLineFlowCertificate K := by
  let h := AncientCylinderQuotient.exists_twistedProjectiveSmoothModel q hq hd hfib
  let e := h.choose
  let C := h.choose_spec.choose
  refine
    { sphere := F
      involution_smooth := m27TwistedProductInvolution_contMDiff
      involution_free := m27TwistedProductInvolution_free
      involution_isometry := ?_
      cover := q
      cover_surjective := hq
      cover_local_diffeomorph := hd
      cover_fibers := hfib
      metric_transport := hmetric
      puncture := twistedProjectivePuncture
      projective_topology := e
      projective_smooth_cover := C }
  intro t ht p v w
  have hcomp : q ∘ m27TwistedProductInvolution = q := by
    funext x
    exact ((hfib x (m27TwistedProductInvolution x)).mpr (Or.inr rfl)).symm
  have hder (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q (m27TwistedProductInvolution p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          m27TwistedProductInvolution p a) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p a := by
    rw [← mfderiv_comp_apply p (hd.mdifferentiable (by simp) _)
      (m27TwistedProductInvolution_contMDiff.mdifferentiable (by simp) _), hcomp]
  rw [← hmetric t ht, hder v, hder w]
  have hp := congrFun hcomp p
  change q (m27TwistedProductInvolution p) = q p at hp
  rw [hp]
  exact hmetric t ht p v w

end PoincareConjecture
