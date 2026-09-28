import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.Certificate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Quotient.Certificate










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {M N C : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N]
  [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) C]
  [IsManifold (𝓡 3) ∞ C]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)



def quotientSphereLineCertificateOfRawProduct
    (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (h : ℝ → RiemannianMetric 2 N) (D : ∀ t, LeviCivitaData (h t))
    (hround : ∀ t, t < 0 → ConstantPositiveSectionalCurvature (h t) (D t))
    (hinner : ∀ t, t < 0 → ∀ (p : N) (v w : TangentSpace (𝓡 2) p),
      (h t).inner p v w = (-2 * t) * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p v)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p w))
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C)
    (τ : C ≃ₘ⟮𝓡 3, 𝓡 3⟯ C)
    (hττ : Function.Involutive τ) (hfree : ∀ p, τ p ≠ p)
    (projection : C → M) (hprojection : ContMDiff (𝓡 3) (𝓡 3) ∞ projection)
    (hsurj : Function.Surjective projection)
    (hfiber : ∀ p q, projection p = projection q ↔ q = p ∨ q = τ p)
    (hraw : ∀ t : ℝ, t < 0 → ∀ (z : N × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (G.flow.metric t).inner ((projection ∘ e) z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (projection ∘ e) z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (projection ∘ e) z w) =
          (-2 * t) * inner ℝ
            (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) z.1 v.1)
            (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) z.1 w.1) +
          v.2 * w.2) :
    QuotientSphereLineCertificate G := by
  let d := sphereLineProductDataOfSurface s h D hround hinner e.symm
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N × ℝ) :=
    RiemannianMetric.lineProductChartedSpace (n := 2) (M := N)
  let : IsManifold (𝓡 3) ∞ (N × ℝ) :=
    RiemannianMetric.lineProductIsManifold (n := 2) (M := N)
  let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)
  let b : (N × ℝ) ≃ₘ⟮𝓡 3, 𝓡 3⟯ C := a.symm.trans e
  let deck : (N × ℝ) ≃ₘ⟮𝓡 3, 𝓡 3⟯ (N × ℝ) := b.trans (τ.trans b.symm)
  let q : N × ℝ → M := projection ∘ b
  have hq : ContMDiff (𝓡 3) (𝓡 3) ∞ q := hprojection.comp b.contMDiff
  have hdeck (z : N × ℝ) : deck z = b.symm (τ (b z)) := rfl
  have hdeckdeck : Function.Involutive deck := by
    intro z
    rw [hdeck, hdeck, b.apply_symm_apply, hττ, b.symm_apply_apply]
  have hdeckfree (z : N × ℝ) : deck z ≠ z := by
    intro heq
    have he := congrArg b heq
    rw [hdeck, b.apply_symm_apply] at he
    exact hfree (b z) he
  have hqfiber (z w : N × ℝ) : q z = q w ↔ w = z ∨ w = deck z := by
    change projection (b z) = projection (b w) ↔ _
    rw [hfiber]
    constructor
    · rintro (he | he)
      · exact Or.inl (b.injective he)
      · right
        apply b.injective
        change b w = b (deck z)
        rw [hdeck, b.apply_symm_apply]
        exact he
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (b.apply_symm_apply _)
  have hba (z : N × ℝ) : b (a z) = e z := by
    change e (a.symm (a z)) = e z
    rw [a.symm_apply_apply]
  have hcomp : q ∘ a = projection ∘ e := by
    funext z
    change projection (b (a z)) = projection (e z)
    rw [hba]
  apply d.quotientCertificateOfProjection G deck deck.contMDiff hdeckdeck hdeckfree q hq
    (hsurj.comp b.surjective) hqfiber
  intro t ht p v w
  obtain ⟨z, rfl⟩ := a.surjective p
  let L := a.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) z
  obtain ⟨v', hv⟩ := L.surjective v
  obtain ⟨w', hw⟩ := L.surjective w
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) a z v' = v at hv
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) a z w' = w at hw
  rw [← hv, ← hw]
  have hderiv (u : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv (𝓡 3) (𝓡 3) q (a z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) a z u) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (projection ∘ e) z u := by
    have he := mfderiv_comp z (hq.mdifferentiable (by simp) (a z))
      (a.contMDiff.mdifferentiable (by simp) z)
    rw [hcomp] at he
    exact (congrArg (fun T => T u) he).symm
  change (h t).lineProduct.inner (a z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) a z v')
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) a z w') = _
  rw [RiemannianMetric.lineProduct_inner]
  change (h t).inner z.1 v'.1 w'.1 + v'.2 * w'.2 =
    (G.flow.metric t).inner (q (a z))
      (mfderiv (𝓡 3) (𝓡 3) q (a z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) a z v'))
      (mfderiv (𝓡 3) (𝓡 3) q (a z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) a z w'))
  rw [hderiv, hderiv]
  change (h t).inner z.1 v'.1 w'.1 + v'.2 * w'.2 =
    (G.flow.metric t).inner (projection (b (a z))) _ _
  rw [hba, hinner t ht]
  exact (hraw t ht z v' w').symm

end PoincareConjecture.RicciFlow.Splitting
