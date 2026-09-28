import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.RoundMetric









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow.Splitting

variable {N C : Type*} [TopologicalSpace N] [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) C] [IsManifold (𝓡 3) ∞ C]

theorem lineCoordinate_derivative_in_product
    {r : C → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C)
    (hcoord : ∀ x, (e.symm x).2 = r x)
    (z : N × ℝ) (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    mvfderiv (𝓡 3) r (e z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a) = a.2 := by
  have hcomp : r ∘ e = (Prod.snd : N × ℝ → ℝ) := by
    funext y
    exact (hcoord (e y)).symm.trans (congrArg Prod.snd (e.symm_apply_apply y))
  have hd := mfderiv_comp z (hr.mdifferentiable (by simp) _)
    (e.contMDiff.mdifferentiable (by simp) z)
  rw [hcomp, mfderiv_snd] at hd
  exact congrArg (fun L => L a) hd.symm

theorem product_inner_of_transverse_scale
    (F : ℝ → RiemannianMetric 3 C) (g : RiemannianMetric 3 C)
    (h : RiemannianMetric 2 N)
    {r : C → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C)
    (hcoord : ∀ x, (e.symm x).2 = r x)
    (hinitial : ∀ (z : N × ℝ)
      (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      g.inner (e z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
          h.inner z.1 a.1 b.1 + a.2 * b.2)
    (hscale : ∀ t, t < 0 → ∀ (x : C) (a b : TangentSpace (𝓡 3) x),
      (F t).inner x a b = (-t) * (g.inner x a b -
        mvfderiv (𝓡 3) r x a * mvfderiv (𝓡 3) r x b) +
          mvfderiv (𝓡 3) r x a * mvfderiv (𝓡 3) r x b)
    (t : ℝ) (ht : t < 0) (z : N × ℝ)
    (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    (F t).inner (e z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
        (-t) * h.inner z.1 a.1 b.1 + a.2 * b.2 := by
  rw [hscale t ht, hinitial,
    lineCoordinate_derivative_in_product hr e hcoord z a,
    lineCoordinate_derivative_in_product hr e hcoord z b]
  ring

theorem RoundCylinderSurface.inner_eq_neg_time_mul
    (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (h : RiemannianMetric 2 N)
    (hs : ∀ x (a b : TangentSpace (𝓡 2) x),
      h.inner x a b = 2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
        (s x) (mfderiv (𝓡 2) (𝓡 2) s x a) (mfderiv (𝓡 2) (𝓡 2) s x b))
    (t : ℝ) (ht : t < 0) (x : N) (a b : TangentSpace (𝓡 2) x) :
    (RoundCylinderSurface.metric s t).inner x a b = (-t) * h.inner x a b := by
  change RoundCylinderSurface.scale t *
    (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner (s x)
      (mfderiv (𝓡 2) (𝓡 2) s x a) (mfderiv (𝓡 2) (𝓡 2) s x b) = _
  rw [RoundCylinderSurface.scale, if_pos ht, hs]
  ring

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem product_pullback_inner_of_transverse_scale
    (F : ℝ → RiemannianMetric 3 M) (g : RiemannianMetric 3 C)
    (h : RiemannianMetric 2 N)
    {r : C → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C)
    (hcoord : ∀ x, (e.symm x).2 = r x)
    (projection : C → M) (hp : ContMDiff (𝓡 3) (𝓡 3) ∞ projection)
    (hinitial : ∀ (z : N × ℝ)
      (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      g.inner (e z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
          h.inner z.1 a.1 b.1 + a.2 * b.2)
    (hscale : ∀ t, t < 0 → ∀ (x : C) (a b : TangentSpace (𝓡 3) x),
      (F t).inner (projection x) (mfderiv (𝓡 3) (𝓡 3) projection x a)
        (mfderiv (𝓡 3) (𝓡 3) projection x b) = (-t) * (g.inner x a b -
        mvfderiv (𝓡 3) r x a * mvfderiv (𝓡 3) r x b) +
          mvfderiv (𝓡 3) r x a * mvfderiv (𝓡 3) r x b)
    (t : ℝ) (ht : t < 0) (z : N × ℝ)
    (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    (F t).inner ((projection ∘ e) z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (projection ∘ e) z a)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (projection ∘ e) z b) =
        (-t) * h.inner z.1 a.1 b.1 + a.2 * b.2 := by
  rw [mfderiv_comp z (hp.mdifferentiable (by simp) _)
    (e.contMDiff.mdifferentiable (by simp) z)]
  change (F t).inner (projection (e z))
    (mfderiv (𝓡 3) (𝓡 3) projection (e z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a))
    (mfderiv (𝓡 3) (𝓡 3) projection (e z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b)) = _
  rw [hscale t ht, hinitial,
    lineCoordinate_derivative_in_product hr e hcoord z a,
    lineCoordinate_derivative_in_product hr e hcoord z b]
  ring

end PoincareConjecture.RicciFlow.Splitting
