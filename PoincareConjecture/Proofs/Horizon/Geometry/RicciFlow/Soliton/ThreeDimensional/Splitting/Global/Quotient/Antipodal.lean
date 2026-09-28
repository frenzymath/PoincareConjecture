import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Quotient.ProductTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.RoundMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Lift
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.SphereMotions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {M N : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N]
  {S : GradientShrinkingSolitonData 3 M}

def quotientSphereLineCertificateOfAntipodalSurface
    (G : ShrinkingSolitonFlow S) (g : RiemannianMetric 2 N)
    (q : UnitTwoSphere → N) (hq : ContMDiff (𝓡 2) (𝓡 2) ∞ q)
    (hsurj : Function.Surjective q)
    (hpair : ∀ x y, q x = q y ↔ y = x ∨ y = -x)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 2) x),
      g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
        (mfderiv (𝓡 2) (𝓡 2) q x w) = 2 * (roundSphereMetric 2).inner x v w)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hflow : ∀ t : ℝ, t < 0 → ∀ (z : N × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (G.flow.metric t).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          (-t) * g.inner z.1 v.1 w.1 + v.2 * w.2) :
    QuotientSphereLineCertificate G := by
  let B := ULift.{u} UnitTwoSphere
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) B :=
    Poincare.Manifold.uliftChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let : IsManifold (𝓡 2) ∞ B := Poincare.Manifold.uliftIsManifold (𝓡 2) UnitTwoSphere
  let s : B ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere :=
    Poincare.Manifold.uliftDiffeomorph (𝓡 2) UnitTwoSphere
  let neg : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere :=
    sphereMotion (LinearIsometryEquiv.neg ℝ)
  have hneg (x : UnitTwoSphere) : neg x = -x := Subtype.ext rfl
  let σ : B ≃ₘ⟮𝓡 2, 𝓡 2⟯ B := (s.trans neg).trans s.symm
  have hσ (x : B) : s (σ x) = -(s x) := by
    change s (s.symm (neg (s x))) = _
    rw [s.apply_symm_apply, hneg]
  have hσσ : Function.Involutive σ := by
    intro x
    apply s.injective
    change s (σ (σ x)) = s x
    rw [hσ, hσ, neg_neg]
  have hσfree (x : B) : σ x ≠ x := by
    intro heq
    have he := congrArg s heq
    rw [hσ] at he
    have hz : (s x).val = 0 := by
      ext i
      have hi := congrArg (fun z : UnitTwoSphere => z.val i) he
      change -(s x).val i = (s x).val i at hi
      change (s x).val i = 0
      linarith
    have hn := (s x).property
    simp only [Metric.mem_sphere, dist_zero_right, hz, norm_zero] at hn
    norm_num at hn
  let T := σ.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hTT : Function.Involutive T := by
    intro z
    exact Prod.ext (hσσ z.1) rfl
  have hTfree (z : B × ℝ) : T z ≠ z := by
    intro heq
    exact hσfree z.1 (congrArg Prod.fst heq)
  let r : B → N := q ∘ s
  have hr : ContMDiff (𝓡 2) (𝓡 2) ∞ r := hq.comp s.contMDiff
  let f : B × ℝ → N × ℝ := Prod.map r id
  have hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f :=
    hr.prodMap contMDiff_id
  let j : B × ℝ → M := e ∘ f
  have hj : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ j := e.contMDiff.comp hf
  have hjsurj : Function.Surjective j :=
    e.surjective.comp ((hsurj.comp s.surjective).prodMap Function.surjective_id)
  have hjfiber (z w : B × ℝ) : j z = j w ↔ w = z ∨ w = T z := by
    change e (r z.1, z.2) = e (r w.1, w.2) ↔ _
    have hcancel : e (r z.1, z.2) = e (r w.1, w.2) ↔
        (r z.1, z.2) = (r w.1, w.2) :=
      ⟨fun he => e.injective he, fun he => congrArg e he⟩
    rw [hcancel, Prod.mk.injEq]
    constructor
    · rintro ⟨he, hz⟩
      rcases (hpair (s z.1) (s w.1)).mp he with hs | hs
      · exact Or.inl (Prod.ext (s.injective hs) hz.symm)
      · right
        exact Prod.ext (s.injective (hs.trans (hσ z.1).symm)) hz.symm
    · rintro (rfl | rfl)
      · exact ⟨rfl, rfl⟩
      · exact ⟨(hpair (s z.1) (s (σ z.1))).mpr (Or.inr (hσ z.1)), rfl⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (B × ℝ) :=
    RiemannianMetric.lineProductChartedSpace (n := 2) (M := B)
  let : IsManifold (𝓡 3) ∞ (B × ℝ) :=
    RiemannianMetric.lineProductIsManifold (n := 2) (M := B)
  let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := B)
  let τ : (B × ℝ) ≃ₘ⟮𝓡 3, 𝓡 3⟯ (B × ℝ) := (a.symm.trans T).trans a
  have hτ (z : B × ℝ) : τ z = a (T (a.symm z)) := rfl
  have hττ : Function.Involutive τ := by
    intro z
    rw [hτ, hτ, a.symm_apply_apply, hTT, a.apply_symm_apply]
  have hτfree (z : B × ℝ) : τ z ≠ z := by
    intro heq
    have he := congrArg a.symm heq
    rw [hτ, a.symm_apply_apply] at he
    exact hTfree (a.symm z) he
  let projection : B × ℝ → M := j ∘ a.symm
  have hprojection : ContMDiff (𝓡 3) (𝓡 3) ∞ projection :=
    hj.comp a.symm.contMDiff
  have hpfiber (z w : B × ℝ) : projection z = projection w ↔ w = z ∨ w = τ z := by
    change j (a.symm z) = j (a.symm w) ↔ _
    rw [hjfiber]
    constructor
    · rintro (he | he)
      · exact Or.inl (a.symm.injective he)
      · right
        apply a.symm.injective
        change a.symm w = a.symm (τ z)
        rw [hτ, a.symm_apply_apply]
        exact he
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · right
        rw [hτ, a.symm_apply_apply]
  have hcomp : projection ∘ a = j := by
    funext z
    change j (a.symm (a z)) = j z
    rw [a.symm_apply_apply]
  apply quotientSphereLineCertificateOfRawProduct G s
    (RoundCylinderSurface.metric s) (RoundCylinderSurface.connection s)
    (fun t _ => RoundCylinderSurface.round s t) (RoundCylinderSurface.inner s)
    a τ hττ hτfree projection hprojection (hjsurj.comp a.symm.surjective) hpfiber
  intro t ht z v w
  change EuclideanSpace ℝ (Fin 2) × ℝ at v w
  rw [hcomp]
  change (G.flow.metric t).inner ((e ∘ f) z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (e ∘ f) z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (e ∘ f) z w) = _
  rw [mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _)
    (hf.mdifferentiable (by simp) z)]
  change (G.flow.metric t).inner (e (f z))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (f z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f z v))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (f z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f z w)) = _
  rw [hflow t ht]
  change (-t) * g.inner (q (s z.1))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Prod.map r id) z v).1
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Prod.map r id) z w).1 +
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Prod.map r id) z v).2 *
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Prod.map r id) z w).2 = _
  rw [mfderiv_prodMap (hr.mdifferentiable (by simp) z.1) mdifferentiableAt_id, mfderiv_id]
  change (-t) * g.inner (q (s z.1))
    (mfderiv (𝓡 2) (𝓡 2) (q ∘ s) z.1 v.1)
    (mfderiv (𝓡 2) (𝓡 2) (q ∘ s) z.1 w.1) + v.2 * w.2 = _
  rw [mfderiv_comp z.1 (hq.mdifferentiable (by simp) _)
    (s.contMDiff.mdifferentiable (by simp) _)]
  change (-t) * g.inner (q (s z.1))
    (mfderiv (𝓡 2) (𝓡 2) q (s z.1) (mfderiv (𝓡 2) (𝓡 2) s z.1 v.1))
    (mfderiv (𝓡 2) (𝓡 2) q (s z.1) (mfderiv (𝓡 2) (𝓡 2) s z.1 w.1)) +
      v.2 * w.2 = _
  erw [hmetric, roundSphereMetric_inner]
  have hd := mfderiv_comp z.1
    ((contMDiff_coe_sphere (m := ∞) (n := 2)).mdifferentiable (by simp) _)
    (s.contMDiff.mdifferentiable (by simp) _)
  change mfderiv (𝓡 2) (𝓡 3) (fun y : B => (s y).1) z.1 = _ at hd
  rw [hd]
  simp only [RiemannianMetric.euclideanMetric_inner, ContinuousLinearMap.comp_apply]
  ring

end PoincareConjecture.RicciFlow.Splitting
