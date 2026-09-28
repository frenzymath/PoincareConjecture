import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.RoundMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Quotient.ProductTransport








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle Topology
universe u
namespace PoincareConjecture.SphereLineProductData
variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]
  (B : SphereLineProductData (P := P))

local instance : TopologicalSpace B.surface := B.surface_topology
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) B.surface := B.surface_charted
local instance : IsManifold (𝓡 2) ∞ B.surface := B.surface_manifold
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (B.surface × ℝ) :=
  B.product_charted
local instance : IsManifold (𝓡 3) ∞ (B.surface × ℝ) := B.product_manifold

def canonicalProductDiffeomorph :
    (UnitTwoSphere × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ (B.surface × ℝ) := by
  let a : (B.surface × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ (B.surface × ℝ) :=
    { toEquiv := Equiv.refl _
      contMDiff_toFun := B.product_smooth_from_canonical
      contMDiff_invFun := B.product_smooth_to_canonical }
  exact (B.surface_sphere.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans a

@[simp] theorem canonicalProductDiffeomorph_apply (z : UnitTwoSphere × ℝ) :
    B.canonicalProductDiffeomorph z = (B.surface_sphere.symm z.1, z.2) := rfl

theorem canonicalProductDiffeomorph_inner (t : ℝ) (ht : t < 0)
    (z : UnitTwoSphere × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    (B.product_metric t).inner (B.canonicalProductDiffeomorph z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) B.canonicalProductDiffeomorph z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) B.canonicalProductDiffeomorph z w) =
        (-2 * t) * inner ℝ
          (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 v.1)
          (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 w.1) +
        v.2 * w.2 := by
  let e := B.canonicalProductDiffeomorph
  have hfst : ContMDiff (𝓡 3) (𝓡 2) ∞ (Prod.fst : B.surface × ℝ → B.surface) :=
    B.product_smooth_to_canonical.fst
  have hsnd : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Prod.snd : B.surface × ℝ → ℝ) :=
    B.product_smooth_to_canonical.snd
  have hvfst (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      B.tangent_surface_component (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a) =
      mfderiv (𝓡 2) (𝓡 2) B.surface_sphere.symm z.1 a.1 := by
    rw [B.tangent_surface_component_eq]
    have h := mfderiv_comp z (hfst.mdifferentiable (by simp) _)
      (e.contMDiff.mdifferentiable (by simp) z)
    have hcomp : (Prod.fst : B.surface × ℝ → B.surface) ∘ e =
        B.surface_sphere.symm ∘ Prod.fst := rfl
    rw [hcomp, mfderiv_comp z
      (B.surface_sphere.symm.contMDiff.mdifferentiable (by simp) z.1)
      mdifferentiableAt_fst, mfderiv_fst] at h
    exact congrArg (fun L => L a) h.symm
  have hvsnd (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      B.tangent_line_component (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a) = a.2 := by
    rw [B.tangent_line_component_eq]
    have h := mfderiv_comp z (hsnd.mdifferentiable (by simp) _)
      (e.contMDiff.mdifferentiable (by simp) z)
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd z = _ at h
    rw [mfderiv_snd] at h
    exact congrArg (fun L => L a) h.symm
  rw [B.product_inner_formula t ht, hvfst, hvfst, hvsnd, hvsnd]
  change (B.surface_metric t).inner (B.surface_sphere.symm z.1) _ _ + _ = _
  rw [B.surface_inner_round t ht]
  have hder (a : TangentSpace (𝓡 2) z.1) :
      mfderiv (𝓡 2) (𝓡 3) (fun x : B.surface => (B.surface_sphere x).1)
        (B.surface_sphere.symm z.1)
        (mfderiv (𝓡 2) (𝓡 2) B.surface_sphere.symm z.1 a) =
      mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 a := by
    have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun x : B.surface => (B.surface_sphere x).1) :=
      contMDiff_coe_sphere.comp B.surface_sphere.contMDiff
    have h := mfderiv_comp z.1 (hs.mdifferentiable (by simp) _)
      (B.surface_sphere.symm.contMDiff.mdifferentiable (by simp) z.1)
    have heq : (fun x : B.surface => (B.surface_sphere x).1) ∘ B.surface_sphere.symm =
        (fun x : UnitTwoSphere => x.1) := by
      funext x
      simp only [Function.comp_apply, B.surface_sphere.apply_symm_apply]
    rw [heq] at h
    exact congrArg (fun L => L a) h.symm
  rw [hder, hder]
end PoincareConjecture.SphereLineProductData
