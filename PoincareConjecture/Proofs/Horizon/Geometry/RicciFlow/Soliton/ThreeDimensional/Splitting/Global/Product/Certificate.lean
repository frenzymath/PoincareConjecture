import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.Orientation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]

local instance : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) (N × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 2)) N ℝ ℝ

local instance : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 1))) (N × ℝ) :=
  RiemannianMetric.lineProductChartedSpace (n := 2) (M := N)

local instance : IsManifold (𝓡 (2 + 1)) ∞ (N × ℝ) :=
  RiemannianMetric.lineProductIsManifold (n := 2) (M := N)

omit [IsManifold (𝓡 2) ∞ N] in
private theorem cast_product_diffeomorph_apply
    (I J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)
      (EuclideanSpace ℝ (Fin 2) × ℝ)) (hIJ : I = J)
    (f : (N × ℝ) ≃ₘ⟮I, 𝓡 (2 + 1)⟯ (N × ℝ)) (p : N × ℝ) :
    (cast (congrArg (fun K => (N × ℝ) ≃ₘ⟮K, 𝓡 (2 + 1)⟯ (N × ℝ)) hIJ) f) p = f p := by
  subst J
  rfl

private theorem lineProductDiffeomorph_apply (p : N × ℝ) :
    RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N) p = p := by
  unfold RiemannianMetric.lineProductDiffeomorph
  exact cast_product_diffeomorph_apply _ _ modelWithCornersSelf_prod _ p

private theorem lineProductDiffeomorph_symm_apply (p : N × ℝ) :
    (RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)).symm p = p := by
  let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)
  exact (lineProductDiffeomorph_apply (a.symm p)).symm.trans (a.apply_symm_apply p)

private theorem lineProductDiffeomorph_coe :
    (RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N) : N × ℝ → N × ℝ) = id :=
  funext lineProductDiffeomorph_apply

private theorem lineProductDiffeomorph_symm_coe :
    ((RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)).symm : N × ℝ → N × ℝ) = id :=
  funext lineProductDiffeomorph_symm_apply

private def productTangentComponents (p : N × ℝ) :
    TangentSpace (𝓡 3) p →L[ℝ] (TangentSpace (𝓡 2) p.1 × ℝ) :=
  mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)).symm p

private theorem productTangentComponents_fst (p : N × ℝ)
    (v : TangentSpace (𝓡 3) p) :
    (productTangentComponents p v).1 =
      mfderiv (𝓡 3) (𝓡 2) (Prod.fst : N × ℝ → N) p v := by
  let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)
  have h := mfderiv_comp p mdifferentiableAt_fst
    (a.symm.contMDiff.mdifferentiable (by simp) p)
  rw [mfderiv_fst] at h
  have hid : (Prod.fst : N × ℝ → N) ∘ a.symm = Prod.fst := by
    funext z
    rw [Function.comp_apply, lineProductDiffeomorph_symm_apply]
  rw [hid] at h
  exact (congrArg (fun L => L v) h).symm

private theorem productTangentComponents_snd (p : N × ℝ)
    (v : TangentSpace (𝓡 3) p) :
    (productTangentComponents p v).2 =
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (Prod.snd : N × ℝ → ℝ) p v := by
  let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)
  have h := mfderiv_comp p mdifferentiableAt_snd
    (a.symm.contMDiff.mdifferentiable (by simp) p)
  rw [mfderiv_snd] at h
  have hid : (Prod.snd : N × ℝ → ℝ) ∘ a.symm = Prod.snd := by
    funext z
    rw [Function.comp_apply, lineProductDiffeomorph_symm_apply]
  rw [hid] at h
  exact (congrArg (fun L => L v) h).symm

private theorem productTangentComponents_surjective (p : N × ℝ) :
    Function.Surjective (productTangentComponents p) := by
  let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)
  exact (a.symm.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) p).surjective

private theorem lineProduct_inner_components (h : RiemannianMetric 2 N)
    (p : N × ℝ) (u v : TangentSpace (𝓡 3) p) :
    h.lineProduct.inner p u v =
      h.inner p.1 (productTangentComponents p u).1 (productTangentComponents p v).1 +
        (productTangentComponents p u).2 * (productTangentComponents p v).2 := by
  change (RiemannianMetric.product h RiemannianMetric.realLineMetric).inner
    ((RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)).symm p)
    (productTangentComponents p u) (productTangentComponents p v) = _
  rw [RiemannianMetric.product_inner]
  rw [lineProductDiffeomorph_symm_apply]
  change h.inner p.1 (productTangentComponents p u).1 (productTangentComponents p v).1 +
    inner ℝ (productTangentComponents p u).2 (productTangentComponents p v).2 = _
  simp only [RCLike.inner_apply, conj_trivial]
  ring

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]

def sphereLineProductDataOfSurface
    (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (h : ℝ → RiemannianMetric 2 N) (D : ∀ t, LeviCivitaData (h t))
    (hround : ∀ t, t < 0 → ConstantPositiveSectionalCurvature (h t) (D t))
    (hinner : ∀ t, t < 0 → ∀ (p : N) (u v : TangentSpace (𝓡 2) p),
      (h t).inner p u v = (-2 * t) * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p u)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p v))
    (e : P ≃ₘ⟮𝓡 3, (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (N × ℝ)) :
    SphereLineProductData (P := P) where
  surface := N
  surface_topology := inferInstance
  surface_charted := inferInstance
  surface_manifold := inferInstance
  surface_sphere := s
  surface_metric := h
  surface_connection := D
  surface_round := hround
  surface_inner_round := hinner
  product_charted := RiemannianMetric.lineProductChartedSpace (n := 2) (M := N)
  product_manifold := RiemannianMetric.lineProductIsManifold (n := 2) (M := N)
  product_smooth_to_canonical := by
    simpa only [lineProductDiffeomorph_symm_coe] using
      (RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)).symm.contMDiff
  product_smooth_from_canonical := by
    simpa only [lineProductDiffeomorph_coe] using
      (RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)).contMDiff
  product_metric t := (h t).lineProduct
  product_connection t := RiemannianMetric.leviCivitaData ((h t).lineProduct)
  orientation := lineProductSmoothOrientation s
  product_equiv := e.trans (RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N))
  tangent_surface_component p v := (productTangentComponents p v).1
  tangent_line_component p v := (productTangentComponents p v).2
  tangent_surface_component_eq := productTangentComponents_fst
  tangent_line_component_eq := productTangentComponents_snd
  tangent_components_surjective := productTangentComponents_surjective
  product_inner_formula t _ := lineProduct_inner_components (h t)

@[simp] theorem sphereLineProductDataOfSurface_equiv_apply
    (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (h : ℝ → RiemannianMetric 2 N) (D : ∀ t, LeviCivitaData (h t))
    (hround : ∀ t, t < 0 → ConstantPositiveSectionalCurvature (h t) (D t))
    (hinner : ∀ t, t < 0 → ∀ (p : N) (u v : TangentSpace (𝓡 2) p),
      (h t).inner p u v = (-2 * t) * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p u)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p v))
    (e : P ≃ₘ⟮𝓡 3, (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (N × ℝ)) (p : P) :
    (sphereLineProductDataOfSurface s h D hround hinner e).product_equiv p = e p :=
  lineProductDiffeomorph_apply (e p)

variable [MeasurableSpace P] [BorelSpace P] [T2Space P] [T3Space P]
  [SecondCountableTopology P] [ConnectedSpace P]

def sphereLineProductCertificateOfSurface
    {S : GradientShrinkingSolitonData 3 P} (G : ShrinkingSolitonFlow S)
    (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (h : ℝ → RiemannianMetric 2 N) (D : ∀ t, LeviCivitaData (h t))
    (hround : ∀ t, t < 0 → ConstantPositiveSectionalCurvature (h t) (D t))
    (hinner : ∀ t, t < 0 → ∀ (p : N) (u v : TangentSpace (𝓡 2) p),
      (h t).inner p u v = (-2 * t) * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p u)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : N => (s x).1) p v))
    (e : P ≃ₘ⟮𝓡 3, (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (N × ℝ))
    (hflow : ∀ t, t < 0 → ∀ (p : P) (u v : TangentSpace (𝓡 3) p),
      (G.flow.metric t).inner p u v =
        (h t).inner (e p).1
          (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p u).1
          (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p v).1 +
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p u).2 *
          (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p v).2) :
    SphereLineProductCertificate G where
  toSphereLineProductData := sphereLineProductDataOfSurface s h D hround hinner e
  flow_isometric_to_product t ht p u v := by
    let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)
    change (G.flow.metric t).inner p u v = (h t).lineProduct.inner ((a ∘ e) p)
      (mfderiv (𝓡 3) (𝓡 3) (a ∘ e) p u) (mfderiv (𝓡 3) (𝓡 3) (a ∘ e) p v)
    rw [mfderiv_comp p (a.contMDiff.mdifferentiable (by simp) (e p))
      (e.contMDiff.mdifferentiable (by simp) p)]
    exact (hflow t ht p u v).trans
      (RiemannianMetric.lineProduct_inner (h t) (e p)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p u)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p v)).symm

end PoincareConjecture.RicciFlow.Splitting
