import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.RoundCover
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.IsometryLift
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder

/-!
# Sphere coordinates for the normalized compact round factor

The constructed sphere cover is either a diffeomorphism or identifies exactly
antipodal pairs. A free surface isometry excludes the second alternative.
In the diffeomorphism case the original metric is twice the pulled-back unit
round metric in one fixed system of sphere coordinates.

Reference: Morgan--Tian, Claim 9.45, pp. 208--209.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RicciFlow.Splitting

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- Inverting a bijective smooth round covering gives fixed sphere coordinates
and the original metric's exact factor-of-two pullback identity. -/
theorem exists_sphereDiffeomorph_of_bijective_round_cover
    (g : RiemannianMetric 2 M) (q : UnitTwoSphere → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) (hbij : Function.Bijective q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 2) (𝓡 2) q x u) (mfderiv (𝓡 2) (𝓡 2) q x v) =
        2 * (roundSphereMetric 2).inner x u v) :
    ∃ s : M ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere,
      ∀ x (u v : TangentSpace (𝓡 2) x),
        g.inner x u v = 2 * (roundSphereMetric 2).inner (s x)
          (mfderiv (𝓡 2) (𝓡 2) s x u) (mfderiv (𝓡 2) (𝓡 2) s x v) := by
  let e := hq.diffeomorphOfBijective hbij
  have hemetric (y : UnitTwoSphere) (a b : TangentSpace (𝓡 2) y) :
      g.inner (e y) (mfderiv (𝓡 2) (𝓡 2) e y a) (mfderiv (𝓡 2) (𝓡 2) e y b) =
        2 * (roundSphereMetric 2).inner y a b := hmetric y a b
  refine ⟨e.symm, ?_⟩
  intro x u v
  have hcomp : e ∘ e.symm = id := funext e.apply_symm_apply
  have hd := mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) _)
    (e.symm.contMDiff.mdifferentiable (by simp) x)
  rw [hcomp, mfderiv_id] at hd
  have hder (w : TangentSpace (𝓡 2) x) :
      mfderiv (𝓡 2) (𝓡 2) e (e.symm x)
        (mfderiv (𝓡 2) (𝓡 2) e.symm x w) = w := by
    exact congrArg (fun f => f w) hd.symm
  have hm := hemetric (e.symm x) (mfderiv (𝓡 2) (𝓡 2) e.symm x u)
    (mfderiv (𝓡 2) (𝓡 2) e.symm x v)
  rw [hder, hder, e.apply_symm_apply] at hm
  exact hm

variable [T2Space M] [T3Space M] [ConnectedSpace M] [CompactSpace M]

/-- A normalized compact round soliton surface has actual sphere coordinates
with metric factor two, or an actual cover with exactly antipodal fibers. -/
theorem normalized_round_surface_sphere_or_antipodal_cover
    {g : RiemannianMetric 2 M} (D : LeviCivitaData g) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 2) x,
      D.ricci x u v + D.hessian φ x u v = (1 / 2 : ℝ) * g.inner x u v)
    (hround : ConstantPositiveSectionalCurvature g D) :
    (∃ s : M ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere,
      ∀ x (u v : TangentSpace (𝓡 2) x),
        g.inner x u v = 2 * (roundSphereMetric 2).inner (s x)
          (mfderiv (𝓡 2) (𝓡 2) s x u) (mfderiv (𝓡 2) (𝓡 2) s x v)) ∨
    ∃ q : UnitTwoSphere → M,
      ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧ IsCoveringMap q ∧
      (∀ x (u v : TangentSpace (𝓡 2) x),
        g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
          (mfderiv (𝓡 2) (𝓡 2) q x v) = 2 * (roundSphereMetric 2).inner x u v) ∧
      ∀ x y, q x = q y ↔ y = x ∨ y = -x := by
  obtain ⟨q, hq, hsurj, hlocal, hcover, hmetric⟩ :=
    exists_unitSphere_two_covering_of_round_soliton D hφ hsol hround
  let h := rescaledMetric g (1 / 2) (by norm_num)
  have hunit (x : UnitSphere 2) (u v : TangentSpace (𝓡 2) x) :
      h.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
        (mfderiv (𝓡 2) (𝓡 2) q x v) = (roundSphereMetric 2).inner x u v := by
    change (1 / 2 : ℝ) * g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
      (mfderiv (𝓡 2) (𝓡 2) q x v) = _
    rw [hmetric]
    ring
  rcases orthogonalSurfaceDeckGroup_fiber_dichotomy h q hlocal hunit with hinj | hpair
  · exact Or.inl (exists_sphereDiffeomorph_of_bijective_round_cover
      g q hlocal ⟨hinj, hsurj⟩ hmetric)
  · exact Or.inr ⟨q, hq, hsurj, hlocal, hcover, hmetric, hpair⟩

/-- A free metric isometry on the actual normalized compact round surface
forces its constructed sphere cover to be a diffeomorphism. -/
theorem exists_sphereDiffeomorph_of_round_soliton_free_isometry
    {g : RiemannianMetric 2 M} (D : LeviCivitaData g) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 2) x,
      D.ricci x u v + D.hessian φ x u v = (1 / 2 : ℝ) * g.inner x u v)
    (hround : ConstantPositiveSectionalCurvature g D)
    (σ : M ≃ₘ⟮𝓡 2, 𝓡 2⟯ M)
    (hσ : ∀ x u v, g.inner (σ x)
      (mfderiv (𝓡 2) (𝓡 2) σ x u) (mfderiv (𝓡 2) (𝓡 2) σ x v) =
        g.inner x u v)
    (hfree : ∀ x, σ x ≠ x) :
    ∃ s : M ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere,
      ∀ x (u v : TangentSpace (𝓡 2) x),
        g.inner x u v = 2 * (roundSphereMetric 2).inner (s x)
          (mfderiv (𝓡 2) (𝓡 2) s x u) (mfderiv (𝓡 2) (𝓡 2) s x v) := by
  obtain ⟨q, _, hsurj, hlocal, _, hmetric⟩ :=
    exists_unitSphere_two_covering_of_round_soliton D hφ hsol hround
  let h := rescaledMetric g (1 / 2) (by norm_num)
  have hunit (x : UnitSphere 2) (u v : TangentSpace (𝓡 2) x) :
      h.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
        (mfderiv (𝓡 2) (𝓡 2) q x v) = (roundSphereMetric 2).inner x u v := by
    change (1 / 2 : ℝ) * g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
      (mfderiv (𝓡 2) (𝓡 2) q x v) = _
    rw [hmetric]
    ring
  have hisom (x : M) (u v : TangentSpace (𝓡 2) x) :
      h.inner (σ x) (mfderiv (𝓡 2) (𝓡 2) σ x u)
        (mfderiv (𝓡 2) (𝓡 2) σ x v) = h.inner x u v := by
    change (1 / 2 : ℝ) * g.inner (σ x) (mfderiv (𝓡 2) (𝓡 2) σ x u)
      (mfderiv (𝓡 2) (𝓡 2) σ x v) = (1 / 2 : ℝ) * g.inner x u v
    rw [hσ]
  have hinj := surface_cover_injective_of_free_isometry h q hlocal hsurj hunit σ hisom hfree
  exact exists_sphereDiffeomorph_of_bijective_round_cover g q hlocal ⟨hinj, hsurj⟩ hmetric

end PoincareMT.RicciFlow.Splitting
