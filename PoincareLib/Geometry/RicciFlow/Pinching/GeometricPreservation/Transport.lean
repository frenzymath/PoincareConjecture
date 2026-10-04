import PoincareLib.Geometry.RicciFlow.Frame.Transport.Smooth
import PoincareLib.Geometry.RicciFlow.Frame.Evolution

/-!
# Smooth transport for geometric pinching

The canonical transport has both the joint regularity needed for the spatial
connection and the moving-input curvature equation. The latter retains the
rough Laplacian and all four quadratic curvature contractions.

Reference: Morgan--Tian, Claim 3.16, p. 42; Proposition 3.19, p. 44;
Theorem 4.8, p. 66.
-/

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- The jointly smooth canonical transport satisfies the retained curvature PDE. -/
theorem canonicalTransport_hasDerivAt_curvature
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Ico a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt
      (fun s => (F.connection s).curvatureTensor x
        (canonicalTransport F s x u) (canonicalTransport F s x v)
        (canonicalTransport F s x w) (canonicalTransport F s x z))
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![canonicalTransport F t x u, canonicalTransport F t x v,
            canonicalTransport F t x w, canonicalTransport F t x z] +
        2 * ((F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x v)
            (canonicalTransport F t x w) (canonicalTransport F t x z) -
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x v)
            (canonicalTransport F t x z) (canonicalTransport F t x w) -
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x z)
            (canonicalTransport F t x v) (canonicalTransport F t x w) +
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x w)
            (canonicalTransport F t x v) (canonicalTransport F t x z))) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  have hinput (q : TangentSpace (𝓡 n) x) :
      HasDerivWithinAt (fun s => canonicalTransport F s x q)
        (ricciSharp (F.connection t) x (canonicalTransport F t x q)) (Ico a b) t := by
    have h := (canonicalTransport_hasDerivWithinAt F ⟨ht.1.le, ht.2⟩ x).clm_apply
      (hasDerivWithinAt_const t (Ico a b) q)
    simpa only [map_zero, add_zero, ContinuousLinearMap.comp_apply,
      ricciEndomorphism_eq_sum F x ⟨ht.1.le, ht.2⟩, ricciSharp] using h
  have hinterior : t ∈ interior (Ico a b) := by simpa only [interior_Ico] using ht
  exact (hasDerivWithinAt_curvature_moving_inputs hC F hinterior x
    (fun s => canonicalTransport F s x u) (fun s => canonicalTransport F s x v)
    (fun s => canonicalTransport F s x w) (fun s => canonicalTransport F s x z)
    (hinput u) (hinput v) (hinput w) (hinput z)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hinterior)

/-- At each included time the canonical transport is a smooth bundle map. -/
theorem canonicalTransport_contMDiff_space
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b) :
    ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun y => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        x (canonicalTransport F t x)) := by
  rw [← contMDiffOn_univ]
  exact (canonicalTransport_contMDiffOn F).comp
    (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ _ => ⟨ht, mem_univ _⟩)

/- The canonical solution can be used directly in the curvature transport
consumer. This packages the initial-value, metric, invertibility, and
moving-input facts without introducing an additional transport witness. -/
theorem exists_canonical_curvature_transport
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Ico a b))
    (hab : a < b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∃ U : ℝ → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      U a = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Ico a b, HasDerivWithinAt U
        ((ricciEndomorphism F x t).comp (U t)) (Ico a b) t) ∧
      (∀ t ∈ Ico a b, ∀ v w,
        (F.metric t).inner x (U t v) (U t w) = (F.metric a).inner x v w) ∧
      (∀ t ∈ Ico a b, (U t).IsInvertible) ∧
      (∀ t ∈ Ioo a b, ∀ u v w z,
        HasDerivAt
          (fun s => (F.connection s).curvatureTensor x (U s u) (U s v) (U s w) (U s z))
          ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
              ![U t u, U t v, U t w, U t z] +
            2 * ((F.connection t).curvatureB x (U t u) (U t v) (U t w) (U t z) -
              (F.connection t).curvatureB x (U t u) (U t v) (U t z) (U t w) -
              (F.connection t).curvatureB x (U t u) (U t z) (U t v) (U t w) +
              (F.connection t).curvatureB x (U t u) (U t w) (U t v) (U t z))) t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let U := fun t => canonicalTransport F (a := a) (b := b) t x
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · exact canonicalTransport_initial F hab x
  · intro t ht
    exact canonicalTransport_hasDerivWithinAt F ht x
  · intro t ht v w
    exact canonicalTransport_pairing F hab ht x v w
  · intro t ht
    change (canonicalTransport F t x).IsInvertible
    rw [← orthonormalTransport_toContinuousLinearMap F t x]
    exact ContinuousLinearMap.isInvertible_equiv
  · intro t ht u v w z
    exact canonicalTransport_hasDerivAt_curvature hC F ht x u v w z

end PoincareMT.RicciFlow.Frame
