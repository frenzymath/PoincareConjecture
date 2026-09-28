
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Canonical








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Set Bundle

universe u

noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem canonicalTransport_coordinates_hasDerivWithinAt
    (F : RicciFlow n M (Ico a b)) (x₀ x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x₀).baseSet)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt
      (fun s => ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) x₀ x x₀ x (canonicalTransport F s x))
      ((ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) x₀ x x₀ x (ricciEndomorphism F x t)).comp
        (ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) x₀ x x₀ x (canonicalTransport F t x)))
      (Ico a b) t := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let e := (trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x₀).continuousLinearEquivAt ℝ x hx
  simp only [ContinuousLinearMap.inCoordinates_eq hx hx]
  have hd := (e.arrowCongr e).hasFDerivAt.comp_hasDerivWithinAt t
    (canonicalTransport_hasDerivWithinAt F ht x)
  convert hd using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro v
  change e (ricciEndomorphism F x t
    (e.symm (e (canonicalTransport F t x (e.symm v))))) =
      e (ricciEndomorphism F x t (canonicalTransport F t x (e.symm v)))
  rw [e.symm_apply_apply]

theorem canonicalTransport_coordinates_initial
    (F : RicciFlow n M (Ico a b)) (hab : a < b) (x₀ x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x₀).baseSet) :
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x₀ x x₀ x (canonicalTransport F a x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  rw [canonicalTransport_initial F hab, ContinuousLinearMap.inCoordinates_eq hx hx]
  ext v
  simp

end PoincareConjecture.RicciFlow.Frame
