import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem intrinsicOpenMetric_pullbackCoefficients (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M)
    {f : EuclideanSpace ℝ (Fin 3) → U} {x : EuclideanSpace ℝ (Fin 3)}
    (hf : MDifferentiableAt (𝓡 3) (𝓡 3) f x) :
    (intrinsicOpenMetric g U).pullbackCoefficients f x =
      g.pullbackCoefficients (Subtype.val ∘ f) x := by
  have hi : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : U → M) (f x) :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := U) (n := 1)).mdifferentiable
      one_ne_zero (f x)
  ext v w
  change g.inner (f x : M)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v))
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x w)) =
    g.inner (f x : M)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val ∘ f) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val ∘ f) x w)
  rw [mfderiv_comp x hi hf]
  rfl

namespace CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem tubeCriticalMetric_pullbackCoefficients (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (Acrit : ℝ) (k : ℕ)
    {f : EuclideanSpace ℝ (Fin 3) → H.tubeCriticalRegion T Acrit k}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hf : MDifferentiableAt (𝓡 3) (𝓡 3) f x) :
    (H.tubeCriticalMetric T Acrit k).pullbackCoefficients f x =
      (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ •
        ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).pullbackCoefficients
          (fun y => (f y).val.val) x := by
  have hi : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : H.tubeCriticalRegion T Acrit k → (T k).carrierOpen) (f x) :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := H.tubeCriticalRegion T Acrit k)
      (n := 1)).mdifferentiable one_ne_zero (f x)
  change (intrinsicOpenMetric (H.tubeMetric T k)
    (H.tubeCriticalRegion T Acrit k)).pullbackCoefficients f x = _
  rw [intrinsicOpenMetric_pullbackCoefficients _ _ hf]
  change (intrinsicOpenMetric (H.normalizedSliceMetric k)
    (T k).carrierOpen).pullbackCoefficients (Subtype.val ∘ f) x = _
  rw [intrinsicOpenMetric_pullbackCoefficients _ _ (hi.comp x hf)]
  ext v w
  rfl

end CounterexampleNeckFamily
end PoincareConjecture.M28
