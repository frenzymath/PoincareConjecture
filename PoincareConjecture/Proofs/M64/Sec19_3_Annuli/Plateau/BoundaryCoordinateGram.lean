import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.C2BoundaryMetric
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusStressIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

theorem m64BoundaryCoordinate_metric_gram {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (e : M → EuclideanSpace ℝ (Fin m)) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (A : EuclideanSpace ℝ (Fin n) → M)
    (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hsymm : ∀ q v w, B q v w = B q w v)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    {f : LoopPlane → M} {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {p : LoopPlane}
    (hu : DifferentiableAt ℝ u p) (hA : MDifferentiableAt (𝓡 n) (𝓡 n) A (u p))
    (heq : f =ᶠ[𝓝 p] A ∘ u) (i j : Fin 2) :
    m64ObservedCoordinateMetric (e ∘ A) (B ∘ A) (u p)
      (fderiv ℝ u p (EuclideanSpace.single i 1))
      (fderiv ℝ u p (EuclideanSpace.single j 1)) = m60AreaGram g f p i j := by
  have hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p :=
    (hA.comp p hu.mdifferentiableAt).congr_of_eventuallyEq heq
  have hJ : DifferentiableAt ℝ (e ∘ A) (u p) :=
    mdifferentiableAt_iff_differentiableAt.mp ((he.mdifferentiable (by simp) _).comp (u p) hA)
  have hobs : (e ∘ f) =ᶠ[𝓝 p] (e ∘ A) ∘ u :=
    heq.mono fun z hz => congrArg e hz
  have hder : fderiv ℝ (e ∘ f) p = (fderiv ℝ (e ∘ A) (u p)).comp (fderiv ℝ u p) :=
    hobs.fderiv_eq.trans (fderiv_comp p hJ hu)
  have hcol (k : Fin 2) : fderiv ℝ (e ∘ f) p (EuclideanSpace.single k 1) =
      fderiv ℝ (e ∘ A) (u p) (fderiv ℝ u p (EuclideanSpace.single k 1)) :=
    congrArg (fun D => D (EuclideanSpace.single k 1)) hder
  have hvalue : f p = A (u p) := heq.self_of_nhds
  change B (A (u p))
    (fderiv ℝ (e ∘ A) (u p) (fderiv ℝ u p (EuclideanSpace.single i 1)))
    (fderiv ℝ (e ∘ A) (u p) (fderiv ℝ u p (EuclideanSpace.single j 1))) = _
  rw [← hvalue, ← hcol i, ← hcol j]
  have h := m64ObservedMetric_symmetric_pair_of_mDifferentiableAt g e he B hdiag hf i j
  rw [hsymm (f p) (fderiv ℝ (e ∘ f) p (EuclideanSpace.single j 1))] at h
  linarith only [h]

end PoincareConjecture
