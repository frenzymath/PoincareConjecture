import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PhysicalBuffer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M04.TensorNorm










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M44

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem physicalBufferFlow_curvatureTensorNorm {J : Set ℝ} (F : RicciFlow n M J)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (t : ℝ) (x : (⟨e.target, e.open_target⟩ : Opens M)) :
    ((physicalBufferFlow F e).connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm x.1 := by
  simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using
    physicalBufferFlow_curvatureDerivativeNorm F e t 0 x




theorem physicalBufferFlow_pullbackCoefficients {J : Set ℝ} (F : RicciFlow n M J)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (p : (⟨e.target, e.open_target⟩ : Opens M)) (t : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    ((physicalBufferFlow F e).metric t).pullbackCoefficients (targetChart e p) x =
      (F.metric t).pullbackCoefficients e x := by
  have heq : (Subtype.val ∘ targetChart e p) =ᶠ[𝓝 x] (e : _ → M) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact targetChart_val e p hy
  have hd : (mfderiv (𝓡 n) (𝓡 n) Subtype.val (targetChart e p x)).comp
      (mfderiv (𝓡 n) (𝓡 n) (targetChart e p) x) = mfderiv (𝓡 n) (𝓡 n) e x := by
    rw [← mfderiv_comp x ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) _)
      (((contMDiffOn_targetChart e p).contMDiffAt
        (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact heq.mfderiv_eq
  ext v w
  change (F.metric t).inner (targetChart e p x).1
      (mfderiv (𝓡 n) (𝓡 n) Subtype.val (targetChart e p x)
        (mfderiv (𝓡 n) (𝓡 n) (targetChart e p) x v))
      (mfderiv (𝓡 n) (𝓡 n) Subtype.val (targetChart e p x)
        (mfderiv (𝓡 n) (𝓡 n) (targetChart e p) x w)) =
    (F.metric t).inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
      (mfderiv (𝓡 n) (𝓡 n) e x w)
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  change mfderiv (𝓡 n) (𝓡 n) Subtype.val (targetChart e p x)
    (mfderiv (𝓡 n) (𝓡 n) (targetChart e p) x v) = mfderiv (𝓡 n) (𝓡 n) e x v at hv
  change mfderiv (𝓡 n) (𝓡 n) Subtype.val (targetChart e p x)
    (mfderiv (𝓡 n) (𝓡 n) (targetChart e p) x w) = mfderiv (𝓡 n) (𝓡 n) e x w at hw
  rw [hv, hw, targetChart_val e p hx]




theorem physicalBufferFlow_pullbackJets {J : Set ℝ} (F : RicciFlow n M J)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (p : (⟨e.target, e.open_target⟩ : Opens M)) (t : ℝ) (m : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    iteratedFDeriv ℝ m (((physicalBufferFlow F e).metric t).pullbackCoefficients
      (targetChart e p)) x =
        iteratedFDeriv ℝ m ((F.metric t).pullbackCoefficients e) x := by
  have heq : ((physicalBufferFlow F e).metric t).pullbackCoefficients (targetChart e p)
      =ᶠ[𝓝 x] (F.metric t).pullbackCoefficients e := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact physicalBufferFlow_pullbackCoefficients F e p t hy
  exact (heq.iteratedFDeriv ℝ m).self_of_nhds

end PoincareConjecture.M44
