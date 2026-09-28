import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M28

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem exists_local_pullback_realization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    {f : EuclideanSpace ℝ (Fin n) → M} (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible) :
    ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g'), g'.euclideanCoefficients =ᶠ[𝓝 p] g.pullbackCoefficients f := by
  obtain ⟨g', D, V, hVo, hpV, _, heq⟩ :=
    RiemannianMetric.exists_local_realization hU hp (g.pullbackCoefficients f)
      (fun x hx => (g.contDiffAt_pullbackCoefficients
        ((hf x hx).contMDiffAt (hU.mem_nhds hx))).contDiffWithinAt)
      (fun x _ v w => g.symm (f x) _ _)
      (fun x hx v hv => by
        apply g.pos (f x)
        intro hzero
        apply hv
        apply (hi x hx).injective
        rw [map_zero]
        convert! hzero using 1)
  exact ⟨g', D, Filter.mem_of_superset (hVo.mem_nhds hpV) heq⟩

private theorem curvatureTensor_eq_of_pullback_germ
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (gX : RiemannianMetric n X) (DE : LeviCivitaData gE) (DX : LeviCivitaData gX)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    {e : EuclideanSpace ℝ (Fin n) → X} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hie : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible)
    (hmetric : gE.euclideanCoefficients =ᶠ[𝓝 p] gX.pullbackCoefficients e)
    (u v w z : EuclideanSpace ℝ (Fin n)) :
    DE.curvatureTensor p u v w z = DX.curvatureTensor (e p)
      (mfderiv (𝓡 n) (𝓡 n) e p u) (mfderiv (𝓡 n) (𝓡 n) e p v)
      (mfderiv (𝓡 n) (𝓡 n) e p w) (mfderiv (𝓡 n) (𝓡 n) e p z) := by
  apply DE.curvatureTensor_eq_pullback_euclidean DX
    ((he p hp).contMDiffAt (hU.mem_nhds hp))
  · exact Filter.mem_of_superset (hU.mem_nhds hp) hie
  · filter_upwards [hmetric] with x hx a b
    exact congrArg (fun B => B a b) hx

set_option synthInstance.maxHeartbeats 200000 in

set_option maxSynthPendingDepth 12 in

set_option maxHeartbeats 1600000 in




theorem tendsto_curvatureTensor_of_pullback_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {M : α → Type*} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M i)]
    [∀ i, IsManifold (𝓡 n) ∞ (M i)]
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {gseq : ∀ i, RiemannianMetric n (M i)} {g : RiemannianMetric n N}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    {fseq : ∀ i, EuclideanSpace ℝ (Fin n) → M i}
    (hfseq : ∀ i, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (fseq i) U)
    (hiseq : ∀ i x, x ∈ U → (mfderiv (𝓡 n) (𝓡 n) (fseq i) x).IsInvertible)
    {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible)
    (hzero : Tendsto (fun i => (gseq i).pullbackCoefficients (fseq i) p) l
      (𝓝 (g.pullbackCoefficients f p)))
    (hone : Tendsto (fun i => fderiv ℝ ((gseq i).pullbackCoefficients (fseq i)) p) l
      (𝓝 (fderiv ℝ (g.pullbackCoefficients f) p)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ
      ((gseq i).pullbackCoefficients (fseq i))) p) l
      (𝓝 (fderiv ℝ (fderiv ℝ (g.pullbackCoefficients f)) p)))
    (u v w z : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun i => (Dseq i).curvatureTensor (fseq i p)
      (mfderiv (𝓡 n) (𝓡 n) (fseq i) p u) (mfderiv (𝓡 n) (𝓡 n) (fseq i) p v)
      (mfderiv (𝓡 n) (𝓡 n) (fseq i) p w) (mfderiv (𝓡 n) (𝓡 n) (fseq i) p z)) l
      (𝓝 (D.curvatureTensor (f p)
        (mfderiv (𝓡 n) (𝓡 n) f p u) (mfderiv (𝓡 n) (𝓡 n) f p v)
        (mfderiv (𝓡 n) (𝓡 n) f p w) (mfderiv (𝓡 n) (𝓡 n) f p z))) := by
  classical
  choose G DG hG using fun i =>
    exists_local_pullback_realization (gseq i) hU hp (hfseq i) (hiseq i)
  obtain ⟨H, DH, hH⟩ := exists_local_pullback_realization g hU hp hf hi
  have h0 : Tendsto (fun i => (G i).euclideanCoefficients p) l
      (𝓝 (H.euclideanCoefficients p)) := by
    simpa only [(hG _).self_of_nhds, hH.self_of_nhds] using hzero
  have h1 : Tendsto (fun i => fderiv ℝ (G i).euclideanCoefficients p) l
      (𝓝 (fderiv ℝ H.euclideanCoefficients p)) := by
    simpa only [(hG _).fderiv_eq, hH.fderiv_eq] using hone
  have h2 : Tendsto (fun i => fderiv ℝ (fderiv ℝ (G i).euclideanCoefficients) p) l
      (𝓝 (fderiv ℝ (fderiv ℝ H.euclideanCoefficients) p)) := by
    simpa only [(hG _).fderiv.fderiv_eq, hH.fderiv.fderiv_eq] using htwo
  have ht := LeviCivitaData.tendsto_curvatureTensor_of_metric_jets DG DH p u v w z h0 h1 h2
  simpa only [curvatureTensor_eq_of_pullback_germ (G _) _ (DG _) (Dseq _)
    hU hp (hfseq _) (hiseq _) (hG _),
    curvatureTensor_eq_of_pullback_germ H g DH D hU hp hf hi hH] using ht

end PoincareConjecture.M28
