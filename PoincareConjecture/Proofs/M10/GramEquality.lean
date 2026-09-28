import PoincareConjecture.Proofs.M10.RayTensorEquality
import PoincareConjecture.Proofs.M10.GramDiagonal
import PoincareConjecture.Proofs.M10.InitialPairing
import PoincareConjecture.Proofs.M10.HomogeneousRay

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponential_diagonal_eq_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n)
    (x v : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) (hτb : τ < b) :
    pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ) x v v =
      4 * τ * inner ℝ v v := by
  let f := fun s ↦ pullbackMetricForm (F.metric (T - s)) (exponentialSliceChart G s) x v v
  have hd (s : ℝ) (hs : s ∈ Ioo 0 b) : HasDerivAt f (f s / s) s := by
    have heqs := reducedVolume_eq_euclidean_of_le hL hDifferential G hmax hT hwindow
      hcurvature hb hbmax hs.1 hs.2.le heq
    have hsource := (exponentialSliceChart_global_of_volume_eq hL hDifferential G hmax hT
      hwindow hcurvature hs.1 (hs.2.trans hbmax) heqs).1
    have hreg : (metricCoordinates (F.metric T) p x, s) ∈
        G.toLExponentialFamily.regularDomain := by
      have hx : x ∈ (exponentialSliceChart G s).source := hsource.symm ▸ mem_univ x
      simpa only [exponentialSliceChart_source, mem_ofPred_eq] using hx
    let V := G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) s
      (metricCoordinates (F.metric T) p v)
    have hmetric : (F.metric (T - s)).inner
        (G.gamma (metricCoordinates (F.metric T) p x) s) V V = f s := by
      change (F.metric (T - s)).inner (G.gamma (metricCoordinates (F.metric T) p x) s) V V =
        (F.metric (T - s)).inner (exponentialSliceChart G s x)
          (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G s) x v)
          (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G s) x v)
      rw [exponentialSliceChart_differential G hs.1 (hs.2.trans hbmax),
        exponentialSliceChart_apply]
    have htensor := reducedLength_tensor_eq_of_volume_eq hL hDifferential G hmax hT
      hwindow hcurvature hb hbmax heq x hs.1 hs.2 V V
    rw [hmetric] at htensor
    apply (exponential_diagonal_hasDerivAt hwindow hL G x v hreg).congr_deriv
    calc
      _ = 2 * (f s / (2 * s)) := by linarith only [htensor]
      _ = f s / s := by ring
  have h := homogeneous_ray_eq hb hd
    (exponential_scaled_pairing_tendsto G hmax hT hwindow x v v) ⟨hτ, hτb⟩
  dsimp only [f] at h
  calc
    _ = (4 * inner ℝ v v) * τ := h
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in

theorem exponential_pairing_eq_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n)
    (x u v : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) (hτb : τ < b) :
    pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ) x u v =
      4 * τ * inner ℝ u v := by
  let B := pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ) x
  have hdiag := fun v ↦ exponential_diagonal_eq_of_volume_eq hL hDifferential G hmax hT hwindow
    hcurvature hb hbmax heq x v hτ hτb
  have hu : B u u = 4 * τ * inner ℝ u u := hdiag u
  have hv : B v v = 4 * τ * inner ℝ v v := hdiag v
  have huv : B (u + v) (u + v) = 4 * τ * inner ℝ (u + v) (u + v) := hdiag (u + v)
  have hsymm : B v u = B u v := (F.metric (T - τ)).symm _ _ _
  simp only [map_add, _root_.add_apply, inner_add_left, inner_add_right, hsymm] at huv
  rw [real_inner_comm u v] at huv
  change B u v = _
  nlinarith only [hu, hv, huv]

end PoincareConjecture.M10
