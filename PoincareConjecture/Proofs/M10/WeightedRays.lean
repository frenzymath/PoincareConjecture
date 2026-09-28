import PoincareConjecture.Proofs.M10.ExponentialJacobian
import PoincareConjecture.Proofs.M10.ExponentialTransport
import PoincareConjecture.Proofs.M10.MovingAction
import PoincareConjecture.Proofs.M10.WeightedJacobian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

noncomputable def weightedExponentialJacobian (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.rpow τ (-(n : ℝ) / 2) *
    Real.exp (-(G.toLExponentialFamily.action (metricCoordinates (F.metric T) p x) τ /
      (2 * Real.sqrt τ))) * exponentialSliceJacobian G τ x

theorem weightedExponentialJacobian_nonneg (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ weightedExponentialJacobian G τ x :=
  mul_nonneg (mul_pos (Real.rpow_pos_of_pos hτ _) (Real.exp_pos _)).le
    (exponentialSliceJacobian_nonneg G τ x)

variable [ConnectedSpace M]

theorem weightedExponentialJacobian_eq_density_mul (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain) :
    weightedExponentialJacobian G τ x =
      reducedVolumeDensity F T p τ (exponentialSliceChart G τ x) *
        exponentialSliceJacobian G τ x := by
  obtain ⟨hτ, hmax, hmin, _⟩ := hreg.1
  have ha := reducedLength_eq_normalized_action_of_minimizing hL G
    (metricCoordinates (F.metric T) p x) hτ hmax hmin
  simp only [weightedExponentialJacobian, reducedVolumeDensity, exponentialSliceChart_apply,
    ha, if_pos hτ]

theorem weightedExponentialJacobian_hasDerivAt
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain) :
    let q := G.gamma (metricCoordinates (F.metric T) p x) τ
    HasDerivAt (fun s ↦ weightedExponentialJacobian G s x)
      (weightedExponentialJacobian G τ x *
        ((F.connection (T - τ)).scalarCurvature q +
          (F.connection (T - τ)).laplacian (fun y ↦ reducedLength F T p y τ) q -
          (deriv (fun s ↦ reducedLength F T p q s) τ +
            reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q) -
          (n : ℝ) / (2 * τ))) τ := by
  obtain ⟨hτ, _, _, _⟩ := hreg.1
  have ha := normalized_action_regular_hasDerivAt hL hDifferential G
    (metricCoordinates (F.metric T) p x) hreg
  have hj := exponentialJacobian_hasDerivAt hwindow hL G x hreg
  simp only [exponentialSliceChart_apply] at hj
  exact weightedJacobian_hasDerivAt hτ ha hj

theorem weightedExponentialJacobian_deriv_nonpos
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain) :
    deriv (fun s ↦ weightedExponentialJacobian G s x) τ ≤ 0 := by
  let Z := metricCoordinates (F.metric T) p x
  have hsrc : (Z, τ) ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have htgt : (G.gamma Z τ, τ) ∈ G.regular_chart.target := by
    simpa only [G.regular_forward] using G.regular_chart.map_source hsrc
  have hres := (reducedLength_regular_inequalities hDifferential
    (G.regular_point (G.gamma Z τ, τ) htgt)).1
  obtain ⟨hτ, _, _, _⟩ := hreg.1
  rw [(weightedExponentialJacobian_hasDerivAt hwindow hL hDifferential G x hreg).deriv]
  refine mul_nonpos_of_nonneg_of_nonpos (weightedExponentialJacobian_nonneg G hτ x) ?_
  dsimp only [reducedLengthLaplacian] at hres
  linarith only [hres]

theorem weightedExponentialJacobian_antitoneOn
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) :
    AntitoneOn (fun s ↦ weightedExponentialJacobian G s x)
      {s | (metricCoordinates (F.metric T) p x, s) ∈ G.toLExponentialFamily.regularDomain} := by
  intro a ha b hb hab
  obtain ⟨ha0, _, _, _⟩ := ha.1
  have hreg (s : ℝ) (hs : s ∈ Icc a b) :
      (metricCoordinates (F.metric T) p x, s) ∈ G.toLExponentialFamily.regularDomain :=
    G.backward_nesting _ b hb s (ha0.trans_le hs.1) hs.2
  have hanti : AntitoneOn (fun s ↦ weightedExponentialJacobian G s x) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun s hs ↦ (weightedExponentialJacobian_hasDerivAt hwindow hL hDifferential G x
        (hreg s hs)).continuousAt.continuousWithinAt)
      (fun s hs ↦ (weightedExponentialJacobian_hasDerivAt hwindow hL hDifferential G x
        (hreg s (interior_subset hs))).differentiableAt.differentiableWithinAt)
    intro s hs
    exact weightedExponentialJacobian_deriv_nonpos hwindow hL hDifferential G x
      (hreg s (interior_subset hs))
  exact hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

end PoincareConjecture.M10
