import PoincareConjecture.Proofs.M10.GlobalRegularSlice

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem regular_tensor_eq_of_weight_deriv_zero
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hpos : 0 < weightedExponentialJacobian G τ x)
    (hzero : deriv (fun s ↦ weightedExponentialJacobian G s x) τ = 0) :
    let q := G.gamma (metricCoordinates (F.metric T) p x) τ
    ∀ v w : TangentSpace (𝓡 n) q,
      (F.connection (T - τ)).ricci q v w +
        (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q v w =
          (F.metric (T - τ)).inner q v w / (2 * τ) := by
  let Z := metricCoordinates (F.metric T) p x
  let q := G.gamma Z τ
  have hsrc : (Z, τ) ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have htgt : (q, τ) ∈ G.regularImage := by
    simpa only [LExponentialGeometry.regularImage, G.regular_forward, q] using
      G.regular_chart.map_source hsrc
  let r := G.regular_point (q, τ) htgt
  have hprod := (weightedExponentialJacobian_hasDerivAt hwindow hL hDifferential G x hreg).deriv
  rw [hzero] at hprod
  have hres := (mul_eq_zero.mp hprod.symm).resolve_left hpos.ne'
  obtain ⟨hd, hg, _⟩ := hDifferential.regular_point_formulas p q τ r
  rw [(regular_time_eventuallyEq r).deriv_eq] at hd
  rw [regular_gradientNormSq_eq r] at hg
  have hsum : deriv (fun s ↦ reducedLength F T p q s) τ +
      reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q =
        -reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative τ /
          (2 * τ * Real.sqrt τ) := by
    rw [hd, hg]
    ring
  have hsharp : reducedLengthLaplacian F T r.representative τ q =
      (n : ℝ) / (2 * τ) - (F.connection (T - τ)).scalarCurvature q -
        reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative τ /
          (2 * τ * Real.sqrt τ) := by
    rw [regular_laplacian_eq r]
    change (F.connection (T - τ)).laplacian (fun y ↦ reducedLength F T p y τ) q = _
    change (F.connection (T - τ)).scalarCurvature q +
      (F.connection (T - τ)).laplacian (fun y ↦ reducedLength F T p y τ) q -
      (deriv (fun s ↦ reducedLength F T p q s) τ +
        reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q) -
      (n : ℝ) / (2 * τ) = 0 at hres
    rw [hsum] at hres
    rw [neg_div] at hres
    linarith only [hres]
  dsimp only
  intro v w
  have htensor := hDifferential.regular_point_equality p G (q, τ) htgt hsharp v w
  change (F.connection (T - τ)).ricci q v w +
      (F.connection (T - τ)).hessian (fun y ↦ r.representative (y, τ)) q v w = _ at htensor
  rw [hessian_eq_of_eventuallyEq _ (regular_space_eventuallyEq r) v w] at htensor
  exact htensor

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem weightedExponentialJacobian_deriv_eq_zero_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n)
    (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) (hτb : τ < b) :
    deriv (fun s ↦ weightedExponentialJacobian G s x) τ = 0 := by
  have hconst : (fun s ↦ weightedExponentialJacobian G s x) =ᶠ[𝓝 τ]
      (fun _ ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hτ, hτb⟩] with s hs
    exact congrFun (weightedExponentialJacobian_eq_gaussian_of_volume_eq hL hDifferential G
      hmax hT hwindow hcurvature hs.1 (hs.2.trans hbmax)
      (reducedVolume_eq_euclidean_of_le hL hDifferential G hmax hT hwindow hcurvature
        hb hbmax hs.1 hs.2.le heq)) x
  rw [hconst.deriv_eq, deriv_const]

theorem reducedLength_tensor_eq_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n)
    (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) (hτb : τ < b) :
    let q := G.gamma (metricCoordinates (F.metric T) p x) τ
    ∀ v w : TangentSpace (𝓡 n) q,
      (F.connection (T - τ)).ricci q v w +
        (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q v w =
          (F.metric (T - τ)).inner q v w / (2 * τ) := by
  have heqτ := reducedVolume_eq_euclidean_of_le hL hDifferential G hmax hT hwindow
    hcurvature hb hbmax hτ hτb.le heq
  have hglobal := exponentialSliceChart_global_of_volume_eq hL hDifferential G hmax hT
    hwindow hcurvature hτ (hτb.trans hbmax) heqτ
  have hreg : (metricCoordinates (F.metric T) p x, τ) ∈
      G.toLExponentialFamily.regularDomain := by
    have hx : x ∈ (exponentialSliceChart G τ).source := hglobal.1.symm ▸ mem_univ x
    simpa only [exponentialSliceChart_source, mem_ofPred_eq] using hx
  have hpos : 0 < weightedExponentialJacobian G τ x := by
    rw [weightedExponentialJacobian_eq_gaussian_of_volume_eq hL hDifferential G hmax hT
      hwindow hcurvature hτ (hτb.trans hbmax) heqτ]
    exact sourceGaussian_pos n x
  exact regular_tensor_eq_of_weight_deriv_zero hwindow hL hDifferential G x hreg hpos
    (weightedExponentialJacobian_deriv_eq_zero_of_volume_eq hL hDifferential G hmax hT
      hwindow hcurvature hb hbmax heq x hτ hτb)

end PoincareConjecture.M10
