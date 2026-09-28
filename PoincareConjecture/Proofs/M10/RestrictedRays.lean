import PoincareConjecture.Proofs.M10.RegularWeights









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


def restrictedRegularSource (G : LExponentialGeometry F T τmax p)
    (A : Set (M × ℝ)) (τ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (exponentialSliceChart G τ).source ∩
    (fun x ↦ (exponentialSliceChart G τ x, τ)) ⁻¹' A


theorem restrictedRegularSource_isOpen (G : LExponentialGeometry F T τmax p)
    {A : Set (M × ℝ)} (hA : IsOpen A) (τ : ℝ) :
    IsOpen (restrictedRegularSource G A τ) :=
  ((exponentialSliceChart G τ).continuousOn.prodMk continuousOn_const).isOpen_inter_preimage
    (exponentialSliceChart G τ).open_source hA


noncomputable def restrictedWeightedJacobian (G : LExponentialGeometry F T τmax p)
    (A : Set (M × ℝ)) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (restrictedRegularSource G A τ).indicator (weightedExponentialJacobian G τ) x


theorem restrictedWeightedJacobian_nonneg (G : LExponentialGeometry F T τmax p)
    (A : Set (M × ℝ)) {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ restrictedWeightedJacobian G A τ x := by
  classical
  by_cases hx : x ∈ restrictedRegularSource G A τ
  · simpa only [restrictedWeightedJacobian, indicator_of_mem hx] using
      weightedExponentialJacobian_nonneg G hτ x
  · simp only [restrictedWeightedJacobian, indicator_of_notMem hx, le_refl]


theorem restrictedWeightedJacobian_measurable (G : LExponentialGeometry F T τmax p)
    {A : Set (M × ℝ)} (hA : IsOpen A) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Measurable (restrictedWeightedJacobian G A τ) := by
  classical
  have hc : ContinuousOn (weightedExponentialJacobian G τ)
      (restrictedRegularSource G A τ) :=
    (weightedExponentialJacobian_continuous G hτ hmax).continuousOn
  exact hc.measurable_piecewise continuousOn_const
      (restrictedRegularSource_isOpen G hA τ).measurableSet


theorem restrictedWeightedJacobian_le_regular (G : LExponentialGeometry F T τmax p)
    (A : Set (M × ℝ)) {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) :
    restrictedWeightedJacobian G A τ x ≤ regularWeightedJacobian G τ x := by
  classical
  by_cases hx : x ∈ restrictedRegularSource G A τ
  · simp only [restrictedWeightedJacobian, regularWeightedJacobian,
      indicator_of_mem hx, indicator_of_mem hx.1, le_refl]
  · simpa only [restrictedWeightedJacobian, indicator_of_notMem hx] using
      regularWeightedJacobian_nonneg G hτ x


theorem restrictedRegularSource_backward_nested (G : LExponentialGeometry F T τmax p)
    {A : Set (M × ℝ)} (hA : IsBackwardLStarShaped F T τmax p A)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    restrictedRegularSource G A b ⊆ restrictedRegularSource G A a := by
  intro x hx
  have hreg : (metricCoordinates (F.metric T) p x, b) ∈
      G.toLExponentialFamily.regularDomain := by
    simpa only [exponentialSliceChart_source, mem_ofPred_eq] using hx.1
  have hrega := G.backward_nesting _ b hreg a ha hab
  refine ⟨?_, ?_⟩
  · simpa only [exponentialSliceChart_source, mem_ofPred_eq] using hrega
  · obtain ⟨r, hr⟩ := hA.2.2 (exponentialSliceChart G b x, b) hx.2
    obtain ⟨_, _, _, huniq⟩ := hreg.1
    have heq := huniq r.path r.path_start
      (by simpa only [exponentialSliceChart_apply] using r.path_end) r.minimizing
    have hpath := hr a ⟨ha, hab⟩
    rw [heq ⟨ha.le, hab⟩] at hpath
    simpa only [mem_preimage, exponentialSliceChart_apply] using hpath

variable [ConnectedSpace M]


theorem restrictedWeightedJacobian_antitoneOn
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) {A : Set (M × ℝ)}
    (hA : IsBackwardLStarShaped F T τmax p A) (x : EuclideanSpace ℝ (Fin n)) :
    AntitoneOn (fun τ ↦ restrictedWeightedJacobian G A τ x) (Ioo 0 τmax) := by
  classical
  intro a ha b hb hab
  by_cases hx : x ∈ restrictedRegularSource G A b
  · have hxa := restrictedRegularSource_backward_nested G hA ha.1 hab hx
    have hreg : (metricCoordinates (F.metric T) p x, b) ∈
        G.toLExponentialFamily.regularDomain := by
      simpa only [exponentialSliceChart_source, mem_ofPred_eq] using hx.1
    have hrega := G.backward_nesting _ b hreg a ha.1 hab
    simp only [restrictedWeightedJacobian, indicator_of_mem hx, indicator_of_mem hxa]
    exact weightedExponentialJacobian_antitoneOn hwindow hL hDifferential G x hrega hreg hab
  · simpa only [restrictedWeightedJacobian, indicator_of_notMem hx] using
      restrictedWeightedJacobian_nonneg G A ha.1 x

end PoincareConjecture.M10
