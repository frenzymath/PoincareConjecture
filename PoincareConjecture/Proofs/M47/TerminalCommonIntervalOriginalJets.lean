import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateRows
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCommonInterval_original_coordinate_jets
    {M : ℕ → Type u} {N : Type v} {X : ℕ → Type w}
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace E (M i)]
    [∀ i, IsManifold (𝓡 3) ∞ (M i)]
    [MetricSpace N] [LocallyCompactSpace N]
    [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
    [∀ n, TopologicalSpace (X n)] [∀ n, ChartedSpace E (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : ∀ i, RiemannianMetric 3 (M i)) (k : RiemannianMetric 3 N)
    (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ i n, PartialDiffeomorph (𝓡 3) (𝓡 3) (M i) (X n) ∞)
    (f : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) N (X n) ∞)
    (d : ∀ i, M i → N) (hd : ∀ i, Continuous (d i))
    (hsource : ∀ i (K : Set (M i)), IsCompact K →
      ∀ᶠ n in atTop, K ⊆ ((e i n).trans (f n).symm).source)
    (hsourceF : ∀ K : Set N, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).source)
    (hconv : ∀ i (K : Set (M i)), IsCompact K → TendstoUniformlyOn
      (fun n => (e i n).trans (f n).symm) (d i) atTop K)
    (a : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) (M i) E ∞)
    (b : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) N E ∞)
    (U : ℕ → Set E) (hU : ∀ i, IsOpen (U i))
    (hUa : ∀ i, U i ⊆ (a i).target)
    (hUb : ∀ i, MapsTo (fun x => d i ((a i).symm x)) (U i) (b i).source)
    (hjetA : ∀ i m K, IsCompact K → K ⊆ (a i).target → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m ((h n).pullbackCoefficients (e i n ∘ (a i).symm)))
      (iteratedFDeriv ℝ m ((g i).pullbackCoefficients (a i).symm)) atTop K)
    (hjetB : ∀ i m K, IsCompact K → K ⊆ (b i).target → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m ((h n).pullbackCoefficients (f n ∘ (b i).symm)))
      (iteratedFDeriv ℝ m (k.pullbackCoefficients (b i).symm)) atTop K) :
    let A := fun i n => (((a i).symm.trans (e i n)).trans (f n).symm).trans (b i)
    let F := fun i x => b i (d i ((a i).symm x))
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      (∀ i, ContDiffOn ℝ ∞ (F i) (U i)) ∧
      (∀ i, MapsTo (F i) (U i) (b i).target) ∧
      (∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ m (A i (sigma n)))
        (iteratedFDeriv ℝ m (F i)) atTop K) ∧
      ∀ i x, x ∈ U i → ∀ v w : E,
        k.pullbackCoefficients (b i).symm (F i x)
            (fderiv ℝ (F i) x v) (fderiv ℝ (F i) x w) =
          (g i).pullbackCoefficients (a i).symm x v w := by
  have hsourceE (i : ℕ) (K : Set (M i)) (hK : IsCompact K) :
      ∀ᶠ n in atTop, K ⊆ (e i n).source := by
    filter_upwards [hsource i K hK] with n hn x hx
    exact (hn hx).1
  have hrow (i : ℕ) := terminalCommonInterval_actual_coordinate_rows
    h (e i) f (d i) (hd i) (hsource i) (hconv i) (a i) (b i) (hUa i) (hUb i)
  apply terminalCommonInterval_smooth_actual_coordinate_limits hU
    (fun i => (b i).open_target) (fun i x => b i (d i ((a i).symm x)))
    (fun i => (hrow i).1)
  · intro i K hK hKU
    exact terminalCommonInterval_coordinate_coefficients_smooth h (e i)
      (hsourceE i) (a i) K hK (hKU.trans (hUa i))
  · intro i
    exact terminalCommonInterval_coordinate_coefficients_smooth h f hsourceF (b i)
  · exact fun i => (hrow i).2.1
  · exact fun i => (terminalCommonInterval_coordinate_limit_coefficients (g i) (a i)).1.mono
      (hUa i)
  · exact fun i => (terminalCommonInterval_coordinate_limit_coefficients k (b i)).1
  · exact fun _i n x _hx v w =>
      terminalCommonInterval_coordinate_coefficients_symmetric (h n) _ x v w
  · exact fun _i n x _hx v w =>
      terminalCommonInterval_coordinate_coefficients_symmetric (h n) _ x v w
  · exact fun i x hx =>
      (terminalCommonInterval_coordinate_limit_coefficients (g i) (a i)).2 x (hUa i hx)
  · exact fun i => (terminalCommonInterval_coordinate_limit_coefficients k (b i)).2
  · exact fun i m K hK hKU => hjetA i m K hK (hKU.trans (hUa i))
  · exact hjetB
  · exact fun i => (hrow i).2.2.1
  · exact fun i => (hrow i).2.2.2

end PoincareConjecture.M47
