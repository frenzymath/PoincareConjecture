import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateRows
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCommonInterval_actual_coordinate_extraction
    {M : Type u} {N : Type v} {X : ℕ → Type w}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    [MetricSpace N] [LocallyCompactSpace N]
    [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
    [∀ n, TopologicalSpace (X n)] [∀ n, ChartedSpace E (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X n) ∞)
    (f : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) N (X n) ∞)
    (d : M → N) (hd : Continuous d)
    (hsource : ∀ K : Set M, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ ((e n).trans (f n).symm).source)
    (hsourceF : ∀ K : Set N, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).source)
    (hconv : ∀ K : Set M, IsCompact K → TendstoUniformlyOn
      (fun n => (e n).trans (f n).symm) d atTop K)
    (a : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (b : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) N E ∞)
    (U : ℕ → Set E) (hU : ∀ i, IsOpen (U i))
    (hUa : ∀ i, U i ⊆ (a i).target)
    (hUb : ∀ i, MapsTo (fun x => d ((a i).symm x)) (U i) (b i).source)
    (hjetA : ∀ i m K, IsCompact K → K ⊆ (a i).target → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m ((h n).pullbackCoefficients (e n ∘ (a i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (a i).symm)) atTop K)
    (hjetB : ∀ i m K, IsCompact K → K ⊆ (b i).target → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m ((h n).pullbackCoefficients (f n ∘ (b i).symm)))
      (iteratedFDeriv ℝ m (k.pullbackCoefficients (b i).symm)) atTop K) :
    let A := fun i n => (((a i).symm.trans (e n)).trans (f n).symm).trans (b i)
    let F := fun i x => b i (d ((a i).symm x))
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      (∀ i, ContDiffOn ℝ ∞ (F i) (U i)) ∧
      (∀ i, MapsTo (F i) (U i) (b i).target) ∧
      (∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ m (A i (sigma n)))
        (iteratedFDeriv ℝ m (F i)) atTop K) ∧
      ∀ i x, x ∈ U i → ∀ v w : E,
        k.pullbackCoefficients (b i).symm (F i x)
            (fderiv ℝ (F i) x v) (fderiv ℝ (F i) x w) =
          g.pullbackCoefficients (a i).symm x v w := by
  have hsourceE (K : Set M) (hK : IsCompact K) :
      ∀ᶠ n in atTop, K ⊆ (e n).source := by
    filter_upwards [hsource K hK] with n hn x hx
    exact (hn hx).1
  have hrow (i : ℕ) := terminalCommonInterval_actual_coordinate_rows
    h e f d hd hsource hconv (a i) (b i) (hUa i) (hUb i)
  apply terminalCommonInterval_smooth_actual_coordinate_limits hU
    (fun i => (b i).open_target) (fun i x => b i (d ((a i).symm x)))
    (fun i => (hrow i).1)
  · intro i K hK hKU
    exact terminalCommonInterval_coordinate_coefficients_smooth h e hsourceE (a i)
      K hK (hKU.trans (hUa i))
  · intro i
    exact terminalCommonInterval_coordinate_coefficients_smooth h f hsourceF (b i)
  · exact fun i => (hrow i).2.1
  · exact fun i => (terminalCommonInterval_coordinate_limit_coefficients g (a i)).1.mono
      (hUa i)
  · exact fun i => (terminalCommonInterval_coordinate_limit_coefficients k (b i)).1
  · exact fun _i n x _hx v w =>
      terminalCommonInterval_coordinate_coefficients_symmetric (h n) _ x v w
  · exact fun _i n x _hx v w =>
      terminalCommonInterval_coordinate_coefficients_symmetric (h n) _ x v w
  · exact fun i x hx =>
      (terminalCommonInterval_coordinate_limit_coefficients g (a i)).2 x (hUa i hx)
  · exact fun i => (terminalCommonInterval_coordinate_limit_coefficients k (b i)).2
  · exact fun i m K hK hKU => hjetA i m K hK (hKU.trans (hUa i))
  · exact hjetB
  · exact fun i => (hrow i).2.2.1
  · exact fun i => (hrow i).2.2.2

end PoincareConjecture.M47
