import PoincareConjecture.Proofs.M10.Continuity
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option maxHeartbeats 800000 in

theorem reducedLength_time_derivative_measurable
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Measurable (fun q : M ↦ deriv (fun s ↦ reducedLength F T p q s) τ) := by
  let a := τ / 2
  let b := (τ + τmax) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have haτ : a < τ := by dsimp [a]; linarith
  have hτb : τ < b := by dsimp [b]; linarith
  have hb : b < τmax := by dsimp [b]; linarith
  let c := fun s : ℝ ↦ max a (min b s)
  have hc (s : ℝ) : c s ∈ Ioo 0 τmax :=
    ⟨ha.trans_le (le_max_left _ _),
      (max_le (haτ.trans hτb).le (min_le_left _ _)).trans_lt hb⟩
  let f := fun (q : M) (s : ℝ) ↦ reducedLength F T p q (c s)
  have hf : Continuous f.uncurry :=
    (reducedLength_continuousOn hL hDifferential p).comp_continuous
      (continuous_fst.prodMk (show Continuous (fun z : M × ℝ ↦ c z.2) by
        dsimp only [c]; fun_prop)) (fun z ↦ ⟨mem_univ _, hc z.2⟩)
  have hm : Measurable (fun q : M ↦ deriv (f q) τ) :=
    (measurable_deriv_with_param hf).comp (measurable_id.prodMk measurable_const)
  have heq (q : M) : deriv (f q) τ = deriv (fun s ↦ reducedLength F T p q s) τ := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds (show τ ∈ Ioo a b from ⟨haτ, hτb⟩)] with s hs
    dsimp only [f, c]
    rw [min_eq_right hs.2.le, max_eq_right hs.1.le]
  simpa only [heq] using hm

theorem reducedLength_weak_bound_measurable
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Measurable (fun q : M ↦ -deriv (fun s ↦ reducedLength F T p q s) τ +
      ((n : ℝ) / 2 - reducedLength F T p q τ) / τ) := by
  have hu : Continuous (fun q : M ↦ reducedLength F T p q τ) :=
    (reducedLength_continuousOn hL hDifferential p).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨mem_univ _, hτ, hmax⟩)
  exact (reducedLength_time_derivative_measurable hL hDifferential hτ hmax).neg.add
    ((measurable_const.sub hu.measurable).div_const τ)

end PoincareConjecture.M10
