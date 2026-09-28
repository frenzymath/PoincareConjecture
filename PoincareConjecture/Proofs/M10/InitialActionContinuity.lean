import PoincareConjecture.Definitions.Ch06.ReducedLength
import Mathlib.MeasureTheory.Integral.DominatedConvergence









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem action_continuousOn_initial (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {b : ℝ} (hb : 0 < b) (hmax : b < τmax) :
    ContinuousOn (G.toLExponentialFamily.action Z) (Icc 0 b) := by
  have hi := (G.path Z b hb hmax).l_integrable
  rw [G.path_eq Z b hb hmax] at hi
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc :
    (0 : ℝ) ∈ uIcc 0 b)
  change ContinuousOn (fun s ↦ ∫ t in 0..s, backwardLIntegrand F T (G.gamma Z) t) (Icc 0 b)
  simpa only [uIcc_of_le hb.le] using hc


theorem action_tendsto_zero (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (Z : TangentSpace (𝓡 n) p) :
    Tendsto (G.toLExponentialFamily.action Z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨b, hb, hbmax⟩ := exists_between hmax
  have hc := action_continuousOn_initial G Z hb hbmax 0 ⟨le_rfl, hb.le⟩
  have he : Icc (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with s hs hsb
    exact ⟨hs.le, hsb.le⟩
  have ht := hc.tendsto.mono_left (le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.2 he))
  have hzero : G.toLExponentialFamily.action Z 0 = 0 := by
    simp only [LExponentialFamily.action, backwardLLength, intervalIntegral.integral_same]
  rwa [hzero] at ht

end PoincareConjecture.M10
