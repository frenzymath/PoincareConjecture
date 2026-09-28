import Mathlib.Geometry.Manifold.SmoothApprox










set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M59

variable {E H X F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [NormalSpace X] [SigmaCompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_coordinate_approximation_preserving_value
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : X → F) (hf : ContinuousOn f U) (p : F) {delta : ℝ} (hd : 0 < delta) :
    ∃ v : X → F, ContMDiff I 𝓘(ℝ, F) ∞ v ∧
      (∀ x ∈ K, dist (v x) (f x) < delta) ∧
      ∀ x ∈ K, f x = p → v x = p := by
  obtain ⟨a, ha0, ha1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I
    hU.isClosed_compl hK.isClosed
    (by exact disjoint_left.mpr fun x hx hKx => hx (hKU hKx)) (n := (⊤ : ℕ∞))
  let w : X → F := fun x => a x • (f x - p)
  have hw : Continuous w := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact a.contMDiff.continuous.continuousAt.smul
        (((hf x hx).continuousAt (hU.mem_nhds hx)).sub continuousAt_const)
    · have ha : (a : X → ℝ) =ᶠ[𝓝 x] 0 := ha0.filter_mono (nhds_le_nhdsSet hx)
      have he : w =ᶠ[𝓝 x] 0 := by
        filter_upwards [ha] with y hy
        simp only [w, hy, Pi.zero_apply, zero_smul]
      exact he.continuousAt
  obtain ⟨g, hg, hsupp⟩ := hw.exists_contMDiff_approx I (⊤ : ℕ∞)
    (ε := fun _ => delta) continuous_const (fun _ => hd)
  refine ⟨fun x => g x + p, g.contMDiff.add contMDiff_const, ?_, ?_⟩
  · intro x hx
    have hax : a x = 1 := ha1.self_of_nhdsSet x hx
    have hdist : dist (g x + p) (f x) = dist (g x) (w x) := by
      simp only [dist_eq_norm, w, hax, one_smul]
      congr 1
      abel
    rw [hdist]
    exact hg x
  · intro x _ hxp
    have hw0 : w x = 0 := by simp only [w, hxp, sub_self, smul_zero]
    have hg0 : g x = 0 := by
      by_contra h
      exact hsupp h hw0
    simp only [hg0, zero_add]

end PoincareConjecture.Proofs.M59
