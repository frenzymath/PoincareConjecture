import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedPolygon










set_option autoImplicit false

open Set Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D




theorem exists_rounded_polygon_family_threshold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} [NeZero n] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hK : IsCompact K) (p : V → Polygon E n)
    (hp : ∀ i, ContDiff ℝ ∞ (fun z => p z i))
    (hsimple : ∀ z ∈ K, IsSimplePolygon (p z)) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ ∀ δ : ℝ, 0 < δ → δ < d → ∀ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ → (∀ s, δ ≤ |s| → ρ s = |s|) →
      (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) → (∀ s, |deriv ρ s| ≤ 1) →
      ContDiff ℝ ∞ (fun x : V × ℝ => roundedPolygonParameter ρ (p x.1) x.2) ∧
      (∀ z, Periodic (roundedPolygonParameter ρ (p z)) (n : ℝ)) ∧
      (∀ z ∈ K, InjOn (roundedPolygonParameter ρ (p z)) (Ico 0 (n : ℝ))) ∧
      (∀ z ∈ K, ∀ t, deriv (roundedPolygonParameter ρ (p z)) t ≠ 0) ∧
      ∀ z ∈ K, ∀ t, dist (roundedPolygonParameter ρ (p z) t)
        (polygonLinearParameter (p z) t) < ε := by
  have hsum : Continuous (fun z : V => ∑ i : Fin n, ‖p z i‖) :=
    continuous_finsetSum _ (fun i _ => (hp i).continuous.norm)
  obtain ⟨b, hb⟩ := hK.bddAbove_image hsum.continuousOn
  let B := max b 0 + 1
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hB (z : V) (hz : z ∈ K) (i : Fin n) : ‖p z i‖ ≤ B := by
    calc
      ‖p z i‖ ≤ ∑ j : Fin n, ‖p z j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg (p z j)) (Finset.mem_univ i)
      _ ≤ b := hb ⟨z, hz, rfl⟩
      _ ≤ B := by dsimp [B]; linarith [le_max_left b 0]
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  obtain ⟨η, hη, hstable⟩ := exists_periodic_injection_tolerance hK
    (T := (n : ℝ)) (r := 1 / 4) (by linarith) (by norm_num) (by linarith)
    (fun z => polygonLinearParameter (p z))
    (continuous_polygonLinearParameter (fun i => (hp i).continuous)).continuousOn
    (fun _ _ => periodic_polygonLinearParameter _)
    (fun z hz => (hsimple z hz).injOn_polygonLinearParameter)
  let d := min (1 / 4 : ℝ) (min ε η / (2 * B))
  have hd : 0 < d := by dsimp only [d]; positivity
  refine ⟨d, hd, min_le_left _ _, ?_⟩
  intro δ hδ hδd ρ hρ htail hbound hder
  have hδquarter : δ < 1 / 4 := lt_of_lt_of_le hδd (min_le_left _ _)
  have herr : 2 * δ * B < min ε η := by
    have h := (lt_div_iff₀ (show 0 < 2 * B by positivity)).mp
      (lt_of_lt_of_le hδd (min_le_right _ _))
    nlinarith
  have hhalf : δ < 1 / 2 := by linarith
  have hreg (z : V) (hz : z ∈ K) := (hsimple z hz).roundedPolygonParameter_regular
    hδ hδquarter htail hbound (hρ.differentiable (by simp)) hder
  have hclose (z : V) (hz : z ∈ K) (t : ℝ) :
      dist (roundedPolygonParameter ρ (p z) t) (polygonLinearParameter (p z) t) < min ε η :=
    (dist_roundedPolygonParameter_le (p z) hδ hhalf htail hbound (hB z hz) t).trans_lt herr
  refine ⟨contDiff_roundedPolygonParameter hδ hhalf htail hbound hρ hp,
    (fun z => periodic_roundedPolygonParameter ρ (p z)), ?_, ?_, ?_⟩
  · apply hstable (fun z => roundedPolygonParameter ρ (p z))
      (fun _ _ => periodic_roundedPolygonParameter _ _)
    · intro z hz t _
      exact lt_of_lt_of_le (hclose z hz t) (min_le_right _ _)
    · intro z hz
      exact (hreg z hz).1
  · intro z hz
    exact (hreg z hz).2
  · intro z hz t
    exact lt_of_lt_of_le (hclose z hz t) (min_le_left _ _)

end PoincareConjecture.M25.Topology3D
