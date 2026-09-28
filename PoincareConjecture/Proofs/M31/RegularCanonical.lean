import PoincareConjecture.Definitions.M28BoundedDistance




set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


theorem regularTimes_left_dense (H : SingularTimeAssumptions F T M)
    {s : ℝ} (hs : s ∈ F.interval) (a : ℝ) (has : a < s) :
    ∃ u, u ∈ F.interval ∧ a < u ∧ u ≤ s ∧ (u = 0 ∨ u ∉ H.singularTimes) := by
  classical
  by_cases hzero : s = 0
  · subst s
    exact ⟨0, hs, has, le_rfl, Or.inl rfl⟩
  have hspos : 0 < s := lt_of_le_of_ne (H.interval_nonnegative hs) (Ne.symm hzero)
  let m : ℝ := (max a 0 + s) / 2
  have hmax : max a 0 < s := max_lt has hspos
  have ham : a < m := by dsimp [m]; linarith [le_max_left a 0]
  have hmpos : 0 < m := by dsimp [m]; linarith [le_max_right a 0]
  have hms : m < s := by dsimp [m]; linarith
  by_cases hm : m ∈ H.singularTimes
  · obtain ⟨delta, hdelta, hsep⟩ := H.singularTimes_discrete m hm
    let d : ℝ := min (delta / 2) ((s - m) / 2)
    have hdpos : 0 < d := lt_min (by linarith) (by linarith)
    have hdleft : d ≤ delta / 2 := min_le_left _ _
    have hdright : d ≤ (s - m) / 2 := min_le_right _ _
    have hus : m + d < s := by linarith
    have hu : m + d ∈ F.interval :=
      H.interval_exhausts_preterminal ⟨by linarith, hus.trans (H.interval_preterminal hs).2⟩
    refine ⟨m + d, hu, by linarith, hus.le, Or.inr ?_⟩
    intro hsingular
    have hdist := hsep (m + d) hsingular (by linarith)
    have habs : |m + d - m| = d := by
      rw [show m + d - m = d by ring, abs_of_pos hdpos]
    rw [habs] at hdist
    linarith
  · exact ⟨m, H.interval_exhausts_preterminal
      ⟨hmpos.le, hms.trans (H.interval_preterminal hs).2⟩, ham, hms.le, Or.inr hm⟩


theorem dense_canonical_control (H : SingularTimeAssumptions F T M)
    (t : ℝ) (x : (F.slice t).carrier)
    (hthreshold : H.r₀⁻¹ ^ 2 ≤ 4 * F.scalar ⟨t, x⟩) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods F H.epsilon H.constant t x := by
  intro s hs _ a has
  obtain ⟨u, hu, hau, hus, hregular⟩ := H.regularTimes_left_dense hs a has
  refine ⟨u, hu, hau, hus, ?_⟩
  intro y hy
  exact ⟨H.canonical_control u hu hregular y (hthreshold.trans hy)⟩

end PoincareConjecture.SingularTimeAssumptions
