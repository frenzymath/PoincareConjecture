import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphSides

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem exists_path_point_on_cap_boundary_sphere
    (K : CapCertificate g) (W : EpsilonNeck g)
    {f : UnitTwoSphere → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hfb : ∀ p, |f p| < 7 * W.epsilon⁻¹ / 8)
    (hgraph : K.boundary_sphere =
      range (fun p : UnitTwoSphere => W.coordinate_map (p, f p)))
    {γ : ℝ → M} {tP tW tb : ℝ} (_hPW : tP < tW) (hWb : tW < tb)
    (hγ : ContinuousOn γ (Icc tP tb))
    (hentry : ∃ a ∈ Ico tP tW,
      MapsTo γ (Icc a tW) W.carrier ∧
        neckGraphHeight W f (γ a) < 0)
    (hcoverW : MapsTo γ (Icc tW tb) W.carrier)
    (hexit : 0 < neckGraphHeight W f (γ tb)) :
    ∃ v ∈ Ioo tP tb, γ v ∈ K.boundary_sphere := by
  have hdom : ∀ p, f p ∈ Ioo (-W.epsilon⁻¹) W.epsilon⁻¹ := by
    intro p
    have hp := abs_lt.mp (hfb p)
    have hA : 0 < W.epsilon⁻¹ := inv_pos.mpr W.epsilon_pos
    constructor <;> nlinarith
  obtain ⟨a, ha, hentryW, hnegative⟩ := hentry
  have hab : a ≤ tb := ha.2.le.trans hWb.le
  have hγW : MapsTo γ (Icc a tb) W.carrier := by
    intro t ht
    by_cases hlt : t < tW
    · exact hentryW ⟨ht.1, le_of_lt hlt⟩
    · exact hcoverW ⟨le_of_not_gt hlt, ht.2⟩
  obtain ⟨v, hv, hvgraph⟩ := exists_neck_graph_crossing W hf hdom hab
    (hγ.mono (Icc_subset_Icc ha.1 le_rfl)) hγW
    (Or.inl rfl) (by simpa only [one_mul] using hnegative)
    (by simpa only [one_mul] using hexit)
  refine ⟨v, ?_, ?_⟩
  · exact ⟨ha.1.trans_lt hv.1, hv.2⟩
  · rw [hgraph]
    exact hvgraph

omit [T2Space M] in

theorem exists_path_point_on_cap_boundary_sphere_signed
    (K : CapCertificate g) (W : EpsilonNeck g)
    {f : UnitTwoSphere → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hfb : ∀ p, |f p| < 7 * W.epsilon⁻¹ / 8)
    (hgraph : K.boundary_sphere =
      range (fun p : UnitTwoSphere => W.coordinate_map (p, f p)))
    {γ : ℝ → M} {tP tW tb : ℝ} (_hPW : tP < tW) (hWb : tW < tb)
    (hγ : ContinuousOn γ (Icc tP tb))
    {kappa : ℝ} (hkappa : kappa = 1 ∨ kappa = -1)
    (hentry : ∃ a ∈ Ico tP tW,
      MapsTo γ (Icc a tW) W.carrier ∧
        kappa * neckGraphHeight W f (γ a) < 0)
    (hcoverW : MapsTo γ (Icc tW tb) W.carrier)
    (hexit : 0 < kappa * neckGraphHeight W f (γ tb)) :
    ∃ v ∈ Ioo tP tb, γ v ∈ K.boundary_sphere := by
  have hdom : ∀ p, f p ∈ Ioo (-W.epsilon⁻¹) W.epsilon⁻¹ := by
    intro p
    have hp := abs_lt.mp (hfb p)
    have hA : 0 < W.epsilon⁻¹ := inv_pos.mpr W.epsilon_pos
    constructor <;> nlinarith
  obtain ⟨a, ha, hentryW, hnegative⟩ := hentry
  have hab : a ≤ tb := ha.2.le.trans hWb.le
  have hγW : MapsTo γ (Icc a tb) W.carrier := by
    intro t ht
    by_cases hlt : t < tW
    · exact hentryW ⟨ht.1, le_of_lt hlt⟩
    · exact hcoverW ⟨le_of_not_gt hlt, ht.2⟩
  obtain ⟨v, hv, hvgraph⟩ := exists_neck_graph_crossing W hf hdom hab
    (hγ.mono (Icc_subset_Icc ha.1 le_rfl)) hγW hkappa hnegative hexit
  refine ⟨v, ?_, ?_⟩
  · exact ⟨ha.1.trans_lt hv.1, hv.2⟩
  · rw [hgraph]
    exact hvgraph

end PoincareConjecture.M28
