import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Geodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.TerminalChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.ChangeCoordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.FixedChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Speed












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric


theorem exists_geodesic_continuation_of_terminal_chart
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    {a t₁ b : ℝ} (hat : a < t₁) (htb : t₁ < b)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Ioo a b))
    (p : M) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt (𝓡 n) p).target)
    {q w : ℝ → EuclideanSpace ℝ (Fin n)}
    (hqrepr : ∀ t ∈ Ioo t₁ b,
      γ t = (extChartAt (𝓡 n) p).symm (q t))
    (hqK : ∀ t ∈ Ioo t₁ b, q t ∈ K)
    (hq : ∀ t ∈ Ioo t₁ b, HasDerivAt q (w t) t)
    (hw : ∀ t ∈ Ioo t₁ b, HasDerivAt w
      (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
        (q t) (w t) (w t)) t) :
    ∃ δ > 0, ∃ η : ℝ → M,
      EqOn η γ (Ioo a b) ∧ g.IsGeodesicOn η (Ioo a (b + δ)) := by
  obtain ⟨δ, hδ, q', w', heqq, heqw, hq'b, hq'⟩ :=
    exists_chart_geodesic_continuation g p hK hKU htb hqK hq hw
  let η : ℝ → M := fun t =>
    if t < b then γ t else (extChartAt (𝓡 n) p).symm (q' t)
  have hηeq : EqOn η γ (Ioo a b) := by
    intro t ht
    simp [η, ht.2]
  refine ⟨δ, hδ, η, hηeq, ?_⟩
  intro t ht
  by_cases htb' : t < b
  · obtain ⟨r, q₀, w₀, hq₀⟩ := hγ t ⟨ht.1, htb'⟩
    refine ⟨r, q₀, w₀, ?_⟩
    filter_upwards [hq₀, isOpen_Iio.mem_nhds htb'] with u hu hu_lt
    exact ⟨by simpa only [η, if_pos (show u < b from hu_lt)] using hu.1, hu.2⟩
  · refine ⟨p, q', w', ?_⟩
    have ht_term : t ∈ Ioo t₁ (b + δ) := ⟨lt_of_lt_of_le htb (le_of_not_gt htb'), ht.2⟩
    filter_upwards [isOpen_Ioo.mem_nhds ht_term] with u hu
    have hq'u := hq' u hu
    have htarget := hq'u.1
    have hderivq := hq'u.2.1
    have hderivw := hq'u.2.2
    have heq : η u = (extChartAt (𝓡 n) p).symm (q' u) := by
      by_cases hul : u < b
      · have hu_term : u ∈ Ioo t₁ b := ⟨by linarith [hu.1], hul⟩
        rw [show η u = γ u by simp [η, hul], hqrepr u hu_term]
        rw [heqq hu_term]
      · simp [η, hul]
    exact ⟨heq, htarget, hderivq, hderivw⟩










theorem exists_precompact_chart_patch_continuation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt (𝓡 n) p).target)
    {a t₁ b : ℝ} (_hat : a < t₁) (htb : t₁ < b)
    {q w : ℝ → EuclideanSpace ℝ (Fin n)}
    (hqK : ∀ t ∈ Ioo t₁ b, q t ∈ K)
    (hq : ∀ t ∈ Ioo t₁ b, HasDerivAt q (w t) t)
    (hw : ∀ t ∈ Ioo t₁ b, HasDerivAt w
      (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
        (q t) (w t) (w t)) t) :
    ∃ δ > 0, ∃ q' w' : ℝ → EuclideanSpace ℝ (Fin n),
      EqOn q' q (Ioo t₁ b) ∧ EqOn w' w (Ioo t₁ b) ∧ q' b ∈ K ∧
      ∀ t ∈ Ioo t₁ (b + δ),
        q' t ∈ (extChartAt (𝓡 n) p).target ∧ HasDerivAt q' (w' t) t ∧
        HasDerivAt w'
          (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
            (q' t) (w' t) (w' t)) t := by
  exact exists_chart_geodesic_continuation g p hK hKU htb hqK hq hw







theorem exists_geodesic_continuation_of_edist_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {a b : ℝ} (hab : a < b)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Ioo a b))
    {S : Set M} (hS : IsCompact S) (hγS : MapsTo γ (Ioo a b) S)
    (C : ℝ≥0)
    (hC : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      g.edist (γ s) (γ t) ≤ C * EDist.edist s t) :
    ∃ δ > 0, ∃ η : ℝ → M,
      EqOn η γ (Ioo a b) ∧ g.IsGeodesicOn η (Ioo a (b + δ)) := by
  obtain ⟨p, hpS, t₁, ht₁, K, hK, hKU, hterm⟩ :=
    exists_terminal_compact_chart_of_edist_bound g hab hS hγS C hC
  let q : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t => extChartAt (𝓡 n) p (γ t)
  let w : ℝ → EuclideanSpace ℝ (Fin n) := deriv q
  have hsource : MapsTo γ (Ioo t₁ b) (extChartAt (𝓡 n) p).source :=
    fun t ht => (hterm t ht).1
  have hγterm : g.IsGeodesicOn γ (Ioo t₁ b) :=
    fun t ht => hγ t ⟨lt_trans ht₁.1 ht.1, ht.2⟩
  have hfixed := hγterm.hasDerivAt_in_chart isOpen_Ioo p hsource
  have hq : ∀ t ∈ Ioo t₁ b, HasDerivAt q (w t) t := by
    intro t ht
    exact hfixed t ht |>.1
  have hw : ∀ t ∈ Ioo t₁ b,
      HasDerivAt w
        (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (q t) (w t) (w t)) t := by
    intro t ht
    exact hfixed t ht |>.2
  have hqK : ∀ t ∈ Ioo t₁ b, q t ∈ K := by
    intro t ht
    exact (hterm t ht).2
  have hqrepr : ∀ t ∈ Ioo t₁ b,
      γ t = (extChartAt (𝓡 n) p).symm (q t) := by
    intro t ht
    exact ((extChartAt (𝓡 n) p).left_inv (hsource ht)).symm
  exact exists_geodesic_continuation_of_terminal_chart g ht₁.1 ht₁.2 hγ p
    hK hKU hqrepr hqK hq hw





theorem exists_geodesic_continuation_of_compact_confinement
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {a b : ℝ} (hab : a < b)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Ioo a b))
    {S : Set M} (hS : IsCompact S) (hγS : MapsTo γ (Ioo a b) S) :
    ∃ δ > 0, ∃ η : ℝ → M,
      EqOn η γ (Ioo a b) ∧ g.IsGeodesicOn η (Ioo a (b + δ)) := by
  obtain ⟨C, hC⟩ := hγ.exists_edist_le_mul hab
  exact exists_geodesic_continuation_of_edist_bound g hab hγ hS hγS C hC

end PoincareConjecture.RiemannianMetric
