import PoincareLib.Geometry.Riemannian.Splitting.Busemann.Basic
import PoincareLib.Geometry.Riemannian.Splitting.Busemann.Weak.Supports
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Regularity

/-!
# Compact comparison for the Busemann limit

The distance approximants lie below the Busemann limit, so a boundary upper
bound for the limit also bounds every nonnegative-time approximant. The
vanishing support error gives comparison with a strictly superharmonic smooth
function, and pointwise convergence passes the comparison to the limit.

Reference: Morgan--Tian, Proposition 2.3, pp. 21--23.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Pointwise limits of approximants bounded above by their limit inherit
compact comparison when their lower-support errors tend uniformly to zero. -/
theorem le_on_compact_of_tendsto_lower_supports (D : LeviCivitaData g)
    {K : Set M} (hK : IsCompact K) {u : ℝ → M → ℝ} {b : M → ℝ}
    (hu : ∀ t, ContinuousOn (u t) K)
    (hlim : ∀ x ∈ K, Tendsto (fun t => u t x) atTop (𝓝 (b x)))
    (hle : ∀ᶠ t in atTop, ∀ x ∈ K, u t x ≤ b x)
    (hsupport : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ x ∈ K,
      ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧
        σ x = u t x ∧ (∀ y ∈ U, σ y ≤ u t y) ∧ -ε ≤ D.laplacian σ x)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hlap : ∀ x ∈ K, D.laplacian φ x < 0)
    (hboundary : ∀ x ∈ K, x ∉ interior K → b x ≤ φ x) :
    ∀ x ∈ K, b x ≤ φ x := by
  intro x hx
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩
    (D.continuous_laplacian hφ).continuousOn
  let ε := -(D.laplacian φ q) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith [hlap q hq]
  apply le_of_tendsto (hlim x hx)
  filter_upwards [hsupport ε hε, hle] with t ht htb
  apply D.le_on_compact_of_lower_supports hK (hu t) hφ (a := -ε) ?_ ?_ ?_ x hx
  · intro y hy
    exact ht y (interior_subset hy)
  · intro y hy
    have h := hmax (interior_subset hy)
    change D.laplacian φ y ≤ D.laplacian φ q at h
    dsimp [ε]
    linarith [hlap q hq]
  · intro y hy hnot
    exact (htb y hy).trans (hboundary y hy hnot)

end PoincareMT.LeviCivitaData

namespace PoincareMT.RiemannianMetric

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]

/-- On a compact set, a smooth function with strictly negative Laplacian
which bounds the Busemann function on the boundary bounds it everywhere. -/
theorem busemann_le_on_compact_of_laplacian_neg
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ D.ricci y v v)
    {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {K : Set M} (hK : IsCompact K) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hlap : ∀ x ∈ K, D.laplacian φ x < 0)
    (hboundary : ∀ x ∈ K, x ∉ interior K → g.busemann γ x ≤ φ x) :
    ∀ x ∈ K, g.busemann γ x ≤ φ x := by
  apply D.le_on_compact_of_tendsto_lower_supports hK
    (fun t => (g.continuous_busemannApprox γ t).continuousOn)
    (fun x _ => g.tendsto_busemannApprox hγ x) ?_ ?_ hφ hlap hboundary
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht x _
    exact g.busemannApprox_le_busemann hγ ht x
  · intro ε hε
    filter_upwards [g.eventually_busemannApprox_lower_supports_on_compact D hm
      hcomplete hRic γ hγ hK hε] with t ht x hx
    obtain ⟨U, σ, hU, hxU, hσ, heq, hle, _, hσlap⟩ := ht x hx
    exact ⟨U, σ, hU, hxU, hσ, heq, hle, hσlap⟩

/-- Summing the actual lower supports proves vanishing support error for
the two oriented approximants without a general addition theorem for limits. -/
theorem eventually_busemannApprox_add_reverse_lower_supports_on_compact
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ D.ricci y v v)
    {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K,
      ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ σ U ∧
        σ x = g.busemannApprox γ t x + g.busemannApprox (fun s => γ (-s)) t x ∧
        (∀ y ∈ U, σ y ≤
          g.busemannApprox γ t y + g.busemannApprox (fun s => γ (-s)) t y) ∧
        -ε ≤ D.laplacian σ x := by
  filter_upwards [g.eventually_busemannApprox_lower_supports_on_compact D hm
    hcomplete hRic γ hγ hK (half_pos hε),
    g.eventually_busemannApprox_lower_supports_on_compact D hm
      hcomplete hRic (fun s => γ (-s)) (g.minimizing_line_reverse hγ) hK (half_pos hε)]
    with t ht ht' x hx
  obtain ⟨U, σ, hU, hxU, hσ, heq, hle, _, hσlap⟩ := ht x hx
  obtain ⟨V, τ, hV, hxV, hτ, heq', hle', _, hτlap⟩ := ht' x hx
  let W := U ∩ V
  have hσW := hσ.mono (show W ⊆ U from inter_subset_left)
  have hτW := hτ.mono (show W ⊆ V from inter_subset_right)
  have hnegτ : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
      (fun y => (-1 : ℝ) * τ y) W := contMDiffOn_const.mul hτW
  refine ⟨W, fun y => σ y - (-1) * τ y, hU.inter hV, ⟨hxU, hxV⟩,
    hσW.sub hnegτ, ?_, ?_, ?_⟩
  · dsimp [busemannApprox]
    rw [heq, heq']
    ring
  · intro y hy
    have hs := hle y hy.1
    have ht := hle' y hy.2
    dsimp [busemannApprox]
    linarith
  · rw [LeviCivitaData.Dirichlet.laplacian_sub_on D (hU.inter hV) hσW
      hnegτ ⟨hxU, hxV⟩, D.laplacian_const_mul]
    linarith

/-- The sum of the two oriented Busemann functions satisfies compact
comparison with smooth strictly superharmonic functions. -/
theorem busemann_add_reverse_le_on_compact_of_laplacian_neg
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ D.ricci y v v)
    {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {K : Set M} (hK : IsCompact K) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hlap : ∀ x ∈ K, D.laplacian φ x < 0)
    (hboundary : ∀ x ∈ K, x ∉ interior K →
      g.busemann γ x + g.busemann (fun s => γ (-s)) x ≤ φ x) :
    ∀ x ∈ K, g.busemann γ x + g.busemann (fun s => γ (-s)) x ≤ φ x := by
  apply D.le_on_compact_of_tendsto_lower_supports hK
    (fun t => ((g.continuous_busemannApprox γ t).add
      (g.continuous_busemannApprox (fun s => γ (-s)) t)).continuousOn)
    (fun x _ => (g.tendsto_busemannApprox hγ x).add
      (g.tendsto_busemannApprox (g.minimizing_line_reverse hγ) x)) ?_ ?_ hφ hlap hboundary
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht x _
    exact add_le_add (g.busemannApprox_le_busemann hγ ht x)
      (g.busemannApprox_le_busemann (g.minimizing_line_reverse hγ) ht x)
  · intro ε hε
    exact g.eventually_busemannApprox_add_reverse_lower_supports_on_compact
      D hm hcomplete hRic hγ hK hε

end PoincareMT.RiemannianMetric
