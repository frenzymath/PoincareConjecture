import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.EndTensorTransition
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.EndTransitionDerivativeBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.ActualDifferenceDensity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.CoordinateTransportDensity

/-!
# Density comparison for arbitrary compatible reference metrics

Two actual metric pullback identities on the open overlap transport the
metric difference, connection difference and raised curvature difference.
The compact derivative bounds therefore give one density constant before
all four metrics and connections. No flow or connection-record equality
is required. This is Section 12.5, pp. 309-319 and Proposition 12.7,
pp. 298-299; see compatible-reference-energy.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

/-- Compact reference overlaps control actual difference density for
any two pairs of compatible metrics, with the constant chosen before
all metric and connection records (Section 12.5, pp. 309-319). -/
theorem exists_compatibleEnd_density_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {K : Set StandardCapSpace} (hK : IsCompact K) (hKU : K ⊆ endReferenceRegion e) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g0 g1 h0 h1 : RiemannianMetric 3 (endReferenceRegion e))
      (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
      (E0 : LeviCivitaData h0) (E1 : LeviCivitaData h1)
      (p : endReferenceRegion e) (r : ℝ), (r = -1 ∨ r = 0 ∨ r = 1) →
      (∀ y ∈ endReferenceOverlap e r, ∀ u v : TangentSpace (𝓡 3) y,
        g0.inner y u v = h0.inner (endReferenceTransition e p r y)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y u)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y v)) →
      (∀ y ∈ endReferenceOverlap e r, ∀ u v : TangentSpace (𝓡 3) y,
        g1.inner y u v = h1.inner (endReferenceTransition e p r y)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y u)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y v)) →
      ∀ x : endReferenceRegion e, (x : StandardCapSpace) ∈ K →
        endAxialTranslation e r x ∈ K →
        actualDifferenceEnergyDensity qH qA qS D0 D1 x ≤
          C * actualDifferenceEnergyDensity qH qA qS E0 E1 (endReferenceTransition e p r x) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  obtain ⟨M, hM, hbounds⟩ := exists_endTransition_derivative_bound e hK hKU
  obtain ⟨C, hC, hcompare⟩ := exists_coordinate_transport_density_bound qH qA qS
    (show 0 ≤ M by linarith)
  refine ⟨C, hC, ?_⟩
  intro g0 g1 h0 h1 D0 D1 E0 E1 p r hr hm0 hm1 x hx hshift
  have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
  have hxO : x ∈ endReferenceOverlap e r := hKU hshift
  have hO := endReferenceOverlap_isOpen e r hrpos
  have hf := endReferenceTransition_contMDiffOn e p r hrpos
  have hinv := endReferenceTransition_mfderiv_isInvertible e p r hrpos
  let L : V 3 →L[ℝ] V 3 := mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x
  obtain ⟨hL, hLi⟩ := hbounds r hr x hx
  dsimp only [actualDifferenceEnergyDensity]
  apply hcompare L hL (hLi hshift)
  · intro u v
    change g0.inner x u v - g1.inner x u v =
      h0.inner (endReferenceTransition e p r x) (L u) (L v) -
        h1.inner (endReferenceTransition e p r x) (L u) (L v)
    rw [hm0 x hxO, hm1 x hxO, endReferenceTransition_mfderiv e p r hrpos x hxO]
    rfl
  · intro u v
    have hi : ∀ᶠ y in 𝓝 x,
        (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y).IsInvertible := by
      filter_upwards [hO.mem_nhds hxO] with y hy
      exact hinv y hy
    have hm0' : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 3) y,
        g0.inner y a b = h0.inner (endReferenceTransition e p r y)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y a)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y b) := by
      filter_upwards [hO.mem_nhds hxO] with y hy
      exact hm0 y hy
    have hm1' : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 3) y,
        g1.inner y a b = h1.inner (endReferenceTransition e p r y)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y a)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y b) := by
      filter_upwards [hO.mem_nhds hxO] with y hy
      exact hm1 y hy
    have hh := LeviCivitaData.connection_difference_eq_of_local_isometries D0 D1 E0 E1
      ((hf x hxO).contMDiffAt (hO.mem_nhds hxO)) hi hm0' hm1' u v
    erw [endReferenceTransition_mfderiv e p r hrpos x hxO] at hh
    exact hh
  · intro u v w
    change curvatureTrilinearMap D0 x u v w - curvatureTrilinearMap D1 x u v w =
      L.inverse (curvatureTrilinearMap E0 (endReferenceTransition e p r x) (L u) (L v) (L w) -
        curvatureTrilinearMap E1 (endReferenceTransition e p r x) (L u) (L v) (L w))
    rw [map_sub]
    simp only [curvatureTrilinearMap_apply]
    rw [D0.curvature_eq_of_local_isometry E0 hO hf hm0 hxO (hinv x hxO),
      D1.curvature_eq_of_local_isometry E1 hO hf hm1 hxO (hinv x hxO),
      endReferenceTransition_mfderiv e p r hrpos x hxO]
    rfl

end PoincareMT.M34
