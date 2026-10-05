import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Jets.SpatialJetsWithin
import PoincareLib.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

/-!
# Actual fixed-chart jets through the birth endpoint

The metric-family smoothness in the frozen Ricci-flow record gives
continuous fixed-coordinate spatial jets up to closed time endpoints.
Morgan--Tian, Lemma 16.8 and Corollary 16.9, pp. 372-373;
see M44 derivation 34.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A fixed smooth spatial pullback is jointly smooth within the actual
time set, including its endpoints. Source: Lemma 16.8, pp. 372-373;
M44 derivation 34. -/
theorem contDiffOn_pullbackCoefficients_within {J : Set ℝ}
    (F : RicciFlow n M J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric z.1).pullbackCoefficients e z.2) (J ×ˢ U) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt F.smooth
    (he.contMDiffAt (hU.mem_nhds hx)) ht
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [RiemannianMetric.constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2)) (t, x) :=
    contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
  have hmap : MapsTo (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2))
      (J ×ˢ U) (J ×ˢ univ) := fun _ hp => ⟨hp.1, mem_univ _⟩
  convert! (hc.comp (t, x) hid.contMDiffWithinAt hmap).contDiffWithinAt using 1

/-- The actual spatial coefficient jets are continuous at every time
on a nondegenerate closed slab, including both endpoints.
Source: Corollary 16.9, p. 373; M44 derivation 34. -/
theorem continuousOn_pullback_spatialJet {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b)) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U) (m : ℕ) :
    ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      iteratedFDeriv ℝ m ((F.metric z.1).pullbackCoefficients e) z.2) (Icc a b ×ˢ U) :=
  (contDiffOn_spatialJet_within (contDiffOn_pullbackCoefficients_within F hU he)
    (uniqueDiffOn_Icc hab) hU m).continuousOn

/-- Each spatial metric jet has a smooth time line within the actual
closed interval. Source: Corollary 16.9, p. 373; M44 derivation 34. -/
theorem contDiffOn_pullback_spatialJet_time {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b)) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (m : ℕ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    ContDiffOn ℝ ∞ (fun t => iteratedFDeriv ℝ m ((F.metric t).pullbackCoefficients e) x)
      (Icc a b) :=
  contDiffOn_spatialJet_time_within (contDiffOn_pullbackCoefficients_within F hU he)
    (uniqueDiffOn_Icc hab) hU m hx

end PoincareMT.M44
