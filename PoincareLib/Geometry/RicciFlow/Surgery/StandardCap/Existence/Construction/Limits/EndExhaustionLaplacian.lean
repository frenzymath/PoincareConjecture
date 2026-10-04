import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Coordinates.PartialFlowFirstJetBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.TranslatedEndCharts
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.PullbackLaplacianEstimate
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.SpatialCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.ConnectionScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.FixedExtension
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeClosure
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Evolution.Scalar.SpatialCoefficients

/-!
# A global evolving Laplacian bound for the original height

Translated initial isometries turn the whole end into one compact
reference problem. The cap core uses ordinary spacetime continuity.
The resulting constant is uniform in space and included time on each
available closed slab (Morgan-Tian Theorem 12.5, pp. 296-297).
-/

set_option autoImplicit false
-- The first metric jet is a three-times-curried continuous linear map.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

set_option backward.isDefEq.respectTransparency false in
/-- The original proper height has uniformly bounded evolving Laplacian
on its whole far end through a bounded-curvature horizon
(Theorem 12.5, pp. 296-297). -/
theorem partialFlow_end_laplacian_bound (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico 0 S, ∀ z : StandardCylinderSpace, 3 ≤ z.2 →
      |(F.flow.connection t).laplacian (endExhaustion g0.cylindrical_end)
        (g0.cylindrical_end.coordinate z)| ≤ C := by
  let e := g0.cylindrical_end
  have hK := endReferenceSection_isCompact e
  obtain ⟨a, b, ha, _hb, hell⟩ := partialFlow_compactPullback_ellipticity P F
    hSF hB.le hfull hK
  obtain ⟨G, _hG, hmetric⟩ := partialFlow_compactPullback_firstJet_bound P E0 F
    hS hSF hB hfull hK
  have hf : ContDiff ℝ ∞ (endExhaustion e) :=
    contMDiff_iff_contDiff.mp (endExhaustion_contMDiff e)
  have hfirst := hf.fderiv_right (m := ∞) (by simp)
  have hsecond := hfirst.fderiv_right (m := ∞) (by simp)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ (endExhaustion e))
    hfirst.continuous.continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ (endExhaustion e))) hsecond.continuous.continuousOn
  let C := 3 * ((B2 + B1 * ((3 / (2 * a)) * G)) / a)
  refine ⟨max C 0, le_max_right _ _, fun t ht z hz => ?_⟩
  obtain ⟨x, hx, hxeq⟩ := endTranslation_covers_tail e z
  have hxU := endReferenceSection_subset_region e hx
  let f := endAxialTranslation e (z.2 - 4)
  have hmap := endTranslation_contMDiffOn e hz
  have hi := fun y hy => endTranslation_mfderiv_isInvertible e hz (x := y) hy
  have hform := fun y hy u v => endTranslation_metric e hz (x := y) hy u v
  have hgerm : (fun y => endExhaustion e (f y) - (z.2 - 4)) =ᶠ[𝓝 x]
      endExhaustion e := by
    filter_upwards [(endReferenceRegion_isOpen e).mem_nhds hxU] with y hy
    exact endExhaustion_translation_eq e hz hy
  have hscalar1 : ‖fderiv ℝ (fun y => endExhaustion e (f y) - (z.2 - 4)) x‖ ≤ B1 := by
    rw [hgerm.fderiv_eq]
    exact hB1 x hx
  have hscalar2 :
      ‖fderiv ℝ (fderiv ℝ (fun y => endExhaustion e (f y) - (z.2 - 4))) x‖ ≤ B2 := by
    rw [hgerm.fderiv.fderiv_eq]
    exact hB2 x hx
  have h := (F.flow.connection t).abs_laplacian_le_of_pullback_bounds
    (endReferenceRegion_isOpen e) hmap hi hxU (endExhaustion_contMDiff e (f x)) (z.2 - 4)
    ha (fun v => (hell t ht x hx f (hform x hxU) v).1) hscalar1 hscalar2
    (hmetric (endReferenceRegion_isOpen e) hmap hi hform t ht x hx hxU)
  change |(F.flow.connection t).laplacian (endExhaustion e) (f x)| ≤ C at h
  dsimp only [f] at h
  rw [hxeq] at h
  exact h.trans (le_max_left _ _)

/-- The fixed smooth proper height has one global Laplacian bound on
every included closed slab of every partial flow
(Theorem 12.5, pp. 296-297). -/
theorem partialFlow_exhaustion_laplacian_bound (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {T : ℝ} (hT : 0 ≤ T) (hTF : T < F.lifetime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace,
      |(F.flow.connection t).laplacian (endExhaustion g0.cylindrical_end) x| ≤ C := by
  let S := (T + F.lifetime) / 2
  have hS : 0 < S := by dsimp [S]; linarith [F.lifetime_pos]
  have hTS : T < S := by dsimp [S]; linarith
  have hSF : S < F.lifetime := by dsimp [S]; linarith
  obtain ⟨K, _hK, hfull⟩ := F.curvature_locally_bounded S hS.le hSF
  obtain ⟨C1, hC1, hend⟩ := partialFlow_end_laplacian_bound P E0 F hS hSF.le
    (lt_of_lt_of_le zero_lt_one (le_max_right K 1))
    (fun s hs x => ((le_abs_self _).trans (hfull s ⟨hs.1, hs.2.le⟩ x)).trans
      (le_max_left _ _))
  let e := g0.cylindrical_end
  have hc := (M04.continuousOn_flow_laplacian F.flow isOpen_univ
    (endExhaustion_contMDiff e).contMDiffOn).mono
    (show Icc 0 T ×ˢ endTruncatedCore e 3 ⊆ Ico 0 F.lifetime ×ˢ univ
      from fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hTF⟩, mem_univ _⟩)
  have hcompact := (isCompact_Icc (a := (0 : ℝ)) (b := T)).prod
    (endTruncatedCore_isCompact e (by norm_num : (0 : ℝ) ≤ 3))
  obtain ⟨C0, hC0⟩ := hcompact.exists_bound_of_continuousOn hc
  refine ⟨max C0 C1, hC1.trans (le_max_right _ _), fun t ht x => ?_⟩
  by_cases hx : x ∈ endTruncatedCore e 3
  · exact (hC0 (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · have htail : x ∈ e.coordinate '' (univ ×ˢ Ioi (3 : ℝ)) := not_not.mp hx
    obtain ⟨z, hz, rfl⟩ := htail
    exact (hend t ⟨ht.1, ht.2.trans_lt hTS⟩ z hz.2.le).trans (le_max_right _ _)

end PoincareMT.M34
