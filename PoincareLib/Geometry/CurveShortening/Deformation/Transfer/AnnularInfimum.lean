import PoincareLib.Geometry.CurveShortening.Ramp.Adapters
import PoincareLib.Geometry.CurveShortening.Deformation.SweptArea.ProjectedAreaEstimate
import PoincareLib.Geometry.CurveShortening.Comparison.Theory

/-!
# Evolved annuli compare the actual projected filling areas

The area comparison in Lemma 19.30, printed pp. 461-462, using Corollary
19.16, pp. 448-449. Nonempty annulus and disk classes are established before
their infima are used. One fixed product solution family is retained.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta circumference : ℝ} {h : 0 < circumference}
  {approximation : M63RawApproximation F Gamma zeta}
  (S : M63ProductSolutionFamily (G.product circumference h) approximation)

/-- Corollary 19.16 on the exact pair of solution curves, as used in
Lemma 19.30, pp. 461-462. The canonical initial annulus is retained. -/
theorem m65FamilyAnnulusFlow (evolution : M64AnnulusEvolution G)
    (z w : LoopTwoSphere)
    (A : M64Annulus ((G.product circumference h).flow.metric a)
      (m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (approximation.family z)))
      (m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (approximation.family w)))) :
    M64AnnulusFlowConclusion G h (S.curve z) (S.curve w) := by
  have hab : a ≤ b := by
    obtain ⟨t, ht⟩ := F.nontrivial.nonempty
    exact ht.1.trans ht.2
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  apply evolution.curves circumference h (S.curve z) (S.curve w)
    (m63C2_of_m62 (S.shrinking z)) (m63C2_of_m62 (S.shrinking w))
    (S.ramp z a ha) (S.ramp w a ha) (S.degree_one z a ha) (S.degree_one w a ha)
  simpa only [S.initial_eq] using A

/-- The projected filling-area difference is a lower bound of the nonempty
annular area range; Lemma 19.30, p. 462. -/
theorem m65ProjectedAreaDifference_le_infimum
    (projection : ∀ t ∈ Set.Icc a b,
      M64AnnulusProjection (G.product circumference h) t)
    (disks : ∀ t ∈ Set.Icc a b,
      M64DiskAreaComparison (G.product circumference h) t)
    (z w : LoopTwoSphere)
    (E : M64AnnulusFlowConclusion G h (S.curve z) (S.curve w))
    (t : Set.Icc a b)
    (D : LipschitzSpanningDisk (F.metric t) (S.projected t z)) :
    |fillingArea (F.metric t) (S.projected t w) -
      fillingArea (F.metric t) (S.projected t z)| ≤
        m64FlowAnnulusArea (G.product circumference h) (S.curve z) (S.curve w) t := by
  apply le_csInf
  · obtain ⟨A⟩ := E.nonempty t t.2
    exact ⟨A.area, A, rfl⟩
  · rintro area ⟨A, rfl⟩
    obtain ⟨_, _, harea⟩ := m65ProjectedDiskComparison (projection t t.2)
      (disks t t.2 _ _ A _ _ (S.projected_eq t z) (S.projected_eq t w)) D
    exact harea

/-- The evolved annular infimum is bounded by the actual initial annulus
with M64's common exponential factor; Lemma 19.30, p. 462. -/
theorem m65FamilyAnnulusArea_le_initial
    (z w : LoopTwoSphere)
    (E : M64AnnulusFlowConclusion G h (S.curve z) (S.curve w))
    (A : M64Annulus ((G.product circumference h).flow.metric a)
      (m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (approximation.family z)))
      (m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (approximation.family w))))
    (t : Set.Icc a b) :
    m64FlowAnnulusArea (G.product circumference h) (S.curve z) (S.curve w) t ≤
      Real.exp (5 * G.K0 * ((t : ℝ) - a)) * A.area := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, t.2.1.trans t.2.2⟩
  have hstart : m64FlowAnnulusArea (G.product circumference h)
      (S.curve z) (S.curve w) a ≤ A.area := by
    simp only [m64FlowAnnulusArea, S.initial_eq]
    have hb := E.bounded_below a ha
    simp only [S.initial_eq] at hb
    exact csInf_le hb ⟨A, rfl⟩
  have hflow := E.exponential a t ha t.2 t.2.1
  norm_num at hflow
  exact hflow.trans (mul_le_mul_of_nonneg_left hstart (Real.exp_nonneg _))

end PoincareMT
