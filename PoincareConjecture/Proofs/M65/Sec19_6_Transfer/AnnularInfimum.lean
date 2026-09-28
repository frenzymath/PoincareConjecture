import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.ProjectedAreaEstimate
import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta circumference : ℝ} {h : 0 < circumference}
  {approximation : M63RawApproximation F Gamma zeta}
  (S : M63ProductSolutionFamily (G.product circumference h) approximation)

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

end PoincareConjecture
