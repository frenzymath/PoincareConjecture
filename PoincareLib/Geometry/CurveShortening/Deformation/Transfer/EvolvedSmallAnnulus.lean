import PoincareLib.Geometry.CurveShortening.Deformation.Transfer.AnnularInfimum

/-!
# An actual small annulus at each included time

The annular-evolution step of Morgan--Tian Claim 19.32, printed pp. 463-464.
A strict upper bound for a nonempty annular infimum supplies an admissible
annulus below the threshold; no minimizer or regularity of a minimizer is used.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta circumference : ℝ} {h : 0 < circumference}
  {approximation : M63RawApproximation F Gamma zeta}

/-- A uniform initial-area cutoff gives actual evolved annuli below the
specified comparison threshold; Claim 19.32, pp. 463-464. -/
theorem m65EvolvedSmallAnnulus
    (S : M63ProductSolutionFamily (G.product circumference h) approximation)
    (evolution : M64AnnulusEvolution G) (z w : LoopTwoSphere)
    {mu epsilon : ℝ} (hmu : 0 < mu)
    (hthreshold : Real.exp (5 * G.K0 * (b - a)) * mu < epsilon)
    (A : M64Annulus ((G.product circumference h).flow.metric a)
      (m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (approximation.family z)))
      (m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (approximation.family w))))
    (hA : A.area < mu) (t : Set.Icc a b) :
    ∃ At : M64Annulus ((G.product circumference h).flow.metric t)
      (fun x => S.curve z x t) (fun x => S.curve w x t), At.area < epsilon := by
  have E := m65FamilyAnnulusFlow S evolution z w A
  have hexp : Real.exp (5 * G.K0 * ((t : ℝ) - a)) ≤
      Real.exp (5 * G.K0 * (b - a)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right t.2.2 a)
      (mul_nonneg (by norm_num) G.nonnegative.1)
  have harea := (m65FamilyAnnulusArea_le_initial S z w E A t).trans_lt
    ((mul_lt_mul_of_pos_left hA (Real.exp_pos _)).trans_le
      (mul_le_mul_of_nonneg_right hexp hmu.le))
  have hne : (m64AnnulusAreaRange ((G.product circumference h).flow.metric t)
      (fun x => S.curve z x t) (fun x => S.curve w x t)).Nonempty := by
    obtain ⟨At⟩ := E.nonempty t t.2
    exact ⟨At.area, At, rfl⟩
  obtain ⟨area, ⟨At, rfl⟩, hAt⟩ := exists_lt_of_csInf_lt hne (harea.trans hthreshold)
  exact ⟨At, hAt⟩

end PoincareMT
