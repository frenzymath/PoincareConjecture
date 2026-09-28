import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SuppliedCanonicalBounds
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SliceCongruence
import PoincareConjecture.Proofs.M63.Adapters

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

theorem m63FamilyConclusion_of_solutions (G : M63AmbientGeometry F)
    (Q : M63AnalyticConclusion F G) (A : M63RawApproximation F Gamma zeta)
    (solutions : ∀ circumference (h : 0 < circumference),
      M63ProductSolutionFamily (G.product circumference h) A) :
    Nonempty {C : M63FamilyConclusion G Gamma zeta // C.approximation = A} := by
  let L := m63FamilyLengthSup (F.metric a) Gamma
  let Theta := (A.count : ℝ) * Real.pi
  let B := max (L + 1) Theta + 1
  have hlengths := m63FamilyLengthSup_properties (F.metric a) Gamma
  have hL : 0 ≤ L := hlengths.2.2.1
  have hB : 0 < B := by
    have h := le_max_left (L + 1) Theta
    dsimp only [B]
    linarith
  have hBL : L + 1 ≤ B := by
    have h := le_max_left (L + 1) Theta
    dsimp only [B]
    linarith
  have hBTheta : Theta ≤ B := by
    have h := le_max_right (L + 1) Theta
    dsimp only [B]
    linarith
  obtain ⟨D⟩ := Q.uniform_derivatives B B hB.le hB.le
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hcanonicalL (circumference : ℝ) (h : 0 < circumference) (hsmall : circumference < 1)
      (z : LoopTwoSphere) :
      m62Length (G.product circumference h).flow
        (fun x _ => m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (A.family z)) x) a ≤ L + 1 :=
    (A.canonical_length_le (G.product circumference h) z).trans (add_le_add le_rfl hsmall.le)
  have hcanonicalTheta (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) :
      m62TotalCurvature (G.product circumference h).flow
        (fun x _ => m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (A.family z)) x) a ≤ Theta :=
    A.canonical_totalCurvature_le (G.product circumference h) z
  have hinitialL (circumference : ℝ) (h : 0 < circumference) (hsmall : circumference < 1)
      (z : LoopTwoSphere) :
      m62Length (G.product circumference h).flow (solutions circumference h |>.curve z) a ≤
        L + 1 := by
    rw [M63.length_congr_slice (G.product circumference h).flow
      (d := fun x _ => m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (A.family z)) x)
      (solutions circumference h |>.initial_eq z)]
    exact hcanonicalL circumference h hsmall z
  have hinitialTheta (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) :
      m62TotalCurvature (G.product circumference h).flow
        (solutions circumference h |>.curve z) a ≤ Theta := by
    rw [M63.totalCurvature_congr_slice (G.product circumference h).flow
      (d := fun x _ => m63CanonicalRamp (G.product circumference h)
        (periodicFreeLoop (A.family z)) x)
      (solutions circumference h |>.initial_eq z)]
    exact hcanonicalTheta circumference h z
  let C : M63FamilyConclusion G Gamma zeta :=
    { approximation := A
      source_lengths_bounded := hlengths.1
      source_length_attained := hlengths.2.1
      initial_bound := B
      initial_bound_positive := hB
      initial_length_bound := hBL
      initial_turning_bound := hBTheta
      derivative_estimates := D
      canonical_length := hcanonicalL
      canonical_total_curvature := hcanonicalTheta
      solutions := solutions
      length_bound := by
        intro circumference h hsmall z t ht
        have E := Q.product_estimates circumference h b hab le_rfl
          (solutions circumference h |>.curve z)
          (m63C2_of_m62 (solutions circumference h |>.shrinking z))
        exact (E.length_exponential a t ha ht ht.1).trans
          (mul_le_mul_of_nonneg_right (hinitialL circumference h hsmall z)
            (Real.exp_pos _).le)
      total_bound := by
        intro circumference h hsmall z t ht
        have E := Q.product_estimates circumference h b hab le_rfl
          (solutions circumference h |>.curve z)
          (m63C2_of_m62 (solutions circumference h |>.shrinking z))
        apply (E.total_exponential a t ha ht ht.1).trans
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have hsum := add_le_add (hinitialTheta circumference h z)
          (hinitialL circumference h hsmall z)
        simpa only [add_comm] using hsum }
  exact ⟨⟨C, rfl⟩⟩

end PoincareConjecture
