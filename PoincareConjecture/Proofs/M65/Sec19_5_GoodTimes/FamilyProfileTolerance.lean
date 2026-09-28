import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.ProfileTolerance
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.TimeAreaLipschitz

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

theorem m65FamilyProfileTolerance (hM61 : M61RawWidthCore.{u})
    (hM64 : M64ComparisonTheory.{u}) (compact : IsCompact (univ : Set M))
    (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta) (hab : a < b)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n : ℕ, ∃ error : ℝ, 0 < error ∧
      ∀ circumference (h : 0 < circumference), circumference < 1 → ∀ z : LoopTwoSphere,
        ∀ (time : ℕ → Icc a b) (good : Finset ℕ),
          (time 0 : ℝ) = a → (time n : ℝ) = b →
          (∀ i < n, (time i : ℝ) ≤ time (i + 1)) →
          (∀ i < n, i ∈ good →
            fillingArea (F.metric (time (i + 1)))
                ((C.solutions circumference h).projected (time (i + 1)) z) ≤
              m65RestartedAreaProfile F (time i)
                (fillingArea (F.metric (time i))
                  ((C.solutions circumference h).projected (time i) z)) (time (i + 1)) + error) →
          (∑ i ∈ Finset.range n,
            if i ∈ good then 0 else (time (i + 1) : ℝ) - time i) ≤ delta →
          fillingArea (F.metric b)
              ((C.solutions circumference h).projected ⟨b, hab.le, le_rfl⟩ z) <
            areaComparisonProfile F (fillingArea (F.metric a)
              ((C.solutions circumference h).projected ⟨a, le_rfl, hab.le⟩ z)) b + eta := by
  obtain ⟨A, hA, L, hL, hactual⟩ := m65UniformTimeFillingBounds hM61 hM64 compact V C hab
  obtain ⟨delta, hdelta, hscalar⟩ := m65FiniteProfileTolerance F compact hA.le hL.le heta
  refine ⟨delta, hdelta, ?_⟩
  intro n
  obtain ⟨error, herror, hcompare⟩ := hscalar n
  refine ⟨error, herror, ?_⟩
  intro circumference h hlt z time good hstart hend hordered hgood hgap
  let area : Icc a b → ℝ := fun t =>
    fillingArea (F.metric t) ((C.solutions circumference h).projected t z)
  let f : ℝ → ℝ := fun t => area (projIcc a b hab.le t)
  have hfun (t : Icc a b) : f t = area t := by dsimp [f]; rw [projIcc_val]
  obtain ⟨hbound, hlip⟩ := hactual circumference h hlt z
  have hbound' : ∀ t ∈ Icc a b, |f t| ≤ A := by
    intro t ht
    change |area (projIcc a b hab.le t)| ≤ A
    rw [projIcc_of_mem hab.le ht]
    exact (abs_of_nonneg (hbound ⟨t, ht⟩).1).trans_le (hbound ⟨t, ht⟩).2
  have hlip' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f t - f s| ≤ L * |t - s| := by
    intro s hs t ht
    change |area (projIcc a b hab.le t) - area (projIcc a b hab.le s)| ≤ L * |t - s|
    rw [projIcc_of_mem hab.le ht, projIcc_of_mem hab.le hs]
    exact hlip ⟨s, hs⟩ ⟨t, ht⟩
  have hresult := hcompare f (fun i => (time i : ℝ)) good hbound' hlip' hstart hend
    (fun i _ => (time i).property) hordered (by
      intro i hi hg
      simpa only [hfun] using hgood i hi hg) hgap
  simpa only [f, area, projIcc_of_mem hab.le (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩),
    projIcc_of_mem hab.le (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)] using hresult

end PoincareConjecture
