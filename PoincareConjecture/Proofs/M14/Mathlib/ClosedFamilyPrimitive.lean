import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathCurrying
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathJointSmooth
import PoincareConjecture.Proofs.M08.ChartConnectionVariation










set_option autoImplicit false

open Set
open scoped ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {C : Set ℝ} {U : Set E}



noncomputable def closedFamilyTimeJet (C : Set ℝ) (U : Set E) (f : ℝ × E → F) :
    ℕ → ℝ × E → F
  | 0 => f
  | j + 1 => M08.timeWithinFDeriv C U (closedFamilyTimeJet C U f j)

omit [FiniteDimensional ℝ E] in



theorem closedFamilyTimeJet_contDiffOn (hC : UniqueDiffOn ℝ C) (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) (j : ℕ) :
    ContDiffOn ℝ ∞ (closedFamilyTimeJet C U f j) (C ×ˢ U) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact M08.timeWithinFDeriv_contDiffOn hC hU _ ih




theorem closedFamilyPrimitive_contDiffOn [CompleteSpace F]
    {a b : ℝ} (hab : a < b) (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => ∫ t in a..z.2, f (t, z.1)) (U ×ˢ Icc a b) := by
  let t₀ : Icc a b := ⟨a, le_rfl, hab.le⟩
  have hJ := closedFamilyTimeJet_contDiffOn (uniqueDiffOn_Icc hab) hU f hf
  choose Φ hΦ hvalue using fun j =>
    exists_contDiffOn_closedPathFamily (uniqueDiffOn_Icc hab) hU
      (closedFamilyTimeJet (Icc a b) U f j) (hJ j)
  let Ψ : ℕ → E → C(Icc a b, F)
    | 0 => fun x => closedPathPrimitive t₀ (Φ 0 x)
    | j + 1 => Φ j
  have hΨ (j : ℕ) : ContDiffOn ℝ ∞ (Ψ j) U := by
    cases j with
    | zero => exact (closedPathPrimitive (E := F) t₀).contDiff.comp_contDiffOn (hΦ 0)
    | succ j => exact hΦ j
  have ht (j : ℕ) (x : E) (hx : x ∈ U) (r : Icc a b) : HasDerivWithinAt
      (fun s => Ψ j x (projIcc a b hab.le s)) (Ψ (j + 1) x r) (Icc a b) r.val := by
    cases j with
    | zero => exact closedPathPrimitive_hasDerivWithinAt t₀ r (Φ 0 x)
    | succ j =>
      change HasDerivWithinAt (fun s => Φ j x (projIcc a b hab.le s)) (Φ (j + 1) x r)
        (Icc a b) r.val
      rw [hvalue (j + 1) x hx r]
      apply (M08.hasDerivWithinAt_timeWithin _ (hJ j) r.property hx).congr_of_mem _ r.property
      intro s hs
      rw [hvalue j x hx, projIcc_of_mem hab.le hs]
  have h := closedPath_timeJets_contDiff hab t₀ hU Ψ hΨ ht
  apply h.congr
  intro z hz
  change (∫ t in a..z.2, f (t, z.1)) =
    closedPathPrimitive t₀ (Φ 0 z.1) (projIcc a b hab.le z.2)
  rw [closedPathPrimitive_apply, projIcc_of_mem hab.le hz.2]
  apply intervalIntegral.integral_congr_Ioo_of_le hz.2.1
  intro t ht
  have htC : t ∈ Icc a b := ⟨ht.1.le, ht.2.le.trans hz.2.2⟩
  change f (t, z.1) = Φ 0 z.1 (projIcc a b hab.le t)
  rw [projIcc_of_mem hab.le htC]
  exact (hvalue 0 z.1 hz.1 ⟨t, htC⟩).symm

end PoincareConjecture.M14
