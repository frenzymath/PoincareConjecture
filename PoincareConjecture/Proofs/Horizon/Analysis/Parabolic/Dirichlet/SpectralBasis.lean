import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Dirichlet.CompactSpectral

open Module.End
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def NonzeroEigenvalue (T : H →L[ℝ] H) :=
  { μ : ℝ // μ ≠ 0 ∧ HasEigenvalue T.toLinearMap μ }

def BasisIndex (T : H →L[ℝ] H) :=
  Σ μ : NonzeroEigenvalue T, Fin (Module.finrank ℝ (eigenspace T.toLinearMap μ.1))

def eigenspaceBasis (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (μ : NonzeroEigenvalue T) :
    OrthonormalBasis (Fin (Module.finrank ℝ (eigenspace T.toLinearMap μ.1)))
      ℝ (eigenspace T.toLinearMap μ.1) := by
  letI := ContinuousLinearMap.finite_dimensional_eigenspace hT μ.1 μ.2.1
  exact stdOrthonormalBasis ℝ (eigenspace T.toLinearMap μ.1)

def basisVector (T : H →L[ℝ] H) (hT : IsCompactOperator T) (i : BasisIndex T) : H :=
  eigenspaceBasis T hT i.1 i.2

theorem basisVector_mem (T : H →L[ℝ] H) (hT : IsCompactOperator T) (i : BasisIndex T) :
    basisVector T hT i ∈ eigenspace T.toLinearMap i.1.1 :=
  (eigenspaceBasis T hT i.1 i.2).property

theorem basisVector_orthonormal (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) : Orthonormal ℝ (basisVector T hT) := by
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
  have hfamily := hsym.orthogonalFamily_eigenspaces.comp
    (fun μ ν h => (Subtype.ext h : (μ : NonzeroEigenvalue T) = ν))
  exact hfamily.orthonormal_sigma_orthonormal (fun μ => (eigenspaceBasis T hT μ).orthonormal)

theorem eigenspace_le_span_basisVector (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (μ : NonzeroEigenvalue T) :
    eigenspace T.toLinearMap μ.1 ≤ Submodule.span ℝ (Set.range (basisVector T hT)) := by
  intro x hx
  have hsum := congrArg (eigenspace T.toLinearMap μ.1).subtype
    ((eigenspaceBasis T hT μ).sum_repr ⟨x, hx⟩)
  simp only [map_sum, map_smul] at hsum
  change _ = x at hsum
  rw [← hsum]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨μ, k⟩, rfl⟩

theorem span_basisVector_eq_iSup (T : H →L[ℝ] H) (hT : IsCompactOperator T) :
    Submodule.span ℝ (Set.range (basisVector T hT)) =
      ⨆ μ : NonzeroEigenvalue T, eigenspace T.toLinearMap μ.1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem i.1 (basisVector_mem T hT i)
  · exact iSup_le (eigenspace_le_span_basisVector T hT)

omit [CompleteSpace H] in
theorem nonzero_eigenspaces_eq_iSup (T : H →L[ℝ] H) (hinj : Function.Injective T) :
    (⨆ μ : NonzeroEigenvalue T, eigenspace T.toLinearMap μ.1) =
      ⨆ μ : ℝ, eigenspace T.toLinearMap μ := by
  apply le_antisymm
  · exact iSup_le fun μ => le_iSup (fun ν : ℝ => eigenspace T.toLinearMap ν) μ.1
  · refine iSup_le fun μ => ?_
    by_cases hzero : μ = 0
    · rw [hzero, eigenspace_zero, LinearMap.ker_eq_bot.mpr hinj]
      exact bot_le
    · by_cases heigen : HasEigenvalue T.toLinearMap μ
      · exact le_iSup (fun ν : NonzeroEigenvalue T => eigenspace T.toLinearMap ν.1)
          ⟨μ, hzero, heigen⟩
      · rw [hasEigenvalue_iff, not_not] at heigen
        rw [heigen]
        exact bot_le

theorem span_basisVector_orthogonal_eq_bot (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) (hinj : Function.Injective T) :
    (Submodule.span ℝ (Set.range (basisVector T hT)))ᗮ = ⊥ := by
  rw [span_basisVector_eq_iSup, nonzero_eigenspaces_eq_iSup T hinj]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself)

def hilbertBasis (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) (hinj : Function.Injective T) :
    HilbertBasis (BasisIndex T) ℝ H :=
  HilbertBasis.mkOfOrthogonalEqBot (basisVector_orthonormal T hT hself)
    (span_basisVector_orthogonal_eq_bot T hT hself hinj)

@[simp] theorem hilbertBasis_apply (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) (hinj : Function.Injective T) (i : BasisIndex T) :
    hilbertBasis T hT hself hinj i = basisVector T hT i :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

theorem apply_hilbertBasis (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) (hinj : Function.Injective T) (i : BasisIndex T) :
    T (hilbertBasis T hT hself hinj i) = i.1.1 • hilbertBasis T hT hself hinj i := by
  rw [hilbertBasis_apply]
  exact (mem_eigenspace_iff).mp (basisVector_mem T hT i)

theorem hilbertBasis_dense (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) (hinj : Function.Injective T) :
    Dense (Submodule.span ℝ (Set.range (hilbertBasis T hT hself hinj)) : Set H) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    (hilbertBasis T hT hself hinj).dense_span]
  rfl

end Poincare.Analysis.Dirichlet.CompactSpectral
