import PoincareConjecture.Proofs.M03.Existence.HilbertResolventNative
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open TopologicalSpace

namespace PoincareConjecture.HilbertResolventNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev NonzeroParameter := {mu : ℝ // mu ≠ 0}

def eigenSpace (J : V →L[ℝ] H) (mu : NonzeroParameter) : Submodule ℝ H :=
  Module.End.eigenspace (operator J).toLinearMap mu.val

abbrev EigenIndex (J : V →L[ℝ] H) :=
  (mu : NonzeroParameter) × Fin (Module.finrank ℝ (eigenSpace J mu))

def eigenspaceBasis (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (mu : NonzeroParameter) :
    OrthonormalBasis (Fin (Module.finrank ℝ (eigenSpace J mu))) ℝ (eigenSpace J mu) := by
  letI : FiniteDimensional ℝ (eigenSpace J mu) :=
    eigenspace_finiteDimensional J hc mu.val mu.property
  exact stdOrthonormalBasis ℝ (eigenSpace J mu)

def eigenvector (J : V →L[ℝ] H) (hc : IsCompactOperator J) (i : EigenIndex J) : H :=
  eigenspaceBasis J hc i.1 i.2

theorem eigenvector_mem (J : V →L[ℝ] H) (hc : IsCompactOperator J) (i : EigenIndex J) :
    eigenvector J hc i ∈ eigenSpace J i.1 := (eigenspaceBasis J hc i.1 i.2).property

theorem operator_eigenvector (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (i : EigenIndex J) : operator J (eigenvector J hc i) = i.1.val • eigenvector J hc i :=
  Module.End.mem_eigenspace_iff.mp (eigenvector_mem J hc i)

theorem eigenvector_orthonormal (J : V →L[ℝ] H) (hc : IsCompactOperator J) :
    Orthonormal ℝ (eigenvector J hc) := by
  have hfamily : OrthogonalFamily ℝ (fun mu : NonzeroParameter => eigenSpace J mu)
      (fun mu => (eigenSpace J mu).subtypeₗᵢ) :=
    (operator_isSymmetric J).orthogonalFamily_eigenspaces.comp Subtype.coe_injective
  exact hfamily.orthonormal_sigma_orthonormal (fun mu => (eigenspaceBasis J hc mu).orthonormal)

theorem eigenvector_ne_zero (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (i : EigenIndex J) : eigenvector J hc i ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [(eigenvector_orthonormal J hc).norm_eq_one]
  exact one_ne_zero

theorem span_eigenvectors (J : V →L[ℝ] H) (hc : IsCompactOperator J) :
    Submodule.span ℝ (Set.range (eigenvector J hc)) = ⨆ mu, eigenSpace J mu := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (le_iSup (eigenSpace J) i.1) (eigenvector_mem J hc i)
  · refine iSup_le (fun mu => ?_)
    intro x hx
    let y : eigenSpace J mu := ⟨x, hx⟩
    have hsum : (∑ j, (eigenspaceBasis J hc mu).repr y j •
        eigenvector J hc ⟨mu, j⟩) = x := by
      have h := congrArg (fun z : eigenSpace J mu => (z : H))
        ((eigenspaceBasis J hc mu).sum_repr y)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, eigenvector, y] using h
    rw [← hsum]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨mu, j⟩, rfl⟩))

theorem nonzero_eigenspaces_eq_all (J : V →L[ℝ] H) (hd : DenseRange J) :
    (⨆ mu, eigenSpace J mu) =
      ⨆ mu : ℝ, Module.End.eigenspace (operator J).toLinearMap mu := by
  apply le_antisymm
  · exact iSup_le (fun mu => le_iSup _ mu.val)
  · refine iSup_le (fun mu => ?_)
    by_cases hmu : mu = 0
    · subst mu
      intro x hx
      have heq : operator J x = 0 := by
        simpa using Module.End.mem_eigenspace_iff.mp hx
      have hx0 : x = 0 := operator_injective J hd (by simpa using heq)
      simpa only [hx0] using (Submodule.zero_mem (⨆ mu, eigenSpace J mu))
    · exact le_iSup (eigenSpace J) ⟨mu, hmu⟩

theorem eigenvectors_total (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) : (Submodule.span ℝ (Set.range (eigenvector J hc)))ᗮ = ⊥ := by
  rw [span_eigenvectors, nonzero_eigenspaces_eq_all J hd]
  exact eigenspaces_total J hc

def eigenbasis (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J) :
    HilbertBasis (EigenIndex J) ℝ H :=
  HilbertBasis.mkOfOrthogonalEqBot (eigenvector_orthonormal J hc) (eigenvectors_total J hc hd)

@[simp] theorem eigenbasis_apply (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (i : EigenIndex J) : eigenbasis J hc hd i = eigenvector J hc i := by
  simp only [eigenbasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem repr_operator (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (f : H) (i : EigenIndex J) :
    (eigenbasis J hc hd).repr (operator J f) i =
      i.1.val * (eigenbasis J hc hd).repr f i := by
  simp only [HilbertBasis.repr_apply_apply, eigenbasis_apply]
  rw [inner_operator_right, ← inner_operator_left, operator_eigenvector]
  simp only [real_inner_smul_left]

theorem eigenparameter_pos (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (i : EigenIndex J) : 0 < i.1.val :=
  eigenvalue_pos J hd (eigenvector_ne_zero J hc i) (operator_eigenvector J hc i)

theorem eigenparameter_le_one (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (i : EigenIndex J) : i.1.val ≤ 1 :=
  eigenvalue_le_one J hd hnorm (eigenvector_ne_zero J hc i) (operator_eigenvector J hc i)

def generatorParameters (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (i : EigenIndex J) : NNReal :=
  parameter i.1.val (eigenparameter_pos J hc hd i) (eigenparameter_le_one J hc hd hnorm i)

@[simp] theorem generatorParameters_coe (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (i : EigenIndex J) :
    (generatorParameters J hc hd hnorm i : ℝ) = i.1.val⁻¹ - 1 := rfl

theorem orthonormal_index_countable {iota : Type*} [SeparableSpace H]
    {e : iota → H} (he : Orthonormal ℝ e) : Countable iota := by
  classical
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense H
  haveI : Countable D := hD.to_subtype
  have hex (i : iota) : ∃ d : D, dist (d : H) (e i) < (1 / 3 : ℝ) := by
    obtain ⟨d, hdD, hball⟩ := hd.exists_mem_open Metric.isOpen_ball
      (Metric.nonempty_ball.mpr (by norm_num : (0 : ℝ) < 1 / 3))
    exact ⟨⟨d, hdD⟩, hball⟩
  choose pick hp using hex
  apply Function.Injective.countable (f := pick)
  intro i j hij
  by_contra hne
  have hs : dist (e i) (e j) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, he.norm_eq_one i, he.norm_eq_one j, he.inner_eq_zero hne]
    norm_num
  have hleft : dist (e i) (pick i : H) < (1 / 3 : ℝ) := by
    simpa only [dist_comm] using hp i
  have hright : dist (pick i : H) (e j) < (1 / 3 : ℝ) := by
    rw [hij]
    exact hp j
  have hdist : dist (e i) (e j) < 1 := by
    linarith [dist_triangle (e i) (pick i : H) (e j)]
  have hslt : dist (e i) (e j) ^ 2 < (1 : ℝ) ^ 2 :=
    (sq_lt_sq₀ dist_nonneg zero_le_one).mpr hdist
  linarith

theorem eigenIndex_countable [SeparableSpace H] (J : V →L[ℝ] H)
    (hc : IsCompactOperator J) : Countable (EigenIndex J) :=
  orthonormal_index_countable (eigenvector_orthonormal J hc)

end PoincareConjecture.HilbertResolventNative
