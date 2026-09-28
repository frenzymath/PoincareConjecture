import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem contDiffOn_of_C2_hessian_smooth (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ 2 f U)
    (hh : ∀ v w : EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ∞ (fun x => D.hessian f x v w) U) :
    ContDiffOn ℝ ∞ f U := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := by
    rw [contDiffOn_infty]
    intro k
    induction k with
    | zero =>
      exact (hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).of_le (by norm_num)
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨?_, by simp, ?_⟩
      · exact (hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
          (by norm_num)
      · apply contDiffOn_clm_apply.mpr
        intro v
        apply contDiffOn_clm_apply.mpr
        intro w
        have hh' := (hh v w).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hΓ' := D.contDiff_connectionCoefficient.of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hright : ContDiffOn ℝ (k : ℕ∞ω)
            (fun x => D.hessian f x v w +
              fderiv ℝ f x (D.connectionCoefficient x v w)) U :=
          hh'.add (ih.clm_apply
            ((hΓ'.contDiffOn.clm_apply contDiffOn_const).clm_apply contDiffOn_const))
        apply hright.congr
        intro x hx
        have h := D.hessian_eq_fderiv_sub_connectionCoefficient_of_C2
          (hf.contDiffAt (hU.mem_nhds hx)) v w
        change fderiv ℝ (fderiv ℝ f) x v w = _
        exact sub_eq_iff_eq_add.mp h.symm
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hU]
  exact ⟨hf.differentiableOn (by norm_num), hfd⟩

theorem contDiff_ricci_const (D : LeviCivitaData g)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun x => D.ricci x v w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hX (i : Fin 2) : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : EuclideanSpace ℝ (Fin n) => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) y (E := TangentSpace (𝓡 n)) (![v, w] i)) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using (contMDiffAt_const
      (I := 𝓡 n) (I' := 𝓡 n) (c := ![v, w] i) (x := x) (n := ∞))⟩
  have h := D.ricciEvaluation_isSmooth_manifold.contMDiffAt_apply
    (X := fun i _ => ![v, w] i) hX
  simpa [ricciEvaluation] using h.contDiffAt

end PoincareConjecture.LeviCivitaData
