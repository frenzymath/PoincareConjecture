import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Paths.ClosedPathJointSmooth
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Paths.ClosedPathSubstitution

/-!
# Actual closed time jets of a smooth ODE family

Morgan-Tian Lemma 6.18, pp. 113-114. Repeated differentiation along
the actual vector (1,f) supplies smooth closed time jets. Substitution
in a smooth family of continuous paths and the actual within ODE give
the hypotheses for joint smoothness at the closed endpoints.
-/

set_option autoImplicit false

open Set
open scoped Topology ContDiff

namespace PoincareMT.M14

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {a b : ℝ}

/-- Repeated differentiation of the state projection along the actual
closed-time ODE vector gives its time-jet coefficients, Lemma 6.18,
pp. 113-114. -/
noncomputable def closedODETimeJet (C : Set ℝ) (f : ℝ × E → E) : ℕ → ℝ × E → E
  | 0 => Prod.snd
  | j + 1 => fun z => fderivWithin ℝ (closedODETimeJet C f j) (C ×ˢ univ) z (1, f z)

omit [FiniteDimensional ℝ E] in
/-- The actual time-jet coefficients are smooth on their original
closed slab, retaining within derivatives, Lemma 6.18, pp. 113-114. -/
theorem closedODETimeJet_contDiffOn {C : Set ℝ} (hC : UniqueDiffOn ℝ C)
    (f : ℝ × E → E) (hf : ContDiffOn ℝ ∞ f (C ×ˢ univ)) (j : ℕ) :
    ContDiffOn ℝ ∞ (closedODETimeJet C f j) (C ×ˢ univ) := by
  induction j with
  | zero => exact contDiffOn_snd
  | succ j ih =>
    exact (ih.fderivWithin (hC.prod uniqueDiffOn_univ) (by simp)).clm_apply
      (contDiffOn_const.prodMk hf)

/-- An actual closed ODE family smooth into continuous paths is jointly
smooth on its open parameter set and closed time interval. The actual
ODE supplies every time jet, including endpoints, Lemma 6.18,
pp. 113-114. -/
theorem closedODEFamily_joint_contDiff (hab : a < b) (t₀ : Icc a b)
    {U : Set P} (hU : IsOpen U) (f : ℝ × E → E)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ)) (Φ : P → C(Icc a b, E))
    (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ht : ∀ x ∈ U, ∀ r : Icc a b, HasDerivWithinAt
      (fun s => Φ x (projIcc a b hab.le s)) (f (r.val, Φ x r)) (Icc a b) r.val) :
    ContDiffOn ℝ ∞ (closedPathEvaluation hab.le Φ) (U ×ˢ Icc a b) := by
  have hJ := closedODETimeJet_contDiffOn (uniqueDiffOn_Icc hab) f hf
  let Ψ : ℕ → P → C(Icc a b, E) := fun j x =>
    closedTimePostcomp (closedODETimeJet (Icc a b) f j) (hJ j).continuousOn (Φ x)
  have hΨ (j : ℕ) : ContDiffOn ℝ ∞ (Ψ j) U :=
    (closedTimePostcomp_contDiff (uniqueDiffOn_Icc hab) _ (hJ j)).comp_contDiffOn hΦ
  have hΨt (j : ℕ) (x : P) (hx : x ∈ U) (r : Icc a b) : HasDerivWithinAt
      (fun s => Ψ j x (projIcc a b hab.le s)) (Ψ (j + 1) x r) (Icc a b) r.val := by
    let γ : ℝ → ℝ × E := fun s => (s, Φ x (projIcc a b hab.le s))
    have hπ : projIcc a b hab.le r.val = r := projIcc_of_mem hab.le r.property
    have hdγ : HasDerivWithinAt γ (1, f (r.val, Φ x r)) (Icc a b) r.val :=
      (hasDerivWithinAt_id r.val (Icc a b)).prodMk (ht x hx r)
    have hγ : γ r.val ∈ Icc a b ×ˢ (univ : Set E) := ⟨r.property, mem_univ _⟩
    have hd := ((hJ j).differentiableOn (by simp) _ hγ).hasFDerivWithinAt.comp_hasDerivWithinAt
      r.val hdγ (fun s hs => ⟨hs, mem_univ _⟩)
    have hγr : γ r.val = (r.val, Φ x r) := by dsimp only [γ]; rw [hπ]
    rw [hγr] at hd
    apply hd.congr_of_mem _ r.property
    intro s hs
    change closedODETimeJet (Icc a b) f j
        ((projIcc a b hab.le s).val, Φ x (projIcc a b hab.le s)) =
      closedODETimeJet (Icc a b) f j (s, Φ x (projIcc a b hab.le s))
    rw [projIcc_of_mem hab.le hs]
  exact closedPath_timeJets_contDiff hab t₀ hU Ψ hΨ hΨt

end PoincareMT.M14
