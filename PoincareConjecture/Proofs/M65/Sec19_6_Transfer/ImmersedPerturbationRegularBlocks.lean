import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationCoordinates
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationFiniteControls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

local notation "ang" => (fun x : ℝ =>
  (Subtype.mk (Proofs.M58.angularPoint x) (Proofs.M58.norm_angularPoint x) : LoopCircle))

private theorem foldControls_angle_eq {M : Type u} {n : ℕ}
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → LoopPlane → ℝ)
    (L : List (Fin n)) (p : Fin n → ℝ) (x y : ℝ)
    (hxy : Proofs.M58.angularPoint x = Proofs.M58.angularPoint y) (q : M) :
    foldControls Phi (fun j r => beta j (Proofs.M58.angularPoint r)) L p x q =
      foldControls Phi (fun j r => beta j (Proofs.M58.angularPoint r)) L p y q := by
  induction L with
  | nil => rfl
  | cons j L ih => simp only [foldControls, ih, hxy]

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {J : Set ℝ} {n : ℕ}

theorem original_values_eq_of_loopSite (C : M65SmoothFilledLoopFamily F J)
    (z w : LoopAmbient) (h : loopSite z = loopSite w) :
    z 2 = w 2 ∧
      periodicFreeLoop (C.loops (z 2)) (z 0) = periodicFreeLoop (C.loops (w 2)) (w 0) ∧
      periodicFreeLoop (C.loops (z 2)) (z 1) = periodicFreeLoop (C.loops (w 2)) (w 1) := by
  have ht : z 2 = w 2 := congrArg Prod.snd h
  have hx : ang (z 0) = ang (w 0) := congrArg (fun v => v.1.1) h
  have hy : ang (z 1) = ang (w 1) := congrArg (fun v => v.1.2) h
  refine ⟨ht, ?_, ?_⟩
  · calc
      _ = C.loops (z 2) (ang (z 0)) := (C.loops (z 2)).boundary (ang (z 0))
      _ = C.loops (w 2) (ang (w 0)) := by rw [ht, hx]
      _ = _ := ((C.loops (w 2)).boundary (ang (w 0))).symm
  · calc
      _ = C.loops (z 2) (ang (z 1)) := (C.loops (z 2)).boundary (ang (z 1))
      _ = C.loops (w 2) (ang (w 1)) := by rw [ht, hy]
      _ = _ := ((C.loops (w 2)).boundary (ang (w 1))).symm

theorem doublePointEquation_eq_of_loopSite (C : M65SmoothFilledLoopFamily F J)
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → LoopPlane → ℝ)
    (L : List (Fin n)) (q : M) (z w : LoopAmbient) (h : loopSite z = loopSite w)
    (p : Fin n → ℝ) :
    doublePointEquation C Phi (fun j x => beta j (Proofs.M58.angularPoint x)) L q (p, z) =
      doublePointEquation C Phi (fun j x => beta j (Proofs.M58.angularPoint x)) L q (p, w) := by
  have hx := congrArg Subtype.val (congrArg (fun v => v.1.1) h)
  have hy := congrArg Subtype.val (congrArg (fun v => v.1.2) h)
  obtain ⟨_, hcx, hcy⟩ := original_values_eq_of_loopSite C z w h
  simp only [doublePointEquation, hcx, hcy,
    foldControls_angle_eq Phi beta L p (z 0) (w 0) hx,
    foldControls_angle_eq Phi beta L p (z 1) (w 1) hy]

private theorem selected_derivative_eq {k : ℕ} (i : Fin k)
    (Q : (Fin (k * 3) → ℝ) × LoopAmbient → LoopAmbient)
    (w : (Fin (k * 3) → ℝ) × LoopAmbient) (hQ : DifferentiableAt ℝ Q w) :
    (fderiv ℝ (fun p => Q (p, w.2)) w.1).comp (controlBlock i) =
      (fderiv ℝ Q w).comp ((controlBlock i).prod (0 : (Fin 3 → ℝ) →L[ℝ] LoopAmbient)) := by
  have hparam : fderiv ℝ (fun p => Q (p, w.2)) w.1 = (fderiv ℝ Q w).comp
      ((ContinuousLinearMap.id ℝ (Fin (k * 3) → ℝ)).prod
        (0 : (Fin (k * 3) → ℝ) →L[ℝ] LoopAmbient)) := by
    simpa +instances only [Function.comp_def, Prod.eta, id_eq] using!
      (hQ.hasFDerivAt.comp w.1
        ((hasFDerivAt_id (𝕜 := ℝ) w.1).prodMk (hasFDerivAt_const w.2 w.1))).fderiv
  rw [hparam]
  rfl

theorem exists_selected_block_neighborhood {k : ℕ} (i : Fin k)
    (Q : (Fin (k * 3) → ℝ) × LoopAmbient → LoopAmbient)
    (w : (Fin (k * 3) → ℝ) × LoopAmbient) (hQ : ContDiffAt ℝ 1 Q w)
    (hblock : Function.Bijective
      ((fderiv ℝ (fun p => Q (p, w.2)) w.1).comp (controlBlock i))) :
    ∃ U : Set ((Fin (k * 3) → ℝ) × LoopAmbient),
      IsOpen U ∧ w ∈ U ∧ ContDiffOn ℝ 1 Q U ∧
      ∀ v ∈ U, Function.Bijective
        ((fderiv ℝ (fun p => Q (p, v.2)) v.1).comp (controlBlock i)) := by
  let B : ((Fin (k * 3) → ℝ) × LoopAmbient) → (Fin 3 → ℝ) →L[ℝ] LoopAmbient :=
    fun v => (fderiv ℝ Q v).comp ((controlBlock i).prod (0 : (Fin 3 → ℝ) →L[ℝ] LoopAmbient))
  have hB : ContinuousAt B w :=
    (hQ.continuousAt_fderiv one_ne_zero).clm_comp continuousAt_const
  have hBw : Function.Bijective (B w) := by
    change Function.Bijective ((fderiv ℝ Q w).comp
      ((controlBlock i).prod (0 : (Fin 3 → ℝ) →L[ℝ] LoopAmbient)))
    rw [← selected_derivative_eq i Q w hQ.differentiableAt_one]
    exact hblock
  let A : (Fin 3 → ℝ) ≃L[ℝ] LoopAmbient := ContinuousLinearEquiv.ofBijective (B w)
    (LinearMap.ker_eq_bot.mpr hBw.1) (LinearMap.range_eq_top.mpr hBw.2)
  have hBrange : B w ∈ range ((↑) : ((Fin 3 → ℝ) ≃L[ℝ] LoopAmbient) →
      (Fin 3 → ℝ) →L[ℝ] LoopAmbient) := ⟨A, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  have hnear := hB.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds hBrange)
  obtain ⟨O, hO, hQO⟩ := hQ.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUsub, hU, hwU⟩ := _root_.mem_nhds_iff.mp (inter_mem hO hnear)
  have hQU : ContDiffOn ℝ 1 Q U := hQO.mono (fun _ hx => (hUsub hx).1)
  refine ⟨U, hU, hwU, hQU, ?_⟩
  intro v hv
  rw [selected_derivative_eq i Q v (hQU.contDiffAt (hU.mem_nhds hv)).differentiableAt_one]
  obtain ⟨e, he⟩ := (hUsub hv).2
  change Function.Bijective (B v)
  rw [← he]
  exact e.bijective

end PoincareConjecture.M65Perturbation
