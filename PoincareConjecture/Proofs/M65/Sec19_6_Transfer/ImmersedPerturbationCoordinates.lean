import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationControlAssembly
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationZeroChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M65Perturbation

def controlCoordinates {k : ℕ} (i : Fin k) : (Fin (k * 3) → ℝ) ≃L[ℝ]
    LoopAmbient × ({j : Fin k // j ≠ i} → Fin 3 → ℝ) :=
  let e : (Fin (k * 3) → ℝ) ≃ₗ[ℝ]
      (Fin 3 → ℝ) × ({j : Fin k // j ≠ i} → Fin 3 → ℝ) :=
    { toEquiv := ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl ℝ)).trans
        (Equiv.curry (Fin k) (Fin 3) ℝ)).trans (Equiv.funSplitAt i (Fin 3 → ℝ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  e.toContinuousLinearEquiv.trans
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.prodCongr
      (ContinuousLinearEquiv.refl ℝ _))

theorem controlCoordinates_block {k : ℕ} (i : Fin k) (u : Fin 3 → ℝ) :
    controlCoordinates i (controlBlock i u) = (WithLp.toLp 2 u, 0) := by
  apply Prod.ext
  · apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext j
    change (if (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 = i then
      ContinuousLinearMap.proj (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 else 0) u = u j
    rw [finProdFinEquiv.symm_apply_apply]
    simp
  · ext j l
    change (if (finProdFinEquiv.symm (finProdFinEquiv (j.1, l))).1 = i then
      ContinuousLinearMap.proj (finProdFinEquiv.symm (finProdFinEquiv (j.1, l))).2 else 0) u = 0
    rw [finProdFinEquiv.symm_apply_apply]
    simp [j.2]

theorem controlCoordinates_symm_fst {k : ℕ} (i : Fin k) (u : LoopAmbient) :
    (controlCoordinates i).symm (u, 0) = controlBlock i u.ofLp := by
  apply (controlCoordinates i).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, controlCoordinates_block]

set_option maxHeartbeats 800000 in

theorem exists_control_zero_chart {k : ℕ} (i : Fin k)
    (Q : (Fin (k * 3) → ℝ) × LoopAmbient → LoopAmbient)
    (w : (Fin (k * 3) → ℝ) × LoopAmbient)
    (hQ : ContDiffAt ℝ 1 Q w) (hw : Q w = 0)
    (hblock : Function.Bijective
      ((fderiv ℝ (fun p => Q (p, w.2)) w.1).comp (controlBlock i))) :
    ∃ (U : Set (Fin (k * 3) → ℝ)) (W : Set ((Fin (k * 3) → ℝ) × LoopAmbient))
        (phi : (Fin (k * 3) → ℝ) → (Fin (k * 3) → ℝ) × LoopAmbient)
        (coordinate : (Fin (k * 3) → ℝ) × LoopAmbient → (Fin (k * 3) → ℝ)),
      IsOpen U ∧ IsOpen W ∧ w ∈ W ∧ ContDiffOn ℝ 1 phi U ∧ Continuous coordinate ∧
      (∀ v ∈ U, Q (phi v) = 0 ∧ coordinate (phi v) = v) ∧
      (∀ z ∈ W, Q z = 0 → coordinate z ∈ U ∧ phi (coordinate z) = z) := by
  let e := controlCoordinates i
  let T := e.symm.prodCongr (ContinuousLinearEquiv.refl ℝ LoopAmbient)
  let v := (e w.1, w.2)
  have hTv : T v = w := by simp [T, v]
  have hQt : ContDiffAt ℝ 1 (Q ∘ T) v := by
    apply (hTv ▸ hQ).comp v T.contDiff.contDiffAt
  have hderiv : fderiv ℝ (Q ∘ T) v = (fderiv ℝ Q w).comp T.toContinuousLinearMap := by
    have hQTv : HasFDerivAt Q (fderiv ℝ Q w) (T v) := by
      rw [hTv]
      exact hQ.differentiableAt_one.hasFDerivAt
    exact (hQTv.comp v T.hasFDerivAt).fderiv
  have hparam : fderiv ℝ (fun p => Q (p, w.2)) w.1 = (fderiv ℝ Q w).comp
      ((ContinuousLinearMap.id ℝ (Fin (k * 3) → ℝ)).prod
        (0 : (Fin (k * 3) → ℝ) →L[ℝ] LoopAmbient)) := by
    simpa +instances only [Function.comp_def, Prod.eta, id_eq] using!
      (hQ.differentiableAt_one.hasFDerivAt.comp w.1
        ((hasFDerivAt_id (𝕜 := ℝ) w.1).prodMk (hasFDerivAt_const w.2 w.1))).fderiv
  have hcol (u : LoopAmbient) :
      fderiv ℝ (Q ∘ T) v ((u, 0), 0) =
        (fderiv ℝ (fun p => Q (p, w.2)) w.1) (controlBlock i u.ofLp) := by
    rw [hderiv, hparam]
    change fderiv ℝ Q w (e.symm (u, 0), 0) = _
    rw [controlCoordinates_symm_fst]
    rfl
  have hBt : Function.Bijective
      (fun u : LoopAmbient => fderiv ℝ (Q ∘ T) v ((u, 0), 0)) := by
    rw [funext hcol]
    exact hblock.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).bijective
  obtain ⟨U, W, phi, hU, hW, hvW, hphi, hforward, hback⟩ :=
    exists_zero_chart (Q ∘ T) v hQt (by simpa only [Function.comp_apply, hTv] using hw) hBt
  let coordinate (z : (Fin (k * 3) → ℝ) × LoopAmbient) := e.symm (z.2, (e z.1).2)
  have hc : Continuous coordinate := e.symm.continuous.comp
    (continuous_snd.prodMk ((e.continuous.comp continuous_fst).snd))
  refine ⟨e ⁻¹' U, T.symm ⁻¹' W, T ∘ phi ∘ e, coordinate,
    hU.preimage e.continuous, hW.preimage T.symm.continuous, ?_,
    T.contDiff.contDiffOn.comp (hphi.comp e.contDiff.contDiffOn (fun _ hz => hz))
      (fun _ _ => mem_univ _), hc, ?_, ?_⟩
  · change T.symm w ∈ W
    have heq : T.symm w = v := by simp [T, v]
    exact heq ▸ hvW
  · intro u hu
    obtain ⟨hzero, hinv⟩ := hforward (e u) hu
    refine ⟨hzero, ?_⟩
    change e.symm ((phi (e u)).2, (e (e.symm (phi (e u)).1)).2) = u
    rw [ContinuousLinearEquiv.apply_symm_apply, hinv, ContinuousLinearEquiv.symm_apply_apply]
  · intro z hz hzero
    have hzt : (Q ∘ T) (T.symm z) = 0 := by
      simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hzero
    obtain ⟨hmem, heq⟩ := hback (T.symm z) hz hzt
    have hcEq : e (coordinate z) = ((T.symm z).2, (T.symm z).1.2) := by
      simp [coordinate, T]
    refine ⟨?_, ?_⟩
    · change e (coordinate z) ∈ U
      exact hcEq ▸ hmem
    · change T (phi (e (coordinate z))) = z
      rw [hcEq, heq, ContinuousLinearEquiv.apply_symm_apply]

end PoincareConjecture.M65Perturbation
