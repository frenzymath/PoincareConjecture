import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Jets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SpacetimeBounds.Bootstrap

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def baseProjection (n : ℕ) : (j : ℕ) → Jet E V (n + j) →L[ℝ] Jet E V n
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => (baseProjection n j).comp (truncate (n + j))

@[simp] theorem baseProjection_spatialJet (n j : ℕ) (f : ℝ × E → V) (z : ℝ × E) :
    baseProjection n j (spatialJet (n + j) f z) = spatialJet n f z := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change baseProjection n j (truncate (n + j)
        (spatialJet ((n + j) + 1) f z)) = _
      rw [truncate_spatialJet, ih]

noncomputable def prolong (n : ℕ) (Q : Jet E V n → W) :
    Jet E V (n + 1) → E →L[ℝ] W :=
  fun a => (fderiv ℝ Q (truncate n a)).comp (shift (E := E) (V := V) n a)

theorem contDiffOn_prolong {n : ℕ} {Q : Jet E V n → W} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω) :
    ContDiffOn ℝ ∞ (prolong n Q) ((truncate n) ⁻¹' Ω) := by
  exact ((hQ.fderiv_of_isOpen hΩ (m := ∞) (by simp)).comp
    (truncate n).contDiff.contDiffOn (fun _ h => h)).clm_comp
      (shift (E := E) (V := V) n).contDiff.contDiffOn

noncomputable def operator (n : ℕ) (Q : Jet E V n → W) :
    (j : ℕ) → Jet E V (n + j) → E [×j]→L[ℝ] W
  | 0 => fun a => (continuousMultilinearCurryFin0 ℝ E W).symm (Q a)
  | j + 1 => fun a => (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) => E) W).symm (prolong (n + j) (operator n Q j) a)

theorem contDiffOn_operator {n : ℕ} {Q : Jet E V n → W} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω) (j : ℕ) :
    ContDiffOn ℝ ∞ (operator n Q j) ((baseProjection n j) ⁻¹' Ω) := by
  induction j with
  | zero =>
      exact (continuousMultilinearCurryFin0 ℝ E W).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hQ
  | succ j ih =>
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j + 1) => E) W).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
          (contDiffOn_prolong (hΩ.preimage (baseProjection n j).continuous) ih)

theorem operator_spatialJet {n : ℕ} {Q : Jet E V n → W} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {f : ℝ × E → V} {J : Set ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : IsOpen J) (hU : IsOpen U)
    (hrange : ∀ z ∈ J ×ˢ U, spatialJet n f z ∈ Ω)
    {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ U) (j : ℕ) :
    operator n Q j (spatialJet (n + j) f (t, x)) =
      iteratedFDeriv ℝ j (fun y => Q (spatialJet n f (t, y))) x := by
  have hfSlice (y : E) (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun y => f (t, y)) y :=
    (hf.contDiffAt ((hJ.prod hU).mem_nhds ⟨ht, hy⟩)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      have heq : (fun y => operator n Q j (spatialJet (n + j) f (t, y))) =ᶠ[𝓝 x]
          iteratedFDeriv ℝ j (fun y => Q (spatialJet n f (t, y))) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih hy
      have hOp : ContDiffAt ℝ ∞ (operator n Q j) (spatialJet (n + j) f (t, x)) :=
        (contDiffOn_operator hΩ hQ j).contDiffAt
          ((hΩ.preimage (baseProjection n j).continuous).mem_nhds (by
            simpa using hrange (t, x) ⟨ht, hx⟩))
      have hd := hOp.differentiableAt (by simp) |>.hasFDerivAt.comp x
        (hasFDerivAt_spatialJet (n + j) f t x (hfSlice x hx))
      change (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j + 1) => E) W).symm _ = _
      rw [iteratedFDeriv_succ_eq_comp_left]
      congr 1
      exact hd.fderiv.symm.trans heq.fderiv_eq

end PoincareConjecture.SpacetimeBounds.Bootstrap
