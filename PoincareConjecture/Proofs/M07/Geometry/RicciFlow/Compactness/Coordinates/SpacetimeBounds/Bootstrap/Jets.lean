import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.MixedDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SpacetimeBounds.Bootstrap

variable (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev Jet (n : ℕ) := (j : Fin (n + 1)) → E [×(j : ℕ)]→L[ℝ] V

variable {E V}

noncomputable def spatialJet (n : ℕ) (f : ℝ × E → V) (z : ℝ × E) : Jet E V n :=
  fun j => iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2

noncomputable def truncate (n : ℕ) : Jet E V (n + 1) →L[ℝ] Jet E V n :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.castSucc

noncomputable def shift (n : ℕ) : Jet E V (n + 1) →L[ℝ] (E →L[ℝ] Jet E V n) :=
  (ContinuousLinearMap.piEquivL ℝ E (fun j : Fin (n + 1) => E [×(j : ℕ)]→L[ℝ] V)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin ((j : ℕ) + 1) => E) V).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.proj j.succ))

@[simp] theorem truncate_spatialJet (n : ℕ) (f : ℝ × E → V) (z : ℝ × E) :
    truncate n (spatialJet n.succ f z) = spatialJet n f z := rfl

@[simp] theorem shift_apply (n : ℕ) (a : Jet E V (n + 1)) (v : E)
    (j : Fin (n + 1)) :
    shift (E := E) (V := V) n a v j =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin ((j : ℕ) + 1) => E) V)
        (a j.succ) v := rfl

theorem contDiffOn_spatialJet {f : ℝ × E → V} {J : Set ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : IsOpen J) (hU : IsOpen U) (n : ℕ) :
    ContDiffOn ℝ ∞ (spatialJet n f) (J ×ˢ U) := by
  apply contDiffOn_pi.mpr
  intro j
  exact SpacetimeBounds.contDiffOn_spatialJet hf hJ hU j

theorem fderiv_spatialJet (n : ℕ) (f : ℝ × E → V) (t : ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ (fun y => f (t, y)) x) :
    fderiv ℝ (fun y => spatialJet n f (t, y)) x =
      shift (E := E) (V := V) n (spatialJet (n + 1) f (t, x)) := by
  have hd (j : Fin (n + 1)) :
      DifferentiableAt ℝ (iteratedFDeriv ℝ (j : ℕ) (fun y => f (t, y))) x :=
    (hf.iteratedFDeriv_right (m := 1) (by exact_mod_cast le_top)).differentiableAt (by simp)
  change fderiv ℝ (fun y (j : Fin (n + 1)) =>
    iteratedFDeriv ℝ (j : ℕ) (fun y => f (t, y)) y) x = _
  rw [fderiv_pi hd]
  apply ContinuousLinearMap.ext
  intro v
  funext j
  change fderiv ℝ (iteratedFDeriv ℝ (j : ℕ) (fun y => f (t, y))) x v = _
  rw [shift_apply]
  change _ = (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin ((j : ℕ) + 1) => E) V)
      (iteratedFDeriv ℝ ((j : ℕ) + 1) (fun y => f (t, y)) x) v
  rw [iteratedFDeriv_succ_eq_comp_left]
  simp

theorem hasFDerivAt_spatialJet (n : ℕ) (f : ℝ × E → V) (t : ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ (fun y => f (t, y)) x) :
    HasFDerivAt (fun y => spatialJet n f (t, y))
      (shift (E := E) (V := V) n (spatialJet (n + 1) f (t, x))) x := by
  rw [← fderiv_spatialJet n f t x hf]
  have hd (j : Fin (n + 1)) :
      DifferentiableAt ℝ (iteratedFDeriv ℝ (j : ℕ) (fun y => f (t, y))) x :=
    (hf.iteratedFDeriv_right (m := 1) (by exact_mod_cast le_top)).differentiableAt (by simp)
  exact (differentiableAt_pi.mpr hd).hasFDerivAt

end PoincareConjecture.SpacetimeBounds.Bootstrap
