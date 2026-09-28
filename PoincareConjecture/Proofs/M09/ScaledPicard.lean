import PoincareConjecture.Proofs.M09.PathSpaceCalculus
import PoincareConjecture.Proofs.M09.PathPrimitive
import Mathlib.Analysis.Calculus.ImplicitContDiff

set_option autoImplicit false

open scoped ContDiff Topology
open Set Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def scaledPicardResidual (f : C(E, E))
    (z : (E × ℝ) × C(Set.Icc (-1 : ℝ) 1, E)) : C(Set.Icc (-1 : ℝ) 1, E) :=
  z.2 - ContinuousMap.const _ z.1.1 - z.1.2 • pathPrimitive (f.comp z.2)

theorem scaledPicardResidual_smooth (f : C(E, E)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scaledPicardResidual f) := by
  have hc : ContDiff ℝ ∞ (fun z : (E × ℝ) × C(Set.Icc (-1 : ℝ) 1, E) ↦
      ContinuousMap.const (Set.Icc (-1 : ℝ) 1) z.1.1) :=
    (ContinuousLinearMap.const (R := ℝ) (M := E) (Set.Icc (-1 : ℝ) 1)).contDiff.comp
      (contDiff_fst.comp contDiff_fst)
  have hp : ContDiff ℝ ∞ (fun z : (E × ℝ) × C(Set.Icc (-1 : ℝ) 1, E) ↦
      pathPrimitive (f.comp z.2)) :=
    (pathPrimitive (E := E)).contDiff.comp
      ((contDiff_postcomp_smooth (K := Set.Icc (-1 : ℝ) 1) f hf).comp contDiff_snd)
  exact (contDiff_snd.sub hc).sub ((contDiff_snd.comp contDiff_fst).smul hp)

@[simp] theorem scaledPicardResidual_at_zero (f : C(E, E)) (x : E) :
    scaledPicardResidual f ((x, 0), ContinuousMap.const _ x) = 0 := by
  simp only [scaledPicardResidual, zero_smul, sub_self]

theorem scaledPicardResidual_partial (f : C(E, E)) (hf : ContDiff ℝ ∞ f) (x : E) :
    (fderiv ℝ (scaledPicardResidual f) ((x, 0), ContinuousMap.const _ x)).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(Set.Icc (-1 : ℝ) 1, E)) =
        ContinuousLinearMap.id ℝ C(Set.Icc (-1 : ℝ) 1, E) := by
  have hfull := ((scaledPicardResidual_smooth f hf).differentiable (by simp)
    ((x, 0), ContinuousMap.const _ x)).hasFDerivAt
  have hcomp := hfull.comp (ContinuousMap.const (Set.Icc (-1 : ℝ) 1) x)
    (hasFDerivAt_prodMk_right (x, (0 : ℝ)) (ContinuousMap.const _ x))
  have hrestriction : HasFDerivAt
      (fun v : C(Set.Icc (-1 : ℝ) 1, E) ↦ scaledPicardResidual f ((x, 0), v))
      (ContinuousLinearMap.id ℝ C(Set.Icc (-1 : ℝ) 1, E)) (ContinuousMap.const _ x) := by
    convert! (hasFDerivAt_id (𝕜 := ℝ) (ContinuousMap.const (Set.Icc (-1 : ℝ) 1) x)).sub_const
      (ContinuousMap.const _ x) using 1
    simp only [scaledPicardResidual, zero_smul, sub_zero, id_eq]
  exact hcomp.unique hrestriction

theorem exists_scaledPicard (f : C(E, E)) (hf : ContDiff ℝ ∞ f) (x0 : E) :
    ∃ sigma : E × ℝ → C(Set.Icc (-1 : ℝ) 1, E),
      sigma (x0, 0) = ContinuousMap.const _ x0 ∧
      ContDiffAt ℝ ∞ sigma (x0, 0) ∧
      ∀ᶠ p in 𝓝 (x0, (0 : ℝ)),
        sigma p = ContinuousMap.const _ p.1 + p.2 • pathPrimitive (f.comp (sigma p)) := by
  let z0 : (E × ℝ) × C(Set.Icc (-1 : ℝ) 1, E) :=
    ((x0, 0), ContinuousMap.const _ x0)
  have hc : ContDiffAt ℝ ∞ (scaledPicardResidual f) z0 :=
    (scaledPicardResidual_smooth f hf).contDiffAt
  have hi : ((fderiv ℝ (scaledPicardResidual f) z0).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(Set.Icc (-1 : ℝ) 1, E))).IsInvertible := by
    rw [scaledPicardResidual_partial f hf x0]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  refine ⟨hc.implicitFunction hn hi, hc.implicitFunction_apply_self hn hi,
    hc.contDiffAt_implicitFunction hn hi, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction hn hi] with p hp
  rw [scaledPicardResidual_at_zero] at hp
  exact sub_eq_zero.mp (by simpa only [scaledPicardResidual, sub_sub] using hp)

end PoincareConjecture.Proofs.M09
