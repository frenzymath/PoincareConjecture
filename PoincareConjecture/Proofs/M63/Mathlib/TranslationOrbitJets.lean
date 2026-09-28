import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTranslation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic









set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M63




theorem iteratedDeriv_comp_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {u : ℝ → E} {x : ℝ} (k : ℕ)
    (hu : ContDiffAt ℝ k u x) :
    iteratedDeriv k (A ∘ u) x = A (iteratedDeriv k u x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    A.iteratedFDeriv_comp_left hu le_rfl, iteratedDeriv_eq_iteratedFDeriv]
  rfl






theorem spatial_jets_of_smooth_translation_orbit
    {L : ℝ} [Fact (0 < L)] {K E : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : C(K, C(AddCircle L, E))) (U : ℝ → C(K, C(AddCircle L, E)))
    (hU : ContDiffAt ℝ ∞ U 0)
    (horbit : ∀ (s : ℝ) (t : K) (x : AddCircle L), U s t x = f t (x - (s : AddCircle L))) :
    (∀ t : K, ContDiff ℝ ∞ (fun x : ℝ => f t (x : AddCircle L))) ∧
      ∀ k : ℕ, ∃ J : C(K, C(AddCircle L, E)), ∀ (t : K) (x : ℝ),
        iteratedDeriv k (fun y : ℝ => f t (y : AddCircle L)) x = J t (x : AddCircle L) := by
  constructor
  · intro t
    apply contDiff_iff_contDiffAt.mpr
    intro x
    let A : C(K, C(AddCircle L, E)) →L[ℝ] E :=
      (ContinuousMap.evalCLM ℝ (x : AddCircle L)).comp (ContinuousMap.evalCLM ℝ t)
    have hUat : ContDiffAt ℝ ∞ U (x - x) := by simpa only [sub_self] using hU
    have harg : ContDiffAt ℝ ∞ (fun y : ℝ => x - y) x :=
      contDiffAt_const.sub contDiffAt_id
    have hcomp := A.contDiff.contDiffAt.comp x (hUat.comp x harg)
    apply hcomp.congr_of_eventuallyEq
    apply Eventually.of_forall
    intro y
    change f t (y : AddCircle L) = U (x - y) t (x : AddCircle L)
    rw [horbit]
    simp only [AddCircle.coe_sub, sub_sub_cancel]
  · intro k
    refine ⟨(-1 : ℝ) ^ k • iteratedDeriv k U 0, ?_⟩
    intro t x
    let A : C(K, C(AddCircle L, E)) →L[ℝ] E :=
      (ContinuousMap.evalCLM ℝ (x : AddCircle L)).comp (ContinuousMap.evalCLM ℝ t)
    have hUk : ContDiffAt ℝ k U 0 :=
      hU.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
    have hlinear := iteratedDeriv_comp_clm A k hUk
    have heq : A ∘ U = fun s : ℝ => f t ((x - s : ℝ) : AddCircle L) := by
      funext s
      exact (horbit s t (x : AddCircle L)).trans (by rw [AddCircle.coe_sub])
    have hreflect : iteratedDeriv k (A ∘ U) 0 =
        (-1 : ℝ) ^ k • iteratedDeriv k (fun y : ℝ => f t (y : AddCircle L)) x := by
      rw [heq]
      simpa only [sub_zero] using congrFun
        (iteratedDeriv_comp_const_sub k (fun y : ℝ => f t (y : AddCircle L)) x) (0 : ℝ)
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    change iteratedDeriv k (fun y : ℝ => f t (y : AddCircle L)) x =
      (-1 : ℝ) ^ k • A (iteratedDeriv k U 0)
    simpa only [smul_smul, hsign, one_smul] using
      (congrArg (fun z : E => (-1 : ℝ) ^ k • z) (hlinear.symm.trans hreflect)).symm

end PoincareConjecture.M63
