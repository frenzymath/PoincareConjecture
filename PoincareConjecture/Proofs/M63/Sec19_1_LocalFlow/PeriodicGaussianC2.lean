import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianDeriv










set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]




theorem exists_periodicGaussian_c2_jets (f : C(AddCircle L, E))
    (hf : ContDiff ℝ 2 (fun x : ℝ => f (x : AddCircle L))) :
    ∃ f1 f2 : C(AddCircle L, E),
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => f1 (y : AddCircle L)) (f2 (x : AddCircle L)) x) ∧
      ∀ t : ℝ, ContDiff ℝ 2 (fun x : ℝ => periodicGaussianHeat t f (x : AddCircle L)) ∧
        (∀ x : ℝ, HasDerivAt (fun y : ℝ => periodicGaussianHeat t f (y : AddCircle L))
          (periodicGaussianHeat t f1 (x : AddCircle L)) x) ∧
        (∀ x : ℝ, HasDerivAt (fun y : ℝ => periodicGaussianHeat t f1 (y : AddCircle L))
          (periodicGaussianHeat t f2 (x : AddCircle L)) x) := by
  let u := fun x : ℝ => f (x : AddCircle L)
  have hu : Differentiable ℝ u := hf.differentiable (by norm_num)
  have hu1 : ContDiff ℝ 1 (deriv u) := hf.deriv' (n := 1)
  have hd1 : Differentiable ℝ (deriv u) := hu1.differentiable (by norm_num)
  have hp : Function.Periodic u L := by
    intro x
    simp only [u, AddCircle.coe_add_period]
  have hp1 : Function.Periodic (deriv u) L := by
    intro x
    have h : HasDerivAt (fun y => u (y + L)) (deriv u (x + L)) x := by
      simpa only [Function.comp_def, one_smul, id_eq] using
        (hu (x + L)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const L)
    rw [show (fun y => u (y + L)) = u from funext hp] at h
    exact h.unique (hu x).hasDerivAt
  have hp2 : Function.Periodic (deriv (deriv u)) L := by
    intro x
    have h : HasDerivAt (fun y => deriv u (y + L)) (deriv (deriv u) (x + L)) x := by
      simpa only [Function.comp_def, one_smul, id_eq] using
        (hd1 (x + L)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const L)
    rw [show (fun y => deriv u (y + L)) = deriv u from funext hp1] at h
    exact h.unique (hd1 x).hasDerivAt
  let f1 : C(AddCircle L, E) := ⟨hp1.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
      hu1.continuous⟩
  let f2 : C(AddCircle L, E) := ⟨hp2.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
      hu1.continuous_deriv_one⟩
  have h1 (x : ℝ) : HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x :=
    (hu x).hasDerivAt
  have h2 (x : ℝ) : HasDerivAt (fun y : ℝ => f1 (y : AddCircle L)) (f2 (x : AddCircle L)) x :=
    (hd1 x).hasDerivAt
  refine ⟨f1, f2, h1, h2, fun t => ?_⟩
  have hG1 := hasDerivAt_periodicGaussianHeat t f f1 h1
  have hG2 := hasDerivAt_periodicGaussianHeat t f1 f2 h2
  have heq1 : deriv (fun x : ℝ => periodicGaussianHeat t f (x : AddCircle L)) =
      fun x : ℝ => periodicGaussianHeat t f1 (x : AddCircle L) :=
    funext (fun x => (hG1 x).deriv)
  have heq2 : deriv (fun x : ℝ => periodicGaussianHeat t f1 (x : AddCircle L)) =
      fun x : ℝ => periodicGaussianHeat t f2 (x : AddCircle L) :=
    funext (fun x => (hG2 x).deriv)
  refine ⟨?_, hG1, hG2⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hG1 x).differentiableAt, by norm_num, ?_⟩
  rw [heq1, contDiff_one_iff_deriv]
  refine ⟨fun x => (hG2 x).differentiableAt, ?_⟩
  rw [heq2]
  exact (periodicGaussianHeat t f2).continuous.comp (AddCircle.continuous_mk' L)

end PoincareConjecture.M63
