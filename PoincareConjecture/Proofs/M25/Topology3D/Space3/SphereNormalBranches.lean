import PoincareConjecture.Proofs.M25.Topology3D.Space3.FiniteSmoothBranches
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSard

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem sphere_ne_antipode (u : UnitTwoSphere) : u ≠ -u := by
  intro h
  have hi := congrArg (fun p : UnitTwoSphere => ⟪(u : E3), (p : E3)⟫_ℝ) h
  simp only [coe_neg_sphere, inner_neg_right, real_inner_self_eq_norm_sq,
    norm_eq_of_mem_sphere, one_pow] at hi
  norm_num at hi

theorem exists_opposite_normal_branches (N : UnitTwoSphere → UnitTwoSphere)
    (hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N) (u : UnitTwoSphere)
    (hregular : ∀ q, N q = u ∨ N q = -u →
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) N q)) :
    (N ⁻¹' {u}).Finite ∧ (N ⁻¹' {-u}).Finite ∧
      ∃ (W : Set UnitTwoSphere)
        (g : (N ⁻¹' {u}) ⊕ (N ⁻¹' {-u}) → UnitTwoSphere → UnitTwoSphere),
        IsOpen W ∧ u ∈ W ∧
        (∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (g i) W) ∧
        (∀ i v, v ∈ W → N (g i v) = v ∨ N (g i v) = -v) ∧
        (∀ v ∈ W, ∀ q, N q = v ∨ N q = -v → ∃ i, g i v = q) ∧
        (∀ v ∈ W, Function.Injective (fun i => g i v)) ∧
        ∀ i v, v ∈ W → Function.Injective (mfderiv (𝓡 2) (𝓡 2) N (g i v)) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  obtain ⟨hfp, Wp, gp, hWp, huWp, hgp, hpval, hpall, hpinj, _⟩ :=
    exists_finite_smooth_inverse_branches N hN u (fun q hq => hregular q (Or.inl hq))
  obtain ⟨hfm, Wm, gm, hWm, huWm, hgm, hmval, hmall, hminj, _⟩ :=
    exists_finite_smooth_inverse_branches N hN (-u) (fun q hq => hregular q (Or.inr hq))
  have hneg : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun v : UnitTwoSphere => -v) :=
    contMDiff_neg_sphere
  let W := Wp ∩ (fun v : UnitTwoSphere => -v) ⁻¹' Wm
  let g : (N ⁻¹' {u}) ⊕ (N ⁻¹' {-u}) → UnitTwoSphere → UnitTwoSphere :=
    Sum.elim gp (fun j v => gm j (-v))
  refine ⟨hfp, hfm, W, g, hWp.inter (hWm.preimage hneg.continuous),
    ⟨huWp, huWm⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact (hgp i).mono inter_subset_left
    | inr j => exact (hgm j).comp hneg.contMDiffOn (fun _ hv => hv.2)
  · intro i v hv
    cases i with
    | inl i => exact Or.inl (hpval i v hv.1)
    | inr j => exact Or.inr (hmval j (-v) hv.2)
  · intro v hv q hq
    rcases hq with hq | hq
    · obtain ⟨i, hi⟩ := hpall q (hq.symm ▸ hv.1)
      exact ⟨Sum.inl i, (congrArg (gp i) hq.symm).trans hi⟩
    · obtain ⟨j, hj⟩ := hmall q (hq.symm ▸ hv.2)
      exact ⟨Sum.inr j, (congrArg (gm j) hq.symm).trans hj⟩
  · intro v hv i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hpinj v hv.1 hij)
      | inr j =>
        have h : v = -v := (hpval i v hv.1).symm.trans
          ((congrArg N hij).trans (hmval j (-v) hv.2))
        exact (sphere_ne_antipode v h).elim
    | inr i =>
      cases j with
      | inl j =>
        have h : v = -v := (hpval j v hv.1).symm.trans
          ((congrArg N hij.symm).trans (hmval i (-v) hv.2))
        exact (sphere_ne_antipode v h).elim
      | inr j => exact congrArg Sum.inr (hminj (-v) hv.2 hij)
  · intro i v hv
    cases i with
    | inl i =>
      apply mfderiv_injective_of_local_right_inverse N hN (gp i) v
        (((hgp i).contMDiffAt (hWp.mem_nhds hv.1)).mdifferentiableAt (by simp))
      filter_upwards [hWp.mem_nhds hv.1] with z hz
      exact hpval i z hz
    | inr j =>
      apply mfderiv_injective_of_local_right_inverse N hN (gm j) (-v)
        (((hgm j).contMDiffAt (hWm.mem_nhds hv.2)).mdifferentiableAt (by simp))
      filter_upwards [hWm.mem_nhds hv.2] with z hz
      exact hmval j z hz

end PoincareConjecture.M25.Topology3D
