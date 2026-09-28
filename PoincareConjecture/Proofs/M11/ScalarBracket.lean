import PoincareConjecture.Proofs.M11.ChartScalarAction





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem scalar_mlieBracket_eq_zero {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (V W : ∀ p : M, TangentSpace I p) (O : Set M) (hO : IsOpen O) (x : M) (hx : x ∈ O)
    (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (fun p ↦ (V p : TangentBundle I M)) x)
    (hW : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (fun p ↦ (W p : TangentBundle I M)) x)
    (a b : ℝ) (ha : ∀ p ∈ O, mfderiv I 𝓘(ℝ) f p (V p) = a)
    (hb : ∀ p ∈ O, mfderiv I 𝓘(ℝ) f p (W p) = b) :
    mfderiv I 𝓘(ℝ) f x (VectorField.mlieBracket I V W x) = 0 := by
  let c := extChartAt I x
  let V' := VectorField.mpullbackWithin 𝓘(ℝ, E) I c.symm V (range I)
  let W' := VectorField.mpullbackWithin 𝓘(ℝ, E) I c.symm W (range I)
  have hV' : DifferentiableWithinAt ℝ V' (range I) (c x) := by
    have hd : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
        (fun p ↦ (V p : TangentBundle I M)) univ x :=
      (hV.mdifferentiableAt (by simp)).mdifferentiableWithinAt
    simpa only [preimage_univ, univ_inter] using
      hd.differentiableWithinAt_mpullbackWithin_vectorField
  have hW' : DifferentiableWithinAt ℝ W' (range I) (c x) := by
    have hd : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
        (fun p ↦ (W p : TangentBundle I M)) univ x :=
      (hW.mdifferentiableAt (by simp)).mdifferentiableWithinAt
    simpa only [preimage_univ, univ_inter] using
      hd.differentiableWithinAt_mpullbackWithin_vectorField
  have hcs : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ c.symm (range I) (c x) :=
    contMDiffWithinAt_extChartAt_symm_range_self x
  have hfs : ContDiffWithinAt ℝ ∞ (f ∘ c.symm) (range I) (c x) :=
    ((hf _).comp_contMDiffWithinAt (c x) hcs).contDiffWithinAt
  have haction (Z : ∀ p : M, TangentSpace I p) (d : ℝ)
      (hd : ∀ p ∈ O, mfderiv I 𝓘(ℝ) f p (Z p) = d) :
      (fun y ↦ fderivWithin ℝ (f ∘ c.symm) (range I) y
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I c.symm Z (range I) y)) =ᶠ[𝓝[range I] (c x)]
          (fun _ ↦ d) := by
    have hm : O ∈ 𝓝 (c.symm (c x)) := by
      rw [extChartAt_to_inv]
      exact hO.mem_nhds hx
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x,
      hcs.continuousWithinAt.eventually hm] with y hy hyO
    exact (extChart_scalar_action x hy ((hf _).mdifferentiableAt (by simp)) Z).trans
      (hd _ hyO)
  have hVa : fderivWithin ℝ (fun y ↦ fderivWithin ℝ (f ∘ c.symm) (range I) y (V' y))
      (range I) (c x) = 0 := by
    rw [(haction V a ha).fderivWithin_eq_of_mem (mem_range_self _),
      fderivWithin_const_apply]
  have hWb : fderivWithin ℝ (fun y ↦ fderivWithin ℝ (f ∘ c.symm) (range I) y (W' y))
      (range I) (c x) = 0 := by
    rw [(haction W b hb).fderivWithin_eq_of_mem (mem_range_self _),
      fderivWithin_const_apply]
  have hn : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have hbracket := VectorField.fderivWithin_apply_lieBracket hfs hn
    I.uniqueDiffOn (I.range_subset_closure_interior (mem_range_self _)) (mem_range_self _) hW' hV'
  rw [hWb, hVa] at hbracket
  simp only [zero_apply, sub_self] at hbracket
  rw [extChart_scalar_derivative x ((hf x).mdifferentiableAt (by simp))]
  simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
    preimage_univ, univ_inter, mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id]
  change fderivWithin ℝ (f ∘ c.symm) (range I) (c x)
    (VectorField.lieBracketWithin ℝ V' W' (range I) (c x)) = (0 : ℝ)
  exact hbracket

end PoincareConjecture.Proofs.M11
