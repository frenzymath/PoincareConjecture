import PoincareConjecture.Proofs.M35.RadialGauge.JointC1










set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem joint_contDiffOn_succ_of_partials
    {J : Set ℝ} (hJ : IsOpen J) {u H : ℝ → E → F} (k : ℕ)
    (hspace : ∀ t ∈ J, Differentiable ℝ (u t))
    (htime : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => u s x) (H t x) t)
    (hH : ContDiffOn ℝ k (Function.uncurry H) (J ×ˢ univ))
    (hdu : ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (u p.1) p.2) (J ×ˢ univ)) :
    ContDiffOn ℝ (k + 1 : ℕ) (Function.uncurry u) (J ×ˢ univ) := by
  let timeMap : F →L[ℝ] (ℝ →L[ℝ] F) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toContinuousLinearEquiv.toContinuousLinearMap
  let D (p : ℝ × E) := (timeMap (H p.1 p.2)).coprod (fderiv ℝ (u p.1) p.2)
  have hW : IsOpen (J ×ˢ (univ : Set E)) := hJ.prod isOpen_univ
  have htc := timeMap.contDiff.comp_contDiffOn hH
  have hDc : ContDiffOn ℝ k D (J ×ˢ univ) := by
    have h := (htc.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ ℝ E))).add
      (hdu.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ ℝ E)))
    exact h.congr (fun _ _ => (ContinuousLinearMap.comp_fst_add_comp_snd _ _).symm)
  have hd {p : ℝ × E} (hp : p ∈ J ×ˢ (univ : Set E)) :
      HasFDerivAt (Function.uncurry u) (D p) p := by
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := u) (f₁ := fun t x => timeMap (H t x))
      (f₂ := fun t x => fderiv ℝ (u t) x)
      (by
        filter_upwards [hW.mem_nhds hp] with q hq
        exact (htime q.1 hq.1 q.2).hasFDerivAt)
      (by
        filter_upwards [hW.mem_nhds hp] with q hq
        exact (hspace q.1 hq.1 q.2).hasFDerivAt)
      (htc.continuousOn.continuousAt (hW.mem_nhds hp))
      (hdu.continuousOn.continuousAt (hW.mem_nhds hp))).hasFDerivAt
  rw [Nat.cast_add, Nat.cast_one]
  apply (contDiffOn_succ_iff_fderiv_of_isOpen hW).mpr
  refine ⟨fun p hp => (hd hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  exact hDc.congr (fun p hp => (hd hp).fderiv)

end PoincareConjecture.M35.RadialGauge
