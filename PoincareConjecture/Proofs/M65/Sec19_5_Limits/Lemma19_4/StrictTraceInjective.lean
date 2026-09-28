import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceCircleArc
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceDifferential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65StrictTrace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem parameter_injective_of_finite_branches
    {f : LoopPlane → M}
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    {gamma : LoopCircle → M} (beta : C(LoopCircle, LoopCircle))
    (hbeta : M65WeakCircleParameter beta)
    (htrace : ∀ z : LoopCircle, f z = gamma (beta z))
    (hfinite : {z : LoopPlane | z ∈ loopDiskSet ∧
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0}.Finite) :
    Function.Injective beta := by
  classical
  by_contra hnot
  obtain ⟨p, a, b, hab, _hI, hsi, hconst⟩ := exists_collapsed_arc beta hbeta hnot
  let c := fun t : ℝ => (puncturedArc p t : LoopPlane)
  have hcK (t : ℝ) : c t ∈ loopDiskSet := by
    exact mem_closedBall_zero_iff.mpr (le_of_eq (puncturedArc p t).property)
  have hbranches (t : ℝ) (ht : t ∈ Ioo a b) :
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (c t) = 0 := by
    obtain ⟨v, hv, hd⟩ := puncturedArc_hasDerivAt p t
    have heq : f ∘ c =ᶠ[𝓝 t] fun _ => gamma (beta (puncturedArc p a)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (htrace (puncturedArc p s)).trans (congrArg gamma (hconst s ⟨hs.1.le, hs.2.le⟩))
    have hzero : mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) (f ∘ c) t = 0 := by
      rw [heq.mfderiv_eq, mfderiv_const]
    have hdc : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 2) c t :=
      hd.differentiableAt.mdifferentiableAt
    have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (I'' := 𝓡 3) t
      ((hb _ (hcK t)).mdifferentiableWithinAt (by decide))
      hdc.mdifferentiableWithinAt (show univ ⊆ c ⁻¹' loopDiskSet from fun s _ => hcK s)
      (uniqueMDiffWithinAt_univ (𝓘(ℝ, ℝ)))
    simp only [mfderivWithin_univ] at hchain
    have hvelocity : mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) c t 1 = v := by
      simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hd.deriv
    have hap := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 3) (f (c t)) => L 1) hchain
    rw [hzero] at hap
    change 0 = mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (c t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) c t 1) at hap
    rw [hvelocity] at hap
    exact diskDifferential_eq_zero_of_direction g f hb hconf (hcK t) hv hap.symm
  have hsub : c '' Ioo a b ⊆ {z : LoopPlane | z ∈ loopDiskSet ∧
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0} := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨hcK t, hbranches t ht⟩
  have hi : InjOn c (Ioo a b) := by
    intro s hs t ht he
    exact hsi ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ (Subtype.ext he)
  exact (Set.Ioo_infinite hab) ((hfinite.subset hsub).of_finite_image hi)

end PoincareConjecture.M65StrictTrace
