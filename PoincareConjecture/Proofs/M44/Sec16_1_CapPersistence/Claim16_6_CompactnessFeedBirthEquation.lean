import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds SpacetimeBounds.Bootstrap




theorem hasDerivWithinAt_birth_of_continuous_evolution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : ℝ → V} {T : ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Ico 0 T)) (hg : ContinuousOn g (Ico 0 T))
    (hevolution : ∀ t ∈ Ioo 0 T, HasDerivAt f (g t) t) :
    HasDerivWithinAt f (g 0) (Ico 0 T) 0 := by
  have hzero : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hderiv : ∀ᶠ t in 𝓝[>] (0 : ℝ), HasDerivAt f (g t) t := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    exact hevolution t ht
  have hglim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
    ((hg 0 hzero).mono_of_mem_nhdsWithin (Ico_mem_nhdsGE hT)).mono Ioi_subset_Ici_self
  have hright : HasDerivWithinAt f (g 0) (Ici 0) 0 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioo 0 T)
      (fun t ht => (hevolution t ht).differentiableAt.differentiableWithinAt)
      ((hf 0 hzero).mono Ioo_subset_Ico_self) (Ioo_mem_nhdsGT hT)
      (hglim.congr' (hderiv.mono fun _ ht => ht.deriv.symm))
  exact hright.mono (fun _ ht => ht.1)

set_option maxHeartbeats 800000 in




theorem hasDerivWithinAt_ricci_coefficients_birth
    {n : ℕ} {T : ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hT : 0 < T)
    {B : ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    (hB : ContinuousOn B (Ico 0 T ×ˢ U))
    (hjets : ∀ m : ℕ, ContinuousOn
      (fun p => iteratedFDeriv ℝ m (fun x => B (p.1, x)) p.2) (Ico 0 T ×ˢ U))
    (hinvertible : ∀ p ∈ Ico 0 T ×ˢ U, (B p).IsInvertible)
    (hevolution : ∀ t ∈ Ioo 0 T, ∀ x ∈ U,
      HasDerivAt (fun s => B (s, x))
        (ricciFlowOperator n (metricTwoJet (fun y => B (t, y)) x)) t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    HasDerivWithinAt (fun s => B (s, x))
      (ricciFlowOperator n (metricTwoJet (fun y => B (0, y)) x)) (Ico 0 T) 0 := by
  have hjet : ContinuousOn (spatialJet 2 B) (Ico 0 T ×ˢ U) :=
    continuousOn_pi.mpr fun m => hjets m.1
  have hrhs : ContinuousOn (fun p => jetRicciFlowOperator n (spatialJet 2 B p))
      (Ico 0 T ×ˢ U) := by
    apply (contDiffOn_jetRicciFlowOperator n).continuousOn.comp hjet
    intro p hp
    change (twoJetProjection n (spatialJet 2 B p)).1.IsInvertible
    rw [twoJetProjection_spatialJet]
    exact hinvertible p hp
  have htime := hrhs.comp (continuousOn_id.prodMk continuousOn_const)
    (fun _ ht => ⟨ht, hx⟩)
  simp only [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet] at htime
  exact hasDerivWithinAt_birth_of_continuous_evolution hT
    (hB.comp (continuousOn_id.prodMk continuousOn_const) (fun _ ht => ⟨ht, hx⟩))
    htime (fun t ht => hevolution t ht x hx)

end PoincareConjecture.M44
