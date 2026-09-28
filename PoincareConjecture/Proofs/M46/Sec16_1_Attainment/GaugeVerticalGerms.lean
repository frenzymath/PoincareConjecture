import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeVertical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem gauge_vertical_germs (e f : AttainmentGauge G)
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma) {a b T c : ℝ}
    (hclock : ∀ s ∈ Icc a b, G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (hc : c ∈ Ioo a b) (he : gamma c ∈ e.source) (hf : gamma c ∈ f.source) :
    (fun s => (G.gaugeCover.cylinder e.index).toSpacetime
      ((e.lift (gamma s)).1, (e.lift (gamma c)).2)) =ᶠ[𝓝 c]
    (fun s => (G.gaugeCover.cylinder f.index).toSpacetime
      ((f.lift (gamma s)).1, (f.lift (gamma c)).2)) := by
  have hnear : ∀ᶠ s in 𝓝 c,
      s ∈ Ioo a b ∧ gamma s ∈ e.source ∧ gamma s ∈ f.source := by
    filter_upwards [isOpen_Ioo.mem_nhds hc,
      hgamma.continuousAt.preimage_mem_nhds (e.source_open.mem_nhds he),
      hgamma.continuousAt.preimage_mem_nhds (f.source_open.mem_nhds hf)] with s hs hse hsf
    exact ⟨hs, hse, hsf⟩
  obtain ⟨l, r, hclr, hlr⟩ := hnear.exists_Ioo_subset
  have htheta := gauge_square_clock_smooth f gamma T
    (fun s hs => (hlr hs).2.2) (fun s hs => hclock s (Ioo_subset_Icc_self (hlr hs).1))
  let beta := fun s => (G.gaugeCover.cylinder f.index).toSpacetime
    ((f.lift (gamma s)).1, (f.lift (gamma c)).2)
  have hbeta : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ beta (Ioo l r) :=
    (G.gaugeCover.cylinder f.index).smooth.comp_contMDiffOn
      (htheta.prodMk contMDiffOn_const)
  have hbetac : beta c = gamma c := f.right_inv (gamma c) hf
  have hcapture : ∀ᶠ s in 𝓝 c, s ∈ Ioo l r ∧ beta s ∈ e.source := by
    have hcont := (hbeta.continuousOn c hclr).continuousAt (isOpen_Ioo.mem_nhds hclr)
    filter_upwards [isOpen_Ioo.mem_nhds hclr,
      hcont.preimage_mem_nhds (e.source_open.mem_nhds (hbetac.symm ▸ he))] with s hs hse
    exact ⟨hs, hse⟩
  obtain ⟨l', r', hclr', hlr'⟩ := hcapture.exists_Ioo_subset
  have hsub : Ioo l' r' ⊆ Ioo l r := fun s hs => (hlr' hs).1
  have hsrc : MapsTo beta (Ioo l' r') e.source := fun s hs => (hlr' hs).2
  have hzero (s : ℝ) (hs : s ∈ Ioo l' r') :
      M14.projectedCurveVelocity G beta s = 0 :=
    gauge_vertical_velocity_zero f.index (fun s => (f.lift (gamma s)).1)
      (f.lift (gamma c)).2
      (((htheta s (hsub hs)).contMDiffAt
        (isOpen_Ioo.mem_nhds (hsub hs))).mdifferentiableAt (by simp))
  filter_upwards [isOpen_Ioo.mem_nhds hclr'] with s hs
  have hspace := gauge_lift_spatial_constant e isOpen_Ioo (convex_Ioo l' r').isPreconnected
    beta ((hbeta.mono hsub).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hsrc hzero hs hclr'
  rw [hbetac] at hspace
  have htime : (e.lift (beta s)).1 = (e.lift (gamma s)).1 := by
    apply Subtype.ext
    rw [e.clock (beta s) (hsrc hs), e.clock (gamma s) (hlr (hsub hs)).2.1]
    change G.spacetime.timeFunction
      ((G.gaugeCover.cylinder f.index).toSpacetime
        ((f.lift (gamma s)).1, (f.lift (gamma c)).2)) = _
    rw [(G.gaugeCover.cylinder f.index).time_eq]
    exact f.clock (gamma s) (hlr (hsub hs)).2.2
  have heq : e.lift (beta s) = ((e.lift (gamma s)).1, (e.lift (gamma c)).2) :=
    Prod.ext htime hspace
  exact (congrArg (G.gaugeCover.cylinder e.index).toSpacetime heq).symm.trans
    (e.right_inv (beta s) (hsrc hs))

end PoincareConjecture.Proofs.M46
