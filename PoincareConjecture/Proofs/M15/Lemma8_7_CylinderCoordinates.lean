import PoincareConjecture.Definitions.M11CompatibleEmbedding
import PoincareConjecture.Proofs.M15.Lemma8_7_IntervalCalculus

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K0 K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {D0 : SmoothSpacetimeInterval K0} {D : SmoothSpacetimeInterval K}
  {V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}

theorem cylinder_localInverse_spatial_time_derivative
    (e0 : CompatibleSpacetimeCylinder F D0 V)
    (q0 : D0.Point × V)
    (hlocal : IsLocalDiffeomorphAt (spacetimeModel n) (spacetimeModel n) ∞
      e0.toSpacetime q0)
    (p : F.Point) (hp : p ∈ hlocal.localInverse.source) :
    mfderiv (spacetimeModel n) (𝓡 n)
      (fun z : F.Point => (hlocal.localInverse z).2.val) p
      (F.timeVector p) = 0 := by
  let q := hlocal.localInverse p
  let kappa := fun z : F.Point => (hlocal.localInverse z).2.val
  have hq : q ∈ hlocal.localInverse.target := hlocal.localInverse.map_source hp
  have hqp : e0.toSpacetime q = p := hlocal.localInverse_right_inv hp
  have hk : ContMDiffOn (spacetimeModel n) (𝓡 n) ∞ kappa
      hlocal.localInverse.source :=
    (contMDiff_subtype_val.comp contMDiff_snd).comp_contMDiffOn
      hlocal.localInverse_contMDiffOn
  have hevent : (fun s : D0.Point => kappa (e0.toSpacetime (s, q.2)))
      =ᶠ[𝓝 q.1] (fun _ => q.2.val) := by
    have hn : ∀ᶠ s : D0.Point in 𝓝 q.1, (s, q.2) ∈ hlocal.localInverse.target :=
      (continuous_id.prodMk continuous_const).continuousAt
        (hlocal.localInverse.open_target.mem_nhds hq)
    filter_upwards [hn] with s hs
    dsimp only [kappa]
    rw [hlocal.localInverse_left_inv hs]
  have hzero : mfderiv (𝓡∂ 1) (𝓡 n)
      (fun s : D0.Point => kappa (e0.toSpacetime (s, q.2))) q.1
      (D0.positiveTangent q.1) = 0 := by
    rw [hevent.mfderiv_eq, mfderiv_const]
    rfl
  have hkp : MDifferentiableAt (spacetimeModel n) (𝓡 n) kappa
      (e0.toSpacetime (q.1, q.2)) := by
    rw [Prod.mk.eta, hqp]
    exact ((hk p hp).contMDiffAt
      (hlocal.localInverse.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  change mfderiv (𝓡∂ 1) (𝓡 n)
    (kappa ∘ (fun s : D0.Point => e0.toSpacetime (s, q.2))) q.1
      (D0.positiveTangent q.1) = 0 at hzero
  rw [mfderiv_comp_apply q.1 hkp
    ((e0.worldline_smooth q.2 q.1).mdifferentiableAt (by simp)),
    e0.worldline_derivative] at hzero
  change mfderiv (spacetimeModel n) (𝓡 n) kappa (e0.toSpacetime q)
    (F.timeVector (e0.toSpacetime q)) = 0 at hzero
  rwa [hqp] at hzero

theorem cylinder_localInverse_spatial_constant
    (e0 : CompatibleSpacetimeCylinder F D0 V)
    (q0 : D0.Point × V)
    (hlocal : IsLocalDiffeomorphAt (spacetimeModel n) (spacetimeModel n) ∞
      e0.toSpacetime q0)
    {C : Type v} [TopologicalSpace C]
    (e : CompatibleSpacetimeEmbedding F D C) (c : C)
    (a b : D.Point) (hab : a.val ≤ b.val)
    (hseg : ∀ t : D.Point, a.val ≤ t.val → t.val ≤ b.val →
      e.toSpacetime (t, c) ∈ hlocal.localInverse.source) :
    (hlocal.localInverse (e.toSpacetime (a, c))).2 =
      (hlocal.localInverse (e.toSpacetime (b, c))).2 := by
  let kappa := fun z : F.Point => (hlocal.localInverse z).2.val
  let U := (fun t : D.Point => e.toSpacetime (t, c)) ⁻¹' hlocal.localInverse.source
  have hU : IsOpen U := hlocal.localInverse.open_source.preimage
    (e.worldline_smooth c).continuous
  have hk : ContMDiffOn (spacetimeModel n) (𝓡 n) ∞ kappa
      hlocal.localInverse.source :=
    (contMDiff_subtype_val.comp contMDiff_snd).comp_contMDiffOn
      hlocal.localInverse_contMDiffOn
  have hf : ContMDiffOn (𝓡∂ 1) (𝓡 n) ∞
      (fun t : D.Point => kappa (e.toSpacetime (t, c))) U :=
    hk.comp (e.worldline_smooth c).contMDiffOn (fun _ ht => ht)
  have hz (t : D.Point) (ht : t ∈ U) :
      mfderiv (𝓡∂ 1) (𝓡 n) (fun t : D.Point => kappa (e.toSpacetime (t, c))) t
        (D.positiveTangent t) = 0 := by
    change mfderiv (𝓡∂ 1) (𝓡 n)
      (kappa ∘ (fun s : D.Point => e.toSpacetime (s, c))) t
        (D.positiveTangent t) = 0
    rw [mfderiv_comp_apply t
      (((hk _ ht).contMDiffAt (hlocal.localInverse.open_source.mem_nhds ht)).mdifferentiableAt
        (by simp)) ((e.worldline_smooth c t).mdifferentiableAt (by simp)),
      e.worldline_derivative]
    exact cylinder_localInverse_spatial_time_derivative e0 q0 hlocal _ ht
  apply Subtype.ext
  exact eq_of_mfderiv_positiveTangent_eq_zero_on_Icc D hU hf hz a b hab hseg

end PoincareConjecture.Proofs.M15
