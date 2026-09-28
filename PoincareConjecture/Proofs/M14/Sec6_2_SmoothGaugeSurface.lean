import PoincareConjecture.Proofs.M14.Sec6_1_SupportedGaugeFamily










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))



theorem backwardGaugeFamily_joint_contMDiffAt
    (hp : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ p.curve (Ioo τ₁ τ₂))
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η) {z : ℝ × ℝ} (ht : z.1 ∈ Ioo τ₁ τ₂)
    (hsrc : p.curve z.1 ∈ U)
    (hshift : (lift (p.curve z.1)).2.val + z.2 • η z.1 ∈ G.gaugeCover.spatial b) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun w : ℝ × ℝ => backwardGaugeFamily p b lift η w.2 w.1) z := by
  have hbase : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun w : ℝ × ℝ => p.curve w.1) z :=
    ((hp _ ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)).comp z contMDiffAt_fst
  have hL := ((hlift _ hsrc).contMDiffAt (hU.mem_nhds hsrc)).comp z hbase
  have hv : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun w : ℝ × ℝ => w.2 • η w.1) z :=
    contMDiffAt_snd.smul (hη.contMDiff.contMDiffAt.comp z contMDiffAt_fst)
  have hS := (((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hshift).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hshift)).comp z
      (hL.snd.prodMk hv)
  exact (G.gaugeCover.cylinder b).smooth.contMDiffAt.comp z (hL.fst.prodMk hS)




theorem supportedBackwardGaugeFamily_joint_contMDiffOn
    (hp : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ p.curve (Ioo τ₁ τ₂))
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η) (hsrc : ∀ t ∈ tsupport η, p.curve t ∈ U) {P : Set ℝ}
    (hshift : ∀ t ∈ tsupport η, ∀ v ∈ P,
      (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => supportedBackwardGaugeFamily p b lift η z.2 z.1) (Ioo τ₁ τ₂ ×ˢ P) := by
  have hbase : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => p.curve z.1) (Ioo τ₁ τ₂ ×ˢ P) :=
    hp.comp contMDiffOn_fst (fun _ hz => hz.1)
  intro z hz
  by_cases hs : z.1 ∈ tsupport η
  · have hpathSmooth : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
        (fun w : ℝ × ℝ => p.curve w.1) z :=
      ((hp _ hz.1).contMDiffAt (isOpen_Ioo.mem_nhds hz.1)).comp z contMDiffAt_fst
    have hpath := hpathSmooth.continuousAt
    have heq : (fun w : ℝ × ℝ => supportedBackwardGaugeFamily p b lift η w.2 w.1) =ᶠ[𝓝 z]
        (fun w : ℝ × ℝ => backwardGaugeFamily p b lift η w.2 w.1) := by
      filter_upwards [hpath.preimage_mem_nhds (hU.mem_nhds (hsrc _ hs))] with w hw
      exact supportedBackwardGaugeFamily_eq_gauge p b lift η (hright _ hw) w.2
    exact ((backwardGaugeFamily_joint_contMDiffAt p b lift η hp hU hlift hη hz.1
      (hsrc _ hs) (hshift _ hs _ hz.2)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · have heq : (fun w : ℝ × ℝ => supportedBackwardGaugeFamily p b lift η w.2 w.1) =ᶠ[𝓝 z]
        (fun w => p.curve w.1) := by
      filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage continuous_fst).mem_nhds hs]
        with w hw
      exact supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η hw w.2
    exact (hbase z hz).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds




theorem backwardGaugeFamily_parameter_mfderiv (s : ℝ) :
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun v => backwardGaugeFamily p b lift η v s) 0 1 =
      ((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (p.curve s)).1 (lift (p.curve s)).2 (η s)).val := by
  let c := (lift (p.curve s)).2
  let t := (lift (p.curve s)).1
  let f := fun q : G.gaugeCover.spatial b => (G.gaugeCover.cylinder b).toSpacetime (t, q)
  have hf : ContMDiff (𝓡 n) (spacetimeModel n) ∞ f :=
    (G.gaugeCover.cylinder b).smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hshift := (G.gaugeCover.spatial b).affineShift_parameter_contMDiffAt c (η s)
  have hd := mfderiv_comp_apply_of_eq (x := (0 : ℝ))
    (hf.mdifferentiable (by simp) c) (hshift.mdifferentiableAt (by simp))
    (show (G.gaugeCover.spatial b).affineShift c ((0 : ℝ) • η s) = c by
      rw [zero_smul, TopologicalSpace.Opens.affineShift_zero]) (1 : ℝ)
  rw [TopologicalSpace.Opens.affineShift_parameter_mfderiv] at hd
  simpa only [f, c, t, Function.comp_def, backwardGaugeFamily, zero_smul,
    TopologicalSpace.Opens.affineShift_zero, (G.gaugeCover.metric b).spatialTangentEquiv_eq]
    using hd



theorem supportedBackwardGaugeFamily_parameter_mfderiv
    (hright : ∀ s ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (p.curve s)) = p.curve s) (s : ℝ) :
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun v => supportedBackwardGaugeFamily p b lift η v s) 0 1 =
      ((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (p.curve s)).1 (lift (p.curve s)).2 (η s)).val := by
  by_cases hs : s ∈ tsupport η
  · have heq : (fun v => supportedBackwardGaugeFamily p b lift η v s) =
        (fun v => backwardGaugeFamily p b lift η v s) :=
      funext (fun v => supportedBackwardGaugeFamily_eq_gauge p b lift η (hright s hs) v)
    rw [heq]
    exact backwardGaugeFamily_parameter_mfderiv p b lift η s
  · have heq : (fun v => supportedBackwardGaugeFamily p b lift η v s) =
        (fun _ : ℝ => p.curve s) :=
      funext (fun v => supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η hs v)
    rw [heq, image_eq_zero_of_notMem_tsupport hs, map_zero]
    simp only [mfderiv_const, zero_apply, Submodule.coe_zero]

end PoincareConjecture.M14
