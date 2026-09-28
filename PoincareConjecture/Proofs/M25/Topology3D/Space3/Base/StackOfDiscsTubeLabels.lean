import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsEndLabels

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)
local notation "CircleDiff" => Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞

theorem exists_stackTubeEndLabels
    (T : OpenPartialHomeomorph P P)
    (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p ∈ T.source, (T p).1 = p.1)
    (c : ℝ → UnitCircle → E2) (c0 c1 jL jR : ℝ)
    (D0 : PlanarSchoenfliesFamilyData c c0 c1) (G0 : PlanarFamilyGraphChart D0)
    (hJ : jL < jR) (hJband : Ioo jL jR ⊆ Icc c0 c1)
    (hsource : Ioo jL jR ×ˢ closedBall (0 : E2) 1 ⊆ T.source)
    (hcircle : ∀ z ∈ Ioo jL jR, ∀ q : UnitCircle, (T (z, (q : E2))).2 ∈ range (c z)) :
    ∃ phi : ℝ → CircleDiff,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => phi p.1 p.2) (Ioo jL jR ×ˢ univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => (phi p.1).symm p.2) (Ioo jL jR ×ˢ univ) ∧
      (∀ z ∈ Ioo jL jR, ∀ q : UnitCircle,
        (phi z q : E2) = (G0.chart.symm (T (z, (q : E2)))).2 ∧
        ((phi z).symm q : E2) = (T.symm (G0.chart (z, (q : E2)))).2 ∧
        c z (phi z q) = (T (z, (q : E2))).2) ∧
      ∀ z ∉ Ioo jL jR, ∀ q : UnitCircle, phi z q = q := by
  classical
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
  have hsrc (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      (z, (q : E2)) ∈ T.source := hsource ⟨hz, sphere_subset_closedBall q.property⟩
  have hinvheight (p : P) (hp : p ∈ T.target) : (T.symm p).1 = p.1 := by
    have hh := hheight (T.symm p) (T.map_target hp)
    rw [T.right_inv hp] at hh
    exact hh.symm
  have hTf (z : ℝ) (hz : z ∈ Ioo jL jR) :
      IsPlanarEmbedding (fun q : UnitCircle => (T (z, (q : E2))).2) := by
    have hN : ∃ N : BallNeighborhoodChart E2 E2,
        (N.chart : E2 → E2) = fun x => (T (z, x)).2 := by
      have hf : ContDiffOn ℝ ∞ (fun x : E2 => (T (z, x)).2)
          {x | (z, x) ∈ T.source} :=
        (hT.comp (contDiff_prodMk_right z).contDiffOn (fun _ hx => hx)).snd
      have hi : ContDiffOn ℝ ∞ (fun y : E2 => (T.symm (z, y)).2)
          {y | (z, y) ∈ T.target} :=
        (hTi.comp (contDiff_prodMk_right z).contDiffOn (fun _ hy => hy)).snd
      have hforward (x : E2) (hx : (z, x) ∈ T.source) :
          (z, (T (z, x)).2) = T (z, x) := Prod.ext (hheight (z, x) hx).symm rfl
      have hinverse (y : E2) (hy : (z, y) ∈ T.target) :
          (z, (T.symm (z, y)).2) = T.symm (z, y) :=
        Prod.ext (hinvheight (z, y) hy).symm rfl
      let n : OpenPartialHomeomorph E2 E2 := {
        toFun := fun x => (T (z, x)).2
        invFun := fun y => (T.symm (z, y)).2
        source := {x | (z, x) ∈ T.source}
        target := {y | (z, y) ∈ T.target}
        map_source' := by
          intro x hx
          change (z, (T (z, x)).2) ∈ T.target
          rw [hforward x hx]
          exact T.map_source hx
        map_target' := by
          intro y hy
          change (z, (T.symm (z, y)).2) ∈ T.source
          rw [hinverse y hy]
          exact T.map_target hy
        left_inv' := by
          intro x hx
          rw [hforward x hx, T.left_inv hx]
        right_inv' := by
          intro y hy
          rw [hinverse y hy, T.right_inv hy]
        open_source := T.open_source.preimage (continuous_const.prodMk continuous_id)
        open_target := T.open_target.preimage (continuous_const.prodMk continuous_id)
        continuousOn_toFun := hf.continuousOn
        continuousOn_invFun := hi.continuousOn }
      exact ⟨⟨n, fun _ hx => hsource ⟨hz, hx⟩, hf, hi⟩, rfl⟩
    obtain ⟨N, he⟩ := hN
    have hsm : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞
        (fun q : UnitCircle => (T (z, (q : E2))).2) := by
      intro q
      have hq := N.closedBall_subset_source (sphere_subset_closedBall q.property)
      have hh := N.smooth.contDiffAt (N.chart.open_source.mem_nhds hq)
      rw [he] at hh
      exact hh.contMDiffAt.comp q contMDiff_coe_sphere.contMDiffAt
    refine ⟨hsm, ?_, ?_⟩
    · intro p q hpq
      apply Subtype.ext
      apply N.chart.injOn
        (N.closedBall_subset_source (sphere_subset_closedBall p.property))
        (N.closedBall_subset_source (sphere_subset_closedBall q.property))
      rw [he]
      exact hpq
    · intro q
      let i : UnitCircle → E2 := fun p => (p : E2)
      have hi : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ i := contMDiff_coe_sphere
      have hdi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) i q) := by
        intro v w hvw
        exact injective_mvfderiv_subtypeVal_sphere q
          (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (q : E2)) hvw)
      have hq := N.closedBall_subset_source (sphere_subset_closedBall q.property)
      obtain ⟨A, hA⟩ := exists_smoothChart_derivative N.chart N.smooth N.smooth_symm hq
      have hcomp : (fun q : UnitCircle => (T (z, (q : E2))).2) = N.chart ∘ i := by
        funext p
        exact (congrFun he (p : E2)).symm
      rw [hcomp, mfderiv_comp q hA.differentiableAt.mdifferentiableAt
        (hi.mdifferentiable (by simp) q), mfderiv_eq_fderiv, hA.fderiv]
      exact A.injective.comp hdi
  have hGsource (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      (z, (q : E2)) ∈ G0.chart.source :=
    G0.mem_source (hJband hz)
      (mem_ball_zero_iff.mpr ((norm_eq_of_mem_sphere q).trans_lt G0.one_lt_radius))
  have hmatchExists (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      ∃ eta : UnitCircle, G0.chart (z, (eta : E2)) = T (z, (q : E2)) := by
    obtain ⟨eta, heta⟩ := hcircle z hz q
    refine ⟨eta, ?_⟩
    rw [G0.chart_apply, D0.chart_boundary z (hJband hz) eta]
    exact Prod.ext (hheight _ (hsrc z hz q)).symm heta
  have htarget (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      T (z, (q : E2)) ∈ G0.chart.target := by
    obtain ⟨eta, he⟩ := hmatchExists z hz q
    rw [← he]
    exact G0.chart.map_source (hGsource z hz eta)
  have hinverse (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      ∃ eta : UnitCircle, G0.chart.symm (T (z, (q : E2))) = (z, (eta : E2)) ∧
        c z eta = (T (z, (q : E2))).2 := by
    obtain ⟨eta, he⟩ := hmatchExists z hz q
    refine ⟨eta, ?_, ?_⟩
    · rw [← he, G0.chart.left_inv (hGsource z hz eta)]
    · rw [← he, G0.chart_apply, D0.chart_boundary z (hJband hz) eta]
  obtain ⟨zbase, hzbase⟩ := exists_between hJ
  obtain ⟨qbase, _hqbase⟩ := hmatchExists zbase hzbase (sphereCircleParameter e 0)
  let F : ℝ → UnitCircle → UnitCircle := fun z q =>
    unitRadialProjection qbase (G0.chart.symm (T (z, (q : E2)))).2
  have hF (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      (F z q : E2) = (G0.chart.symm (T (z, (q : E2)))).2 ∧
        G0.chart (z, (F z q : E2)) = T (z, (q : E2)) ∧
        c z (F z q) = (T (z, (q : E2))).2 := by
    obtain ⟨eta, hi, hc⟩ := hinverse z hz q
    have he : F z q = eta := by
      change unitRadialProjection qbase (G0.chart.symm (T (z, (q : E2)))).2 = eta
      rw [hi]
      exact unitRadialProjection_apply_coe qbase eta
    rw [he]
    refine ⟨congrArg Prod.snd hi.symm, ?_, hc⟩
    rw [← hi, G0.chart.right_inv (htarget z hz q)]
  have hFsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : ℝ × UnitCircle => F p.1 p.2) (Ioo jL jR ×ˢ univ) := by
    apply contMDiffOn_sphere_of_coe (isOpen_Ioo.prod isOpen_univ)
    have hinner : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, P) ∞
        (fun p : ℝ × UnitCircle => T (p.1, (p.2 : E2))) (Ioo jL jR ×ˢ univ) := by
      intro p hp
      have hs := hT.contDiffAt (T.open_source.mem_nhds (hsrc p.1 hp.1 p.2))
      exact (hs.contMDiffAt.comp p
        (contMDiffAt_fst.prodMk_space
          (contMDiff_coe_sphere.contMDiffAt.comp p contMDiffAt_snd))).contMDiffWithinAt
    have hout := G0.smooth_symm.contMDiffOn.comp hinner
      (fun p hp => htarget p.1 hp.1 p.2)
    exact (contDiff_snd.contMDiff.comp_contMDiffOn hout).congr
      (fun p hp => (hF p.1 hp.1 p.2).1)
  have hFslice (z : ℝ) (hz : z ∈ Ioo jL jR) :
      ContMDiff (𝓡 1) (𝓡 1) ∞ (F z) := by
    have hp : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
        (fun q : UnitCircle => (z, q)) := contMDiff_const.prodMk contMDiff_id
    exact ContMDiffOn.comp_contMDiff
      (g := fun p : ℝ × UnitCircle => F p.1 p.2) (f := fun q : UnitCircle => (z, q))
      hFsm hp (fun _ => ⟨hz, mem_univ _⟩)
  have hFinj (z : ℝ) (hz : z ∈ Ioo jL jR) : Injective (F z) := by
    intro q r h
    apply (hTf z hz).2.1
    change (T (z, (q : E2))).2 = (T (z, (r : E2))).2
    rw [← (hF z hz q).2.2, ← (hF z hz r).2.2, h]
  have hFimm (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      Injective (mfderiv (𝓡 1) (𝓡 1) (F z) q) := by
    have hc : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (c z) := by
      have hg : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞
          (fun q : UnitCircle => D0.chart z (q : E2)) := by
        intro p
        have hs := (G0.fiber_contDiffOn (hJband hz)).contDiffAt
          (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
            ((norm_eq_of_mem_sphere p).trans_lt G0.one_lt_radius)))
        exact hs.contMDiffAt.comp p contMDiff_coe_sphere.contMDiffAt
      exact hg.congr (fun p => (D0.chart_boundary z (hJband hz) p).symm)
    have he : c z ∘ F z = fun q : UnitCircle => (T (z, (q : E2))).2 :=
      funext (fun q => (hF z hz q).2.2)
    have hd := mfderiv_comp q (hc.mdifferentiable (by simp) _)
      ((hFslice z hz).mdifferentiable (by simp) q)
    rw [he] at hd
    intro v w hvw
    apply (hTf z hz).2.2 q
    rw [hd]
    exact congrArg (mfderiv (𝓡 1) 𝓘(ℝ, E2) (c z) (F z q)) hvw
  have hFsurj (z : ℝ) (hz : z ∈ Ioo jL jR) : Surjective (F z) := by
    let fc : ℝ → UnitCircle → E2 := fun _ q => (F z q : E2)
    have hfc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => fc p.1 p.2) :=
      ((contMDiff_coe_sphere (E := E2) (n := 1)).comp (hFslice z hz)).comp contMDiff_snd
    have hfi (q : UnitCircle) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) (fc 0) q) := by
      have hi : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (fun p : UnitCircle => (p : E2)) :=
        contMDiff_coe_sphere
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2)
        ((fun p : UnitCircle => (p : E2)) ∘ F z) q)
      rw [mfderiv_comp q (hi.mdifferentiable (by simp) _)
        ((hFslice z hz).mdifferentiable (by simp) q)]
      apply Injective.comp _ (hFimm z hz q)
      intro v w hvw
      exact injective_mvfderiv_subtypeVal_sphere (F z q)
        (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F z q : E2)) hvw)
    let gamma : ℝ → E2 := fun t => F z (sphereCircleParameter e t)
    have hgamma : ContDiff ℝ ∞ gamma :=
      (((contMDiff_coe_sphere (E := E2) (n := 1)).comp (hFslice z hz)).comp
        (contMDiff_sphereCircleParameter e)).contDiff
    have hgn (t : ℝ) : deriv gamma t ≠ 0 :=
      deriv_curveFamily_circleParameter_ne_zero e fc hfc 0 t (hfi _)
    obtain ⟨s0, hs0⟩ := surjective_sphereCircleParameter e (F z (sphereCircleParameter e 0))
    obtain ⟨b, hb, _hb0, hbphase⟩ := exists_contDiff_sphere_parameter_lift e gamma hgamma
      (fun t => norm_eq_of_mem_sphere _) 0 s0 (congrArg Subtype.val hs0)
    have hbne (t : ℝ) : deriv b t ≠ 0 := by
      intro ht
      have hd := (hasDerivAt_sphereCircleParameter_coe e (b t)).scomp t
        (hb.differentiable (by simp) t).hasDerivAt
      have he : ((fun s => (sphereCircleParameter e s : E2)) ∘ b) = gamma := funext hbphase
      rw [he, ht, zero_smul] at hd
      exact hgn t hd.deriv
    have hbper : Periodic (fun t => sphereCircleParameter e (b t)) (2 * Real.pi) := by
      intro t
      apply Subtype.ext
      rw [hbphase, hbphase]
      exact congrArg (fun q => (F z q : E2)) (periodic_sphereCircleParameter e t)
    have hbinj (s t : ℝ) (h : sphereCircleParameter e (b s) = sphereCircleParameter e (b t)) :
        sphereCircleParameter e s = sphereCircleParameter e t := by
      apply hFinj z hz
      apply Subtype.ext
      change gamma s = gamma t
      rw [← hbphase, ← hbphase]
      exact congrArg Subtype.val h
    have hbd : Continuous (deriv b) := hb.continuous_deriv (by simp)
    have hsign : (∀ t, 0 < deriv b t) ∨ ∀ t, deriv b t < 0 := by
      rcases lt_or_gt_of_ne (hbne 0) with hneg | hpos
      · right
        intro t
        by_contra ht
        obtain ⟨r, hr⟩ := intermediate_value_univ 0 t hbd ⟨hneg.le, le_of_not_gt ht⟩
        exact hbne r hr
      · left
        intro t
        by_contra ht
        obtain ⟨r, hr⟩ := intermediate_value_univ t 0 hbd ⟨le_of_not_gt ht, hpos.le⟩
        exact hbne r hr
    have hbs : Surjective b := by
      have hp : 0 < 2 * Real.pi := by positivity
      rcases hsign with hpos | hneg
      · exact surjective_of_add_period hp hb.continuous
          (circle_lift_add_period_of_positive e b hb hpos hbper hbinj)
      · let b' : ℝ → ℝ := fun t => b (-t)
        have hb' : ContDiff ℝ ∞ b' := hb.comp contDiff_neg
        have hb'p (t : ℝ) : 0 < deriv b' t := by
          have hd := ((hb.differentiable (by simp) (-t)).hasDerivAt).comp t
            (hasDerivAt_id t).neg
          change HasDerivAt b' (deriv b (-t) * -1) t at hd
          rw [hd.deriv]
          nlinarith [hneg (-t)]
        have hb'per : Periodic (fun t => sphereCircleParameter e (b' t)) (2 * Real.pi) := by
          intro t
          change sphereCircleParameter e (b (-(t + 2 * Real.pi))) = _
          rw [neg_add, ← sub_eq_add_neg]
          exact hbper.sub_eq (-t)
        have hb'inj (s t : ℝ)
            (h : sphereCircleParameter e (b' s) = sphereCircleParameter e (b' t)) :
            sphereCircleParameter e s = sphereCircleParameter e t := by
          have hh := congrArg (fun q : UnitCircle =>
            e (starRingEnd ℂ (e.symm (q : E2)))) (hbinj (-s) (-t) h)
          apply Subtype.ext
          simpa only [sphereCircleParameter, e.symm_apply_apply, Circle.exp_neg,
            Circle.coe_inv_eq_conj, starRingEnd_self_apply] using hh
        have hs := surjective_of_add_period hp hb'.continuous
          (circle_lift_add_period_of_positive e b' hb' hb'p hb'per hb'inj)
        intro y
        obtain ⟨t, ht⟩ := hs y
        exact ⟨-t, ht⟩
    intro q
    obtain ⟨t, rfl⟩ := surjective_sphereCircleParameter e q
    obtain ⟨s, hs⟩ := hbs t
    refine ⟨sphereCircleParameter e s, Subtype.ext ?_⟩
    change gamma s = (sphereCircleParameter e t : E2)
    rw [← hbphase, hs]
  let V : ℝ → UnitCircle → UnitCircle := fun z q =>
    unitRadialProjection qbase (T.symm (G0.chart (z, (q : E2)))).2
  have hV (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      G0.chart (z, (q : E2)) ∈ T.target ∧
        (V z q : E2) = (T.symm (G0.chart (z, (q : E2)))).2 ∧
        F z (V z q) = q := by
    obtain ⟨p, rfl⟩ := hFsurj z hz q
    rw [(hF z hz p).2.1]
    have he : V z (F z p) = p := by
      change unitRadialProjection qbase (T.symm (G0.chart (z, (F z p : E2)))).2 = p
      rw [(hF z hz p).2.1, T.left_inv (hsrc z hz p)]
      exact unitRadialProjection_apply_coe qbase p
    exact ⟨T.map_source (hsrc z hz p), by rw [he, T.left_inv (hsrc z hz p)], by rw [he]⟩
  have hVsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : ℝ × UnitCircle => V p.1 p.2) (Ioo jL jR ×ˢ univ) := by
    apply contMDiffOn_sphere_of_coe (isOpen_Ioo.prod isOpen_univ)
    have hinner : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, P) ∞
        (fun p : ℝ × UnitCircle => G0.chart (p.1, (p.2 : E2))) (Ioo jL jR ×ˢ univ) := by
      intro p hp
      have hs := G0.smooth.contDiffAt (G0.chart.open_source.mem_nhds (hGsource p.1 hp.1 p.2))
      exact (hs.contMDiffAt.comp p (contMDiffAt_fst.prodMk_space
        (contMDiff_coe_sphere.contMDiffAt.comp p contMDiffAt_snd))).contMDiffWithinAt
    have hout := hTi.contMDiffOn.comp hinner
      (fun p hp => (hV p.1 hp.1 p.2).1)
    exact (contDiff_snd.contMDiff.comp_contMDiffOn hout).congr
      (fun p hp => (hV p.1 hp.1 p.2).2.1)
  have hVslice (z : ℝ) (hz : z ∈ Ioo jL jR) :
      ContMDiff (𝓡 1) (𝓡 1) ∞ (V z) := by
    have hp : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
        (fun q : UnitCircle => (z, q)) := contMDiff_const.prodMk contMDiff_id
    exact ContMDiffOn.comp_contMDiff
      (g := fun p : ℝ × UnitCircle => V p.1 p.2) (f := fun q : UnitCircle => (z, q))
      hVsm hp (fun _ => ⟨hz, mem_univ _⟩)
  let phi : ℝ → CircleDiff := fun z => if hz : z ∈ Ioo jL jR then {
    toEquiv := {
      toFun := F z
      invFun := V z
      left_inv := fun q => hFinj z hz ((hV z hz (F z q)).2.2)
      right_inv := fun q => (hV z hz q).2.2 }
    contMDiff_toFun := hFslice z hz
    contMDiff_invFun := hVslice z hz }
    else Diffeomorph.refl (𝓡 1) UnitCircle ∞
  refine ⟨phi, ?_, ?_, ?_, ?_⟩
  · exact hFsm.congr (fun p hp => by simp only [phi, dif_pos hp.1]; rfl)
  · exact hVsm.congr (fun p hp => by simp only [phi, dif_pos hp.1]; rfl)
  · intro z hz q
    simp only [phi, dif_pos hz]
    exact ⟨(hF z hz q).1, (hV z hz q).2.1, (hF z hz q).2.2⟩
  · intro z hz q
    simp only [phi, dif_neg hz, Diffeomorph.coe_refl, id_eq]

end PoincareConjecture.M25.Topology3D
