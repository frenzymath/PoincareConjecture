import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_InteriorSurvival
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeEndpointFamily
import PoincareConjecture.Proofs.M14.Sec6_3_SquareFamilyAction
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurveEndpoints
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M14.Sec6_1_PathCongruence












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}





theorem smooth_action_recovery_of_represented_path
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x)
    {q : (G.slices (T - tau)).Point}
    (p : M14BackwardPath G T 0 tau x q.val)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (hcurve : EqOn p.curve (fun r => E.gamma Z (Real.sqrt r)) (Icc 0 tau))
    (htime : T - tau ∈ interior I.domain) :
    ∃ V : Set (G.slices (T - tau)).Point, IsOpen V ∧ q ∈ V ∧
      ∃ cost : (G.slices (T - tau)).Point → ℝ,
        ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ cost V ∧
        cost q = M14BackwardLAction G p ∧
        ∀ z ∈ V, ∃ r : M14BackwardPath G T 0 tau x z.val,
          M14BackwardLAction G r = cost z := by
  classical
  have htau : 0 < tau := p.tau_lt
  have hs : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hqgamma : q.val = E.gamma Z (Real.sqrt tau) :=
    p.curve_end.symm.trans (hcurve ⟨htau.le, le_rfl⟩)
  obtain ⟨b, hsb, hZb⟩ := exists_surviving_extension_at_interior E hs hZ
    (by simpa only [Real.sq_sqrt htau.le] using htime)
  have hb : 0 < b := hs.trans hsb
  have hsC : Real.sqrt tau ∈ Icc 0 b := ⟨hs.le, hsb.le⟩
  have hsub : M14SqrtParameterInterval 0 tau ⊆ Icc 0 b := by
    intro r hr
    exact ⟨by simpa only [Real.sqrt_zero] using hr.1, hr.2.trans hsb.le⟩
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (G.slices (T - tau)).Point :=
    (G.slices (T - tau)).chartedSpace
  let f : ℝ × ℝ → G.Point := fun z => E.gamma Z z.1
  have hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ f
      (Icc 0 b ×ˢ (univ : Set ℝ)) :=
    E.family_smooth.comp (contMDiff_const.prodMk contMDiff_fst).contMDiffOn
      (fun z hz => (E.maximal_lifetime Z).out (E.domain_zero Z) hZb hz.1)
  have hfclock (r : ℝ) (hr : r ∈ Icc 0 b) (a : ℝ) (_ha : a ∈ (univ : Set ℝ)) :
      G.spacetime.timeFunction (f (r, a)) = T - r ^ 2 :=
    E.clock Z r ((E.maximal_lifetime Z).out (E.domain_zero Z) hZb hr)
  obtain ⟨j, U, lift, hU, hqU, hlift, hright, hclock⟩ :=
    M14.exists_smooth_gauge_lift G q.val
  have hfcenter : f (Real.sqrt tau, 0) = q.val := hqgamma.symm
  obtain ⟨D⟩ := M14.gaugeEndpointFamily_nonempty f isOpen_univ (mem_univ (0 : ℝ))
    ⟨hs, hsb⟩ hf hfclock j lift hU hlift hright (hfcenter.symm ▸ hqU)
  let S0 := (Subtype.val : (G.slices (T - tau)).Point → G.Point) ⁻¹' U
  have hS0 : IsOpen S0 := hU.preimage continuous_subtype_val
  have hliftslice : ContMDiffOn (𝓡 n) (spacetimeModel n) ∞
      (fun z : (G.slices (T - tau)).Point => lift z.val) S0 :=
    hlift.comp (G.slices (T - tau)).inclusion_smooth.contMDiffOn (fun _ hz => hz)
  let par (z : (G.slices (T - tau)).Point) : ℝ × EuclideanSpace ℝ (Fin n) :=
    (0, (lift z.val).2.val)
  have hpar : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) ∞ par S0 := by
    have hzero : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
        (fun _ : (G.slices (T - tau)).Point => (0 : ℝ)) S0 := contMDiffOn_const
    have hspatial : ContMDiffOn (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : (G.slices (T - tau)).Point => (lift z.val).2.val) S0 :=
      contMDiff_subtype_val.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn hliftslice)
    exact hzero.prodMk_space hspatial
  let V := S0 ∩ par ⁻¹' D.parameters
  have hV : IsOpen V := hpar.continuousOn.isOpen_inter_preimage hS0 D.parameters_open
  have hqpar : par q = (0, (lift (f (Real.sqrt tau, 0))).2.val) := by
    rw [hfcenter]
  have hqV : q ∈ V := ⟨hqU, by change par q ∈ D.parameters; rw [hqpar]; exact D.center_mem⟩
  let cost (z : (G.slices (T - tau)).Point) :=
    M14.squareFamilyAction G D.family (Icc 0 b) 0 (Real.sqrt tau) (par z)
  have hcost : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ cost V :=
    (M14.squareFamilyAction_contDiffOn hM12 hb D.parameters_open D.smooth hsC).contMDiffOn.comp
      (hpar.mono inter_subset_left) (fun _ hz => hz.2)
  have hpaths (z : (G.slices (T - tau)).Point) (hz : z ∈ V) :
      ∃ r : M14BackwardPath G T 0 tau x z.val,
        (∀ t ∈ Icc 0 tau, r.curve t = D.family (Real.sqrt t, par z)) ∧
        M14BackwardLAction G r = cost z := by
    let alpha := fun s => D.family (s, par z)
    have halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ alpha (Icc 0 b) :=
      D.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
        (fun _ hr => ⟨hr, hz.2⟩)
    have halphaclock (r : ℝ) (hr : r ∈ M14SqrtParameterInterval 0 tau) :
        G.spacetime.timeFunction (alpha r) = T - r ^ 2 := D.clock r (hsub hr) (par z) hz.2
    have hstart : alpha (Real.sqrt 0) = x := by
      rw [Real.sqrt_zero]
      exact (D.initial (par z) hz.2).trans (E.gamma_at_zero Z)
    have hend : alpha (Real.sqrt tau) = z.val := by
      obtain ⟨hy, hmarked⟩ := D.marked (par z) hz.2
      have ht : (lift (f (Real.sqrt tau, 0))).1 = (lift z.val).1 := by
        apply Subtype.ext
        rw [hfcenter, hclock q.val hqU, hclock z.val hz.1, q.property, z.property]
      have hspatial : (⟨(par z).2, hy⟩ : G.gaugeCover.spatial j) = (lift z.val).2 :=
        Subtype.ext rfl
      rw [ht, hspatial] at hmarked
      exact hmarked.trans (hright z.val hz.1)
    let r := M14.backwardPathOfSquareCurveBetween hM12 (by norm_num : (0 : ℝ) ≤ 0)
      htau alpha (halpha.mono hsub) halphaclock hstart hend
    refine ⟨r, fun _ _ => rfl, ?_⟩
    have h := M14.integral_squareCurveDensity_eq_action_between hM12
      (by norm_num : (0 : ℝ) ≤ 0) htau alpha halpha hsub halphaclock hstart hend
    simpa only [r, cost, alpha, Real.sqrt_zero, M14.squareFamilyAction] using h.symm
  obtain ⟨r, hr, hraction⟩ := hpaths q hqV
  have hcenteraction : cost q = M14BackwardLAction G p := by
    apply hraction.symm.trans
    apply M14.action_eq_of_curve_eqOn r p
    intro t ht
    rw [hr t (Ioo_subset_Icc_self ht)]
    have hrecover := D.recovery (par q) hqV.2 (Real.sqrt t)
      ⟨Real.sqrt_nonneg t, (Real.sqrt_le_sqrt ht.2.le).trans hsb.le⟩
    have hparq : (par q).1 = 0 := rfl
    rw [hparq, ← hqpar] at hrecover
    exact hrecover.trans (hcurve (Ioo_subset_Icc_self ht)).symm
  exact ⟨V, hV, hqV, cost, hcost, hcenteraction, fun z hz =>
    (hpaths z hz).imp (fun _ h => h.2)⟩

end PoincareConjecture.Proofs.M46
