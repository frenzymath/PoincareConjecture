import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Uniqueness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.GeodesicFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem IsGeodesicOn.hasDerivAt_chart_at
    {g : RiemannianMetric n M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) {t : ℝ} (ht : t ∈ s) (p : M)
    (hp : γ t ∈ (extChartAt (𝓡 n) p).source) :
    let q := fun u => extChartAt (𝓡 n) p (γ u)
    HasDerivAt q (deriv q t) t ∧
      HasDerivAt (deriv q)
        (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (q t) (deriv q t) (deriv q t)) t := by
  obtain ⟨U, hU, htU, hgeo⟩ := hγ.exists_open_nhds ht
  have hmap := (hγ.contMDiffAt ht).continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source p).mem_nhds hp)
  obtain ⟨V, hVsub, hV, htV⟩ := mem_nhds_iff.mp hmap
  exact (show g.IsGeodesicOn γ (U ∩ V) from fun u hu => hgeo u hu.1)
    |>.hasDerivAt_in_chart (hU.inter hV) p (fun u hu => hVsub hu.2) t ⟨htU, htV⟩

private theorem contDiffAt_coordinate_transition (p r : M)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) p).target)
    (hr : (extChartAt (𝓡 n) p).symm x ∈ (extChartAt (𝓡 n) r).source) :
    ContDiffAt ℝ ∞
      (fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hr)).comp x
    ((contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx))

theorem IsGeodesicOn.chart_deriv_transition
    {g : RiemannianMetric n M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) {t : ℝ} (ht : t ∈ s) (p r : M)
    (hp : γ t ∈ (extChartAt (𝓡 n) p).source)
    (hr : γ t ∈ (extChartAt (𝓡 n) r).source) :
    deriv (fun u => extChartAt (𝓡 n) r (γ u)) t =
      fderiv ℝ (fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y))
        (extChartAt (𝓡 n) p (γ t))
        (deriv (fun u => extChartAt (𝓡 n) p (γ u)) t) := by
  let f := fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)
  have hf : ContDiffAt ℝ ∞ f (extChartAt (𝓡 n) p (γ t)) :=
    contDiffAt_coordinate_transition p r ((extChartAt (𝓡 n) p).map_source hp)
      (by simpa only [(extChartAt (𝓡 n) p).left_inv hp] using hr)
  have hd := (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hγ.hasDerivAt_chart_at ht p hp).1
  apply HasDerivAt.deriv
  apply hd.congr_of_eventuallyEq
  filter_upwards [(hγ.contMDiffAt ht).continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source p).mem_nhds hp)] with u hu
  simp only [f, (extChartAt (𝓡 n) p).left_inv hu, Function.comp_apply]

theorem isGeodesicOn_chart_flow_translate
    (g : RiemannianMetric n M) (p : M)
    {Φ : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {J : Set ℝ} (hJ : IsOpen J)
    (hΦ : ∀ t ∈ J,
      (Φ t).1 ∈ (extChartAt (𝓡 n) p).target ∧
      HasDerivAt Φ
        (coordinateGeodesicField (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (Φ t)) t) (a : ℝ) :
    g.IsGeodesicOn
      (fun t => (extChartAt (𝓡 n) p).symm (Φ (t - a)).1)
      ((fun t : ℝ => t - a) ⁻¹' J) := by
  intro t ht
  refine ⟨p, fun u => (Φ (u - a)).1, fun u => (Φ (u - a)).2, ?_⟩
  have htime : Continuous (fun u : ℝ => u - a) := continuous_id.sub continuous_const
  filter_upwards [(hJ.preimage htime).mem_nhds ht] with u hu
  refine ⟨rfl, (hΦ (u - a) hu).1, ?_, ?_⟩
  · simpa [Function.comp_def, coordinateGeodesicField] using
      (((hΦ (u - a) hu).2.hasFDerivAt.fst).hasDerivAt.scomp u
        ((hasDerivAt_id u).sub_const a))
  · simpa [Function.comp_def, coordinateGeodesicField] using
      (((hΦ (u - a) hu).2.hasFDerivAt.snd).hasDerivAt.scomp u
        ((hasDerivAt_id u).sub_const a))

theorem hasDerivAt_chart_flow_translate
    (g : RiemannianMetric n M) (p : M)
    {Φ : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {J : Set ℝ} (hJ : IsOpen J)
    (hΦ : ∀ t ∈ J,
      (Φ t).1 ∈ (extChartAt (𝓡 n) p).target ∧
      HasDerivAt Φ
        (coordinateGeodesicField (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (Φ t)) t) {a t : ℝ} (ht : t - a ∈ J) :
    HasDerivAt
      (fun u => extChartAt (𝓡 n) p ((extChartAt (𝓡 n) p).symm (Φ (u - a)).1))
      (Φ (t - a)).2 t := by
  have hd : HasDerivAt (fun u => (Φ (u - a)).1) (Φ (t - a)).2 t := by
    simpa [Function.comp_def, coordinateGeodesicField] using
      (((hΦ (t - a) ht).2.hasFDerivAt.fst).hasDerivAt.scomp t
        ((hasDerivAt_id t).sub_const a))
  apply hd.congr_of_eventuallyEq
  filter_upwards [(continuousAt_id.sub continuousAt_const).preimage_mem_nhds
    (hJ.mem_nhds ht)] with u hu
  exact (extChartAt (𝓡 n) p).right_inv (hΦ (u - a) hu).1

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiffAt_chart_velocity_transition
    {g : RiemannianMetric n M} {Γ : P → ℝ → M} {s : Set ℝ} {v : P} {t : ℝ}
    (hgeo : ∀ᶠ z in 𝓝 v, g.IsGeodesicOn (Γ z) s) (ht : t ∈ s)
    (hpnt : ContMDiffAt (𝓘(ℝ, P)) (𝓡 n) ∞ (fun z => Γ z t) v)
    (p r : M) (hp : Γ v t ∈ (extChartAt (𝓡 n) p).source)
    (hr : Γ v t ∈ (extChartAt (𝓡 n) r).source)
    (hvel : ContDiffAt ℝ ∞
      (fun z => deriv (fun u => extChartAt (𝓡 n) p (Γ z u)) t) v) :
    ContDiffAt ℝ ∞
      (fun z => deriv (fun u => extChartAt (𝓡 n) r (Γ z u)) t) v := by
  let f := fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)
  have hf : ContDiffAt ℝ ∞ f (extChartAt (𝓡 n) p (Γ v t)) :=
    contDiffAt_coordinate_transition p r ((extChartAt (𝓡 n) p).map_source hp)
      (by simpa only [(extChartAt (𝓡 n) p).left_inv hp] using hr)
  have hq : ContDiffAt ℝ ∞ (fun z => extChartAt (𝓡 n) p (Γ z t)) v := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hp)).comp v hpnt
  have hsmooth0 := (hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).comp v hq
  have hsmooth := hsmooth0.clm_apply hvel
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [hgeo,
    hpnt.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source p).mem_nhds hp),
    hpnt.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source r).mem_nhds hr)]
    with z hz hzp hzr
  exact hz.chart_deriv_transition ht p r hzp hzr

theorem IsGeodesicOn.eq_nhds_chart_flow [T2Space M]
    {g : RiemannianMetric n M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hs : Convex ℝ s) (p : M)
    {δ : ℝ} (hδ : 0 < δ)
    {Φ : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hΦ : ∀ t ∈ Ioo (-δ) δ,
      (Φ t).1 ∈ (extChartAt (𝓡 n) p).target ∧
      HasDerivAt Φ
        (coordinateGeodesicField (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (Φ t)) t)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hp : γ a ∈ (extChartAt (𝓡 n) p).source)
    (hinit : Φ 0 = (extChartAt (𝓡 n) p (γ a),
      deriv (fun t => extChartAt (𝓡 n) p (γ t)) a))
    (hab : b - a ∈ Ioo (-δ) δ) :
    γ =ᶠ[𝓝 b] (fun t => (extChartAt (𝓡 n) p).symm (Φ (t - a)).1) := by
  let J : Set ℝ := s ∩ Ioo (a - δ) (a + δ)
  have hJ : IsPreconnected J := (hs.inter (convex_Ioo _ _)).isPreconnected
  have haJ : a ∈ J := ⟨ha, by constructor <;> linarith⟩
  have hbJ : b ∈ J := ⟨hb, by constructor <;> linarith [hab.1, hab.2]⟩
  have hsub : J ⊆ (fun t : ℝ => t - a) ⁻¹' Ioo (-δ) δ := by
    intro t ht
    constructor <;> linarith [ht.2.1, ht.2.2]
  have hη := g.isGeodesicOn_chart_flow_translate p isOpen_Ioo hΦ a
  have hηJ : g.IsGeodesicOn
      (fun t => (extChartAt (𝓡 n) p).symm (Φ (t - a)).1) J :=
    fun t ht => hη t (hsub ht)
  have hγJ : g.IsGeodesicOn γ J := fun t ht => hγ t ht.1
  apply hγJ.eq_nhds_on_of_initial_data hηJ hJ haJ p hp _ _ b hbJ
  · simp only [sub_self, hinit, (extChartAt (𝓡 n) p).left_inv hp]
  · have hd := g.hasDerivAt_chart_flow_translate p isOpen_Ioo hΦ
      (a := a) (t := a) (by simpa using (show (0 : ℝ) ∈ Ioo (-δ) δ by
        constructor <;> linarith))
    simpa only [sub_self, hinit] using hd.deriv.symm

def SmoothGeodesicDataAt (Γ : P → ℝ → M) (v : P) (t : ℝ) : Prop :=
  ContMDiffAt (𝓘(ℝ, P)) (𝓡 n) ∞ (fun z => Γ z t) v ∧
    ContDiffAt ℝ ∞
      (fun z => deriv (fun u => extChartAt (𝓡 n) (Γ v t) (Γ z u)) t) v

theorem smooth_geodesic_step [T2Space M]
    {g : RiemannianMetric n M} {Γ : P → ℝ → M} {s : Set ℝ} {v : P}
    (hgeo : ∀ᶠ z in 𝓝 v, g.IsGeodesicOn (Γ z) s) (hs : Convex ℝ s)
    (p : M) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hp : Γ v a ∈ (extChartAt (𝓡 n) p).source)
    {V : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {δ : ℝ} {Φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hV : IsOpen V) (hδ : 0 < δ)
    (hphase : (extChartAt (𝓡 n) p (Γ v a),
      deriv (fun t => extChartAt (𝓡 n) p (Γ v t)) a) ∈ V)
    (hsmooth : ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-δ) δ))
    (hinit : ∀ z ∈ V, Φ (z, 0) = z)
    (hflow : ∀ z ∈ V, ∀ t ∈ Ioo (-δ) δ,
      (Φ (z, t)).1 ∈ (extChartAt (𝓡 n) p).target ∧
      HasDerivAt (fun u => Φ (z, u))
        (coordinateGeodesicField (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (Φ (z, t))) t)
    (hab : b - a ∈ Ioo (-δ) δ)
    (haSmooth : SmoothGeodesicDataAt (n := n) Γ v a) :
    SmoothGeodesicDataAt (n := n) Γ v b := by
  let zdata := fun z => (extChartAt (𝓡 n) p (Γ z a),
    deriv (fun t => extChartAt (𝓡 n) p (Γ z t)) a)
  have hq : ContDiffAt ℝ ∞ (fun z => extChartAt (𝓡 n) p (Γ z a)) v := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hp)).comp
      v haSmooth.1
  have hw := contDiffAt_chart_velocity_transition hgeo ha haSmooth.1 (Γ v a) p
    (mem_extChartAt_source _) hp haSmooth.2
  have hzdata : ContDiffAt ℝ ∞ zdata v := hq.prodMk hw
  have hdataV : ∀ᶠ z in 𝓝 v, zdata z ∈ V :=
    hzdata.continuousAt.preimage_mem_nhds (hV.mem_nhds hphase)
  have hsource : ∀ᶠ z in 𝓝 v, Γ z a ∈ (extChartAt (𝓡 n) p).source :=
    haSmooth.1.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source p).mem_nhds hp)
  have heq : ∀ᶠ z in 𝓝 v,
      Γ z =ᶠ[𝓝 b] (fun t => (extChartAt (𝓡 n) p).symm (Φ (zdata z, t - a)).1) := by
    filter_upwards [hgeo, hdataV, hsource] with z hz hzV hzp
    exact hz.eq_nhds_chart_flow hs p hδ (hflow (zdata z) hzV) ha hb hzp
      (hinit (zdata z) hzV) hab
  have hendpoint : ContDiffAt ℝ ∞ (fun z => Φ (zdata z, b - a)) v :=
    (hsmooth.contDiffAt ((hV.prod isOpen_Ioo).mem_nhds ⟨hphase, hab⟩)).comp v
      (hzdata.prodMk contDiffAt_const)
  have hendpointMem := (hflow (zdata v) hphase (b - a) hab).1
  have hpnt : ContMDiffAt (𝓘(ℝ, P)) (𝓡 n) ∞ (fun z => Γ z b) v := by
    have hcomp := ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hendpointMem)).comp v
      (contMDiffAt_iff_contDiffAt.mpr hendpoint.fst)
    apply hcomp.congr_of_eventuallyEq
    exact heq.mono fun z hz => hz.self_of_nhds
  have hvelocity : ContDiffAt ℝ ∞
      (fun z => deriv (fun t => extChartAt (𝓡 n) p (Γ z t)) b) v := by
    apply hendpoint.snd.congr_of_eventuallyEq
    filter_upwards [heq, hdataV] with z hz hzV
    have hd := g.hasDerivAt_chart_flow_translate p isOpen_Ioo
      (hflow (zdata z) hzV) hab
    exact ((hz.fun_comp (extChartAt (𝓡 n) p)).deriv_eq).trans hd.deriv
  have hpb : Γ v b ∈ (extChartAt (𝓡 n) p).source := by
    rw [heq.self_of_nhds.self_of_nhds]
    exact (extChartAt (𝓡 n) p).map_target hendpointMem
  exact ⟨hpnt, contDiffAt_chart_velocity_transition hgeo hb hpnt p (Γ v b)
    hpb (mem_extChartAt_source _) hvelocity⟩

theorem exists_smooth_geodesic_step_nhds [T2Space M]
    {g : RiemannianMetric n M} {Γ : P → ℝ → M} {s : Set ℝ} {v : P}
    (hgeo : ∀ᶠ z in 𝓝 v, g.IsGeodesicOn (Γ z) s) (hs : Convex ℝ s)
    {t : ℝ} (ht : t ∈ s) :
    ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      ∀ a ∈ U ∩ s, ∀ b ∈ U ∩ s,
        SmoothGeodesicDataAt (n := n) Γ v a →
          SmoothGeodesicDataAt (n := n) Γ v b := by
  let p := Γ v t
  let q := fun u => extChartAt (𝓡 n) p (Γ v u)
  have hp : Γ v t ∈ (extChartAt (𝓡 n) p).source := mem_extChartAt_source p
  have hbase := hgeo.self_of_nhds
  have hderiv := hbase.hasDerivAt_chart_at ht p hp
  obtain ⟨V, δ, Φ, hV, hphase, -, hδ, hsmooth, hinit, hflow⟩ :=
    g.exists_smooth_chart_geodesic_flow p (deriv q t)
  have hphaseNear : ∀ᶠ a in 𝓝 t, (q a, deriv q a) ∈ V :=
    (hderiv.1.continuousAt.prodMk hderiv.2.continuousAt).preimage_mem_nhds
      (hV.mem_nhds hphase)
  have hsource : ∀ᶠ a in 𝓝 t, Γ v a ∈ (extChartAt (𝓡 n) p).source :=
    (hbase.contMDiffAt ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source p).mem_nhds hp)
  have htime : Ioo (t - δ / 3) (t + δ / 3) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨U, hUsub, hU, htU⟩ := mem_nhds_iff.mp
    (hphaseNear.and (hsource.and htime))
  refine ⟨U, hU, htU, ?_⟩
  intro a ha b hb hsa
  have hab : b - a ∈ Ioo (-δ) δ := by
    have ha' := (hUsub ha.1).2.2
    have hb' := (hUsub hb.1).2.2
    constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]
  exact smooth_geodesic_step hgeo hs p ha.2 hb.2 (hUsub ha.1).2.1 hV hδ
    (hUsub ha.1).1 hsmooth hinit
    (fun z hz u hu => ⟨(hflow z hz u hu).1, (hflow z hz u hu).2.1⟩) hab hsa

theorem SmoothGeodesicDataAt.propagate [T2Space M]
    {g : RiemannianMetric n M} {Γ : P → ℝ → M} {s : Set ℝ} {v : P}
    (hgeo : ∀ᶠ z in 𝓝 v, g.IsGeodesicOn (Γ z) s) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hinit : SmoothGeodesicDataAt (n := n) Γ v a) :
    SmoothGeodesicDataAt (n := n) Γ v b := by
  let S : Set s := {t | SmoothGeodesicDataAt (n := n) Γ v t}
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.isPreconnected
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨U, hU, htU, hstep⟩ := exists_smooth_geodesic_step_nhds hgeo hs t.property
    apply Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds htU)
    intro u hu
    exact hstep t ⟨htU, t.property⟩ u ⟨hu, u.property⟩ ht
  have hcomplopen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨U, hU, htU, hstep⟩ := exists_smooth_geodesic_step_nhds hgeo hs t.property
    apply Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds htU)
    intro u hu hus
    exact ht (hstep u ⟨hu, u.property⟩ t ⟨htU, t.property⟩ hus)
  have hall : S = univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hcomplopen, hopen⟩).eq_univ
      ⟨⟨a, ha⟩, hinit⟩
  have hbS : (⟨b, hb⟩ : s) ∈ S := hall ▸ mem_univ _
  exact hbS

theorem contMDiffAt_geodesic_endpoint [T2Space M]
    {g : RiemannianMetric n M} {Γ : P → ℝ → M} {s : Set ℝ} {v : P}
    (hgeo : ∀ᶠ z in 𝓝 v, g.IsGeodesicOn (Γ z) s) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hpnt : ContMDiffAt (𝓘(ℝ, P)) (𝓡 n) ∞ (fun z => Γ z a) v)
    (hvel : ContDiffAt ℝ ∞
      (fun z => deriv (fun t => extChartAt (𝓡 n) (Γ v a) (Γ z t)) a) v) :
    ContMDiffAt (𝓘(ℝ, P)) (𝓡 n) ∞ (fun z => Γ z b) v :=
  (SmoothGeodesicDataAt.propagate hgeo hs ha hb ⟨hpnt, hvel⟩).1

end PoincareConjecture.RiemannianMetric
