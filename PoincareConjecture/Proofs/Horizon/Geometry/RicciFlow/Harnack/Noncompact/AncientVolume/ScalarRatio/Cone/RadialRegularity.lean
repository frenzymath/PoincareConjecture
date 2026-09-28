import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialPotential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.EndpointAgreement
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakDerivative.LipschitzGreen











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

private theorem exists_smooth_endpoint_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set (E × E)} (hU : IsOpen U) {x : E} (hx : (x, 0) ∈ U)
    {e : E × E → E} (he : ContDiffOn ℝ ∞ e U) (he0 : e (x, 0) = x)
    (hed : HasFDerivAt (fun v => e (x, v)) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ G : OpenPartialHomeomorph (E × E) (E × E),
      (x, 0) ∈ G.source ∧ G.source ⊆ U ∧ (x, x) ∈ G.target ∧
      (∀ z, G z = (z.1, e z)) ∧ ContDiffOn ℝ ∞ G.symm G.target := by
  let A := fderiv ℝ e (x, 0)
  have hea := he.contDiffAt (hU.mem_nhds hx)
  have hA := (hea.differentiableAt (by simp)).hasFDerivAt
  have hright (v : E) : A (0, v) = v := by
    have hd := hA.comp 0 ((hasFDerivAt_const x (0 : E)).prodMk (hasFDerivAt_id (0 : E)))
    exact congrArg (fun L : E →L[ℝ] E => L v) (hd.unique hed)
  have hsplit (u v : E) : A (u, v) = A (u, 0) + v := by
    rw [show (u, v) = (u, 0) + (0, v) by ext <;> simp, map_add, hright]
  let L : (E × E) →L[ℝ] (E × E) := (ContinuousLinearMap.fst ℝ E E).prod A
  have hLi : Function.Injective L := by
    intro a b hab
    change (a.1, A a) = (b.1, A b) at hab
    have hfirst := congrArg Prod.fst hab
    change a.1 = b.1 at hfirst
    have hsecond : A a = A b := congrArg Prod.snd hab
    have hh : A (a.1, 0) + a.2 = A (b.1, 0) + b.2 := by
      simpa only [← hsplit] using hsecond
    rw [hfirst] at hh
    exact Prod.ext hfirst (add_left_cancel hh)
  let L' : (E × E) ≃L[ℝ] (E × E) := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hLi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hLi))
  let H : E × E → E × E := fun z => (z.1, e z)
  have hH : ContDiffOn ℝ ∞ H U := contDiffOn_fst.prodMk he
  have hHa := hH.contDiffAt (hU.mem_nhds hx)
  have hdH : HasFDerivAt H (L' : (E × E) →L[ℝ] (E × E)) (x, 0) :=
    hasFDerivAt_fst.prodMk hA
  have hinvert : {z : E × E | ∃ B : (E × E) ≃L[ℝ] (E × E),
      (B : (E × E) →L[ℝ] (E × E)) = fderiv ℝ H z} ∈ 𝓝 (x, 0) := by
    have hn := L'.nhds
    rw [← hdH.fderiv] at hn
    exact (hHa.fderiv_right (m := 0) (by simp)).continuousAt.preimage_mem_nhds hn
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hinvert)
  let G₀ := hHa.toOpenPartialHomeomorph H hdH (by simp)
  let G := G₀.restrOpen (Metric.ball (x, 0) r) Metric.isOpen_ball
  have hxG : (x, 0) ∈ G.source :=
    ⟨hHa.mem_toOpenPartialHomeomorph_source hdH (by simp), Metric.mem_ball_self hr⟩
  have hmap (z : E × E) : G z = (z.1, e z) := rfl
  refine ⟨G, hxG, (fun z hz => (hsub hz.2).1), ?_, hmap, ?_⟩
  · simpa only [hmap, he0] using G.map_source hxG
  · intro y hy
    have hz := G.map_target hy
    obtain ⟨B, hB⟩ := (hsub hz.2).2
    have hsm := hH.contDiffAt (hU.mem_nhds (hsub hz.2).1)
    have hd : HasFDerivAt G (B : (E × E) →L[ℝ] (E × E)) (G.symm y) := by
      change HasFDerivAt H (B : (E × E) →L[ℝ] (E × E)) (G.symm y)
      rw [hB]
      exact (hsm.differentiableAt (by simp)).hasFDerivAt
    exact (G.contDiffAt_symm hy hd hsm).contDiffWithinAt

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem exists_joint_normal_endpoint_coordinates
    (g : RiemannianMetric n M) (p : M) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    ∃ (W : Set (E × E)) (Ψ : (E × E) × ℝ → E × E)
        (G : OpenPartialHomeomorph (E × E) (E × E)),
      IsOpen W ∧ (c p, 0) ∈ W ∧
      ContDiffOn ℝ ∞ Ψ (W ×ˢ Ioo (-2 : ℝ) 2) ∧
      (∀ z ∈ W, Ψ (z, 0) = z) ∧
      (∀ z ∈ W, ∀ t ∈ Ioo (-2 : ℝ) 2,
        (Ψ (z, t)).1 ∈ c.target ∧
        HasDerivAt (fun s => Ψ (z, s)) (coordinateGeodesicField B (Ψ (z, t))) t) ∧
      G.source ⊆ W ∧ (c p, c p) ∈ G.target ∧
      (∀ z, G z = (z.1, (Ψ (z, 1)).1)) ∧ ContDiffOn ℝ ∞ G.symm G.target := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  obtain ⟨V, δ, Φ, hV, hbase, _, hδ, hΦ, hΦ0, hΦspec⟩ :=
    g.exists_smooth_chart_geodesic_flow p (0 : E)
  let a := δ / 2
  have ha : 0 < a := half_pos hδ
  let S := CoordinateExponential.velocityScale (E := E) a⁻¹
  let W := S ⁻¹' V
  let Ψ : (E × E) × ℝ → E × E := fun z =>
    CoordinateExponential.velocityScale a (Φ (S z.1, a * z.2))
  have hW : IsOpen W := hV.preimage S.continuous
  have hxW : (c p, (0 : E)) ∈ W := by
    have hz : S (c p, 0) = (c p, 0) := by ext <;> simp [S]
    change S (c p, 0) ∈ V
    rw [hz]
    exact hbase
  have htime {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) : a * t ∈ Ioo (-δ) δ := by
    have hl := mul_lt_mul_of_pos_left ht.1 ha
    have hu := mul_lt_mul_of_pos_left ht.2 ha
    dsimp [a] at *
    constructor <;> nlinarith
  have hΨ : ContDiffOn ℝ ∞ Ψ (W ×ˢ Ioo (-2 : ℝ) 2) := by
    apply (CoordinateExponential.velocityScale (E := E) a).contDiff.comp_contDiffOn
    exact hΦ.comp
      ((S.contDiff.comp contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)).contDiffOn
      (fun z hz => ⟨hz.1, htime hz.2⟩)
  have hΨ0 (z : E × E) (hz : z ∈ W) : Ψ (z, 0) = z := by
    dsimp [Ψ]
    rw [mul_zero, hΦ0 (S z) hz]
    ext <;> simp [S, smul_smul, ha.ne']
  have hΨspec (z : E × E) (hz : z ∈ W) (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) :
      (Ψ (z, t)).1 ∈ c.target ∧ HasDerivAt (fun s => Ψ (z, s))
        (coordinateGeodesicField B (Ψ (z, t))) t := by
    exact ⟨(hΦspec (S z) hz (a * t) (htime ht)).1,
      CoordinateExponential.hasDerivAt_velocityScale
        (hΦspec (S z) hz (a * t) (htime ht)).2.1⟩
  let Γ : E → ℝ → M := fun v t => c.symm (Ψ ((c p, v), t)).1
  have hnear : ∀ᶠ v : E in 𝓝 0, (c p, v) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hxW)
  have hgeodesic (v : E) (hv : (c p, v) ∈ W) :
      g.IsGeodesicOn (Γ v) (Ioo (-2 : ℝ) 2) := by
    exact g.isGeodesicOn_chart_curve p isOpen_Ioo
      (q := fun t => (Ψ ((c p, v), t)).1)
      (w := fun t => (Ψ ((c p, v), t)).2)
      (fun t ht => ⟨(hΨspec _ hv t ht).1,
        (hΨspec _ hv t ht).2.fst, (hΨspec _ hv t ht).2.snd⟩)
  have hΓ0 (v : E) (hv : (c p, v) ∈ W) : Γ v 0 = p := by
    dsimp [Γ]
    rw [hΨ0 _ hv]
    exact c.left_inv (mem_extChartAt_source p)
  have hΓv (v : E) (hv : (c p, v) ∈ W) :
      HasDerivAt (fun t => c (Γ v t)) v 0 := by
    have hd : HasDerivAt (fun t => (Ψ ((c p, v), t)).1) v 0 := by
      have hh : HasDerivAt (fun t => (Ψ ((c p, v), t)).1)
          (Ψ ((c p, v), 0)).2 0 := (hΨspec _ hv 0 (by norm_num)).2.fst
      simpa only [hΨ0 _ hv] using hh
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (-2 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 2)] with t ht
    exact c.right_inv (hΨspec _ hv t ht).1
  have hgeo : ∀ᶠ v in 𝓝 0, g.IsGeodesicOn (Γ v) (Icc (0 : ℝ) 1) := by
    filter_upwards [hnear] with v hv
    intro t ht
    exact hgeodesic v hv t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hend0, hendd⟩ := g.geodesic_endpoint_zero_and_hasFDerivAt p Γ hgeo
    (hnear.mono hΓ0) (hnear.mono hΓv)
  let e : E × E → E := fun z => (Ψ (z, 1)).1
  have he : ContDiffOn ℝ ∞ e W := hΨ.fst.comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, by norm_num⟩)
  have heq : (fun v => e (c p, v)) =ᶠ[𝓝 0] fun v => c (Γ v 1) := by
    filter_upwards [hnear] with v hv
    exact (c.right_inv (hΨspec _ hv 1 (by norm_num)).1).symm
  have he0 : e (c p, 0) = c p := by
    simpa only [hend0] using heq.self_of_nhds
  obtain ⟨G, _, hGW, hGt, hGmap, hGinv⟩ :=
    Poincare.AncientVolume.ScalarRatio.exists_smooth_endpoint_inverse hW hxW he he0
      (hendd.congr_of_eventuallyEq heq)
  exact ⟨W, Ψ, G, hW, hxW, hΨ, hΨ0, hΨspec, hGW, hGt, hGmap, hGinv⟩




theorem contMDiffAt_of_lipschitz_chart_geodesic_quadratic
    (g : RiemannianMetric n M) (f : M → ℝ) (p : M)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : U ∈ 𝓝 (extChartAt (𝓡 n) p p))
    {C : ℝ≥0} (hLip : LipschitzOnWith C (f ∘ (extChartAt (𝓡 n) p).symm) U)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f p := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  let F : E → ℝ := f ∘ c.symm
  obtain ⟨W, Ψ, G, _, _, _, hΨ0, hΨspec, hGW, hGt, hGmap, hGinv⟩ :=
    g.exists_joint_normal_endpoint_coordinates p
  have hnear : {q : E | (q, c p) ∈ G.target} ∈ 𝓝 (c p) :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (G.open_target.mem_nhds hGt)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hnear)
  have hLip' : LipschitzOnWith C F (Metric.ball (c p) r) :=
    hLip.mono (fun q hq => (hsub hq).1)
  have hae := Poincare.Analysis.WeakDerivative.ae_differentiableAt_of_lipschitzOn
    (volume : Measure E) Metric.isOpen_ball hLip'
  obtain ⟨q, hqball, hqdiff⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt (Metric.isOpen_ball.measure_pos (volume : Measure E)
      ⟨c p, Metric.mem_ball_self hr⟩))
    ((ae_restrict_iff' measurableSet_ball).mpr hae)
  have hqt : (q, c p) ∈ G.target := (hsub hqball).2
  let A := fderiv ℝ F q
  have hformula (v : E) (hv : (q, v) ∈ W) :
      F (Ψ ((q, v), 1)).1 = F q + A v + B q v v / 2 := by
    let z : ℝ → E := fun t => (Ψ ((q, v), t)).1
    let w : ℝ → E := fun t => (Ψ ((q, v), t)).2
    let γ : ℝ → M := fun t => c.symm (z t)
    have hz0 : z 0 = q := congrArg Prod.fst (hΨ0 (q, v) hv)
    have hw0 : w 0 = v := congrArg Prod.snd (hΨ0 (q, v) hv)
    have hdata (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
        z t ∈ c.target ∧ HasDerivAt z (w t) t ∧
        HasDerivAt w (-coordinateChristoffel B (z t) (w t) (w t)) t := by
      have h := hΨspec (q, v) hv t ⟨by linarith [ht.1], ht.2⟩
      exact ⟨h.1, h.2.fst, h.2.snd⟩
    have hγ : g.IsGeodesicOn γ (Ioo (-1 : ℝ) 2) :=
      g.isGeodesicOn_chart_curve p isOpen_Ioo hdata
    have hzd : HasDerivAt z v 0 := by
      simpa only [hw0] using (hdata 0 (by norm_num)).2.1
    have hFd : HasDerivAt (fun t => f (γ t)) (A v) 0 := by
      have hdiff : HasFDerivAt F A (z 0) := by
        rw [hz0]
        exact hqdiff.hasFDerivAt
      exact hdiff.comp_hasDerivAt 0 hzd
    have hspeed := g.tangentNorm_chart_curve p hzd (hdata 0 (by norm_num)).1
    have hQ : 0 ≤ B q v v := by
      let w := mfderiv (𝓡 n) (𝓡 n) c.symm q v
      change 0 ≤ g.inner (c.symm q) w w
      by_cases hw : w = 0
      · rw [hw]; simp
      · exact (g.pos (c.symm q) w hw).le
    have hsquare : g.tangentNorm (γ 0)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 = B q v v := by
      change g.tangentNorm (c.symm (z 0))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t => c.symm (z t)) 0 1) ^ 2 = _
      rw [hspeed, hz0, Real.sq_sqrt hQ]
    have h := Poincare.AncientVolume.ScalarRatio.endpoint_eq_of_quadratic_interpolation
      hFd (hquad γ 1 (by norm_num) (by convert! hγ using 1; norm_num))
    rw [hsquare] at h
    change F (z 1) = F (z 0) + A v + B q v v / 2 at h
    simpa only [hz0] using h
  let v : E → E := fun x => (G.symm (q, x)).2
  have hvsm : ContDiffAt ℝ ∞ v (c p) :=
    ((hGinv.contDiffAt (G.open_target.mem_nhds hqt)).comp (c p)
      (contDiffAt_const.prodMk contDiffAt_id)).snd
  let P : E → ℝ := fun x => F q + A (v x) + B q (v x) (v x) / 2
  have hP : ContDiffAt ℝ ∞ P (c p) := by
    exact (contDiffAt_const.add (A.contDiff.contDiffAt.comp (c p) hvsm)).add
      (((contDiffAt_const.clm_apply hvsm).clm_apply hvsm).div_const 2)
  have heq : F =ᶠ[𝓝 (c p)] P := by
    have htarget : ∀ᶠ x : E in 𝓝 (c p), (q, x) ∈ G.target :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (G.open_target.mem_nhds hqt)
    filter_upwards [htarget] with x hx
    have hsource := G.map_target hx
    have hinv := G.right_inv hx
    rw [hGmap] at hinv
    have hfirst := congrArg Prod.fst hinv
    change (G.symm (q, x)).1 = q at hfirst
    have hsecond := congrArg Prod.snd hinv
    change (Ψ (G.symm (q, x), 1)).1 = x at hsecond
    have hz : G.symm (q, x) = (q, v x) := Prod.ext hfirst rfl
    have hform := hformula (v x) (by rw [← hz]; exact hGW hsource)
    rw [hz] at hsecond
    simpa only [hsecond] using hform
  apply contMDiffAt_iff_source.mpr
  exact (hP.congr_of_eventuallyEq heq).contMDiffAt.contMDiffWithinAt





theorem contMDiff_of_locally_lipschitz_geodesic_quadratic
    (g : RiemannianMetric n M) (f : M → ℝ)
    (hLip : ∀ p : M, ∃ U ∈ 𝓝 (extChartAt (𝓡 n) p p), ∃ C : ℝ≥0,
      LipschitzOnWith C (f ∘ (extChartAt (𝓡 n) p).symm) U)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := by
  intro p
  obtain ⟨U, hU, C, hC⟩ := hLip p
  exact g.contMDiffAt_of_lipschitz_chart_geodesic_quadratic f p hU hC hquad

end PoincareConjecture.RiemannianMetric
