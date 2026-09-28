import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.EndpointAgreement

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.AncientVolume.ScalarRatio

private theorem exists_smooth_local_endpoint_inverse
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

theorem exists_joint_normal_endpoints_in_open
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {U : Set M} (hU : IsOpen U) {p : M} (hp : p ∈ U) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    ∃ (W : Set (E × E)) (Γ : E × E → ℝ → M)
        (G : OpenPartialHomeomorph (E × E) (E × E)),
      IsOpen W ∧ (c p, 0) ∈ W ∧ W ⊆ c.target ×ˢ univ ∧
      (∀ z ∈ W, g.IsGeodesicOn (Γ z) (Ioo (-2 : ℝ) 2) ∧
        Γ z 0 = c.symm z.1 ∧ HasDerivAt (fun t => c (Γ z t)) z.2 0 ∧
        MapsTo (Γ z) (Ioo (-2 : ℝ) 2) U) ∧
      G.source ⊆ W ∧ (c p, c p) ∈ G.target ∧
      (∀ z ∈ G.source, G z = (z.1, c (Γ z 1))) ∧
      ContDiffOn ℝ ∞ G.symm G.target := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  let O := c.target ∩ c.symm ⁻¹' U
  have hO : IsOpen O := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).continuousOn
    |>.isOpen_inter_preimage (isOpen_extChartAt_target (I := 𝓡 n) p) hU
  have hpO : c p ∈ O := ⟨mem_extChartAt_target p, by
    change c.symm (c p) ∈ U
    rw [c.left_inv (mem_extChartAt_source p)]
    exact hp⟩
  obtain ⟨V, δ, Φ, hV, hbase, hVO, hδ, hΦ, hΦ0, hΦspec⟩ :=
    PoincareConjecture.exists_smooth_coordinate_geodesic_flow hO
      ((g.contDiffOn_chartCoefficients p).mono inter_subset_left)
      (fun x hx => g.isInvertible_chartCoefficients p hx.1)
      (fun x _ v w => g.symm _ _ _) hpO (0 : E)
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
      (Ψ (z, t)).1 ∈ O ∧ HasDerivAt (fun s => Ψ (z, s))
        (coordinateGeodesicField B (Ψ (z, t))) t := by
    exact ⟨(hΦspec (S z) hz (a * t) (htime ht)).1,
      CoordinateExponential.hasDerivAt_velocityScale
        (hΦspec (S z) hz (a * t) (htime ht)).2.1⟩
  let Γ : E × E → ℝ → M := fun z t => c.symm (Ψ (z, t)).1
  have hgeodesic (z : E × E) (hz : z ∈ W) :
      g.IsGeodesicOn (Γ z) (Ioo (-2 : ℝ) 2) := by
    exact g.isGeodesicOn_chart_curve p isOpen_Ioo
      (q := fun t => (Ψ (z, t)).1) (w := fun t => (Ψ (z, t)).2)
      (fun t ht => ⟨(hΨspec z hz t ht).1.1,
        (hΨspec z hz t ht).2.fst, (hΨspec z hz t ht).2.snd⟩)
  have hΓ0 (z : E × E) (hz : z ∈ W) : Γ z 0 = c.symm z.1 := by
    dsimp [Γ]
    rw [hΨ0 z hz]
  have hΓv (z : E × E) (hz : z ∈ W) : HasDerivAt (fun t => c (Γ z t)) z.2 0 := by
    have hd : HasDerivAt (fun t => (Ψ (z, t)).1) z.2 0 := by
      have hh : HasDerivAt (fun t => (Ψ (z, t)).1) (Ψ (z, 0)).2 0 :=
        (hΨspec z hz 0 (by norm_num)).2.fst
      simpa only [hΨ0 z hz] using hh
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (-2 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 2)] with t ht
    exact c.right_inv (hΨspec z hz t ht).1.1
  have hnear : ∀ᶠ v : E in 𝓝 0, (c p, v) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hW.mem_nhds hxW)
  obtain ⟨hend0, hendd⟩ := g.geodesic_endpoint_zero_and_hasFDerivAt p
    (fun v => Γ (c p, v))
    (hnear.mono fun v hv t ht => hgeodesic _ hv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (hnear.mono fun v hv => (hΓ0 _ hv).trans (c.left_inv (mem_extChartAt_source p)))
    (hnear.mono fun v hv => hΓv _ hv)
  let e : E × E → E := fun z => (Ψ (z, 1)).1
  have he : ContDiffOn ℝ ∞ e W := hΨ.fst.comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, by norm_num⟩)
  have heq : (fun v => e (c p, v)) =ᶠ[𝓝 0] fun v => c (Γ (c p, v) 1) := by
    filter_upwards [hnear] with v hv
    exact (c.right_inv (hΨspec _ hv 1 (by norm_num)).1.1).symm
  have he0 : e (c p, 0) = c p := by simpa only [hend0] using heq.self_of_nhds
  obtain ⟨G, _, hGW, hGt, hGmap, hGinv⟩ :=
    Poincare.AncientVolume.ScalarRatio.exists_smooth_local_endpoint_inverse hW hxW he he0
      (hendd.congr_of_eventuallyEq heq)
  refine ⟨W, Γ, G, hW, hxW, ?_, ?_, hGW, hGt, ?_, hGinv⟩
  · intro z hz
    exact ⟨(hVO hz).1.1, mem_univ _⟩
  · intro z hz
    exact ⟨hgeodesic z hz, hΓ0 z hz, hΓv z hz,
      fun t ht => (hΨspec z hz t ht).1.2⟩
  · intro z hz
    rw [hGmap]
    exact congrArg (fun y => (z.1, y))
      (c.right_inv (hΨspec z (hGW hz) 1 (by norm_num)).1.1).symm

end PoincareConjecture.RiemannianMetric
