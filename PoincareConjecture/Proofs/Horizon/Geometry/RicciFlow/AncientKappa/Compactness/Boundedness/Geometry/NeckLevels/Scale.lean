import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.AmbientCapture
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.GraphMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.NeckTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.TransportComponentDiameter











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function TopologicalSpace
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Riemannian.SpaceForm

variable {M : Type*} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩



theorem exists_remote_neck_scale_lower_bound
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ N : EpsilonNeck g, N.epsilon ≤ ε₀ →
        2 ≤ busemannExhaustion p N.center →
        p ∉ N.coordinate_map ''
          (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) →
        s₀ ≤ N.scale := by
  letI := g.toMetricSpace
  let f := busemannExhaustion p
  obtain ⟨d, hd, hlow⟩ :=
    g.exists_uniform_exhaustion_low_level_component_diameter D hc hsec p
  obtain ⟨l, hl, hsmooth⟩ := g.exists_smooth_neck_level_transport D hc hsec p
  let W := (4 * Real.pi + 6) / l
  have hW : 0 < W := by dsimp [W]; positivity
  have hWl : l * W = 4 * Real.pi + 6 := by dsimp [W]; field_simp
  obtain ⟨ε₁, hε₁, _, htransport⟩ := hsmooth W hW.le
  let K := 4 * Real.pi * (1 + 8 / l)
  have hK : 0 < K := by dsimp [K]; positivity
  let s₀ := min (1 / (2 * (2 * Real.pi + 2 * W))) (d / K)
  have hs₀ : 0 < s₀ := lt_min (by positivity) (div_pos hd hK)
  refine ⟨min ε₁ (1 / (W + 1)), lt_min hε₁ (by positivity), s₀, hs₀, ?_⟩
  intro N hN hremote hpout
  have hscale_pos := N.scale_pos
  by_contra! hsmall
  have hsmall₁ := hsmall.trans_le (min_le_left _ _)
  have hsmall₂ := hsmall.trans_le (min_le_right _ _)
  have hscale : (2 * Real.pi + 2 * W) * N.scale ≤ 1 / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (2 * Real.pi + 2 * W))).mp hsmall₁
    nlinarith
  have hKscale : K * N.scale < d := by
    have hh := (lt_div_iff₀ hK).mp hsmall₂
    nlinarith
  have hWdom : W < N.epsilon⁻¹ := by
    have hh := hN.trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < W + 1)).mp hh
    rw [← one_div]
    apply (lt_div_iff₀ N.epsilon_pos).mpr
    nlinarith [N.epsilon_pos]
  obtain ⟨u, V, Q, hu, herror, hcpos, hcb, hreg, hband, hV, hAV, hVU,
      hQ, hmaps, honto, hinj, hQbound, hslab⟩ :=
    htransport N (hN.trans (min_le_left _ _)) hremote hscale hpout
  let U : Opens M := ⟨{x | 1 / 2 < f x ∧ f x < f N.center + 1 + 1 / 2},
    (isOpen_lt continuous_const (lipschitz_busemannExhaustion p).continuous).inter
      (isOpen_lt (lipschitz_busemannExhaustion p).continuous continuous_const)⟩
  have hdom {t : ℝ} (ht : t ∈ Icc (-W) W) :
      t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨(neg_lt_neg hWdom).trans_le ht.1, ht.2.trans_lt hWdom⟩
  have hcoord (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Icc (-W) W) :
      (q, t) ∈ N.cylinderDomain := ⟨mem_univ _, hdom ht⟩
  have hlocal (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Icc (-W) W) :=
    hslab (N.coordinate_map (q, t))
      (N.coordinate_map_mem (hcoord q ht)) (by
        rw [N.coordinate_inverse_coordinate_map (hcoord q ht)]
        exact abs_le.mpr ht)
  have hraw (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Icc (-W) W) :
      (l / 2) * N.scale ≤ |mvfderiv (𝓡 3) u (N.coordinate_map (q, t))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, t) (0, 1))| := by
    have hh := (hlocal q ht).2.2
    rw [N.coordinate_inverse_coordinate_map (hcoord q ht), map_smul, smul_eq_mul,
      abs_mul, abs_of_pos (inv_pos.mpr N.scale_pos)] at hh
    have hmul := mul_le_mul_of_nonneg_right hh N.scale_pos.le
    simpa only [mul_assoc, inv_mul_cancel₀ N.scale_pos.ne', mul_one,
      mul_left_comm N.scale⁻¹] using hmul
  have hderiv (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (-W) W) :
      (l / 2) * N.scale ≤ |deriv (fun s : ℝ => u (N.coordinate_map (q, s))) t| := by
    rw [(N.hasDerivAt_comp_axis hu q (hdom ht)).deriv]
    exact hraw q ht
  have hU : N.region (-W) W ⊆ U := by
    intro x hx
    exact (hslab x hx.1 (abs_le.mpr ⟨hx.2.1.le, hx.2.2.le⟩)).1
  have hcenter (q : UnitTwoSphere) :
      |u (N.coordinate_map (q, 0)) - u N.center| < ((l / 2) * N.scale) * W := by
    let x := N.coordinate_map (q, 0)
    have hxU : x ∈ U := (hlocal q (show (0 : ℝ) ∈ Icc (-W) W by constructor <;> linarith)).1
    have hxC : x ∈ horoballIntersection p (f N.center + 2) := by
      apply (busemannExhaustion_le_iff (by linarith : 0 ≤ f N.center + 2)).mp
      linarith [hxU.2]
    have hpC : N.center ∈ horoballIntersection p (f N.center + 2) := by
      apply (busemannExhaustion_le_iff (by linarith : 0 ≤ f N.center + 2)).mp
      linarith
    have hex := (herror x hxC (by linarith [hxU.1])).trans (min_le_left _ _)
    have hep := (herror N.center hpC (by linarith)).trans (min_le_left _ _)
    have hxc : x ∈ N.central_sphere := by
      rw [← N.centralSphere_range]
      exact mem_range_self q
    have hdist : dist x N.center ≤ (2 * Real.pi) * N.scale := by
      have hh := ENNReal.toReal_mono (by simp)
        (N.edist_central_sphere_le_two_pi_mul_scale hxc N.center_on_central_sphere)
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi) * N.scale)] at hh
      exact hh
    have hosc₀ : |f x - f N.center| ≤ dist x N.center := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (lipschitz_busemannExhaustion p).dist_le_mul x N.center
    have hosc : |f x - f N.center| ≤ (2 * Real.pi) * N.scale := hosc₀.trans hdist
    have hb : |u x - u N.center| ≤ (2 * Real.pi + 2) * N.scale := by
      apply abs_le.mpr
      constructor <;> nlinarith [(abs_le.mp hex).1, (abs_le.mp hex).2,
        (abs_le.mp hep).1, (abs_le.mp hep).2, (abs_le.mp hosc).1, (abs_le.mp hosc).2]
    have hw : ((l / 2) * N.scale) * W = (2 * Real.pi + 3) * N.scale := by
      nlinarith [congrArg (fun z : ℝ => z * N.scale) hWl]
    exact hb.trans_lt (by rw [hw]; nlinarith [N.scale_pos])
  letI := openLevelSetChartedSpace hu U hreg 2 (u N.center)
  letI := isManifold_openLevelSet hu U hreg 2 (u N.center)
  obtain ⟨h, F, hh, hheight, hinc, hF, _, hcomponent⟩ :=
    N.exists_regularLevel_component_parametrization hu U hreg hW hWdom
      (mul_pos (by positivity) N.scale_pos) hU hderiv hcenter
  let P := openLevelIncl u U (u N.center) ∘ F
  have hPeq : P = fun q => N.coordinate_map (q, h q) := funext hinc
  have hP : ContMDiff (𝓡 2) (𝓡 3) ∞ P :=
    (contMDiff_openLevelIncl hu U hreg 2 (u N.center)).comp hF
  have hlevel (q : UnitTwoSphere) : u (P q) = u N.center := (F q).2
  have hgraphlevel (q : UnitTwoSphere) : u (N.coordinate_map (q, h q)) = u N.center := by
    rw [← hinc q]
    exact hlevel q
  have hparam (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      g.tangentNorm (P q) (mfderiv (𝓡 2) (𝓡 3) P q v) ≤
        (2 * N.scale * (1 + 8 / l)) * (roundSphereMetric 2).tangentNorm q v := by
    rw [hPeq]
    have hhbound := N.levelGraph_tangentNorm_mfderiv_le D hu hh
      (fun q => hdom ⟨(hheight q).1.le, (hheight q).2.le⟩)
      (by positivity : 0 < l / 2) (by norm_num : (0 : ℝ) ≤ 2) hgraphlevel
      (fun q => (hlocal q ⟨(hheight q).1.le, (hheight q).2.le⟩).2.1)
      (fun q => hraw q ⟨(hheight q).1.le, (hheight q).2.le⟩) q v
    have heq : 2 * (2 : ℝ) / (l / 2) = 8 / l := by ring
    simpa only [heq] using hhbound
  let A := {x | x ∈ U ∧ u x = u N.center}
  let B := {x | x ∈ U ∧ u x = 1}
  have hA : IsCompact A := by
    have heq : A = {x | x ∈ U ∧ u x ∈ Icc 1 (u N.center)} ∩ u ⁻¹' {u N.center} := by
      ext x
      simp only [A, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc]
      constructor
      · rintro ⟨hx, heq⟩
        exact ⟨⟨hx, heq ▸ hcpos.le, heq.le⟩, heq⟩
      · exact fun hx => ⟨hx.1.1, hx.2⟩
    rw [heq]
    exact hband.inter_right (isClosed_singleton.preimage hu.continuous)
  let q₀ := (N.coordinate_inverse N.center).1
  have hx : P q₀ ∈ A := ⟨(F q₀).1.2, (F q₀).2⟩
  have himage : range P = connectedComponentIn A (P q₀) :=
    range_comp_openLevelIncl_eq_connectedComponentIn u U (u N.center) F q₀ (hcomponent q₀)
  have herror' (x : M) (hx : x ∈ horoballIntersection p (f N.center + 1 + 1))
      (hpos : 0 < f x) : |u x - f x| ≤ 1 / 8 := by
    apply (herror x ?_ hpos).trans (min_le_right _ _)
    simpa only [f, add_assoc, one_add_one_eq_two] using hx
  obtain ⟨y, hy, z, hz, hdiam⟩ := hlow (f N.center + 1) (by linarith) u hu hreg
    herror' (Q (P q₀)) (hmaps hx)
  have hupper := g.edist_transport_component_of_spherical_parametrization_le hu
    hA hV hAV hQ ⟨hmaps, hinj, honto⟩ hx hP himage hlevel
    (by norm_num : (0 : ℝ) < 2)
    (mul_pos (mul_pos (by norm_num) N.scale_pos) (by positivity))
    (fun x hx v hv => hQbound x hx.1 hx.2 v hv) hparam hy hz
  have hupper' : dist y z ≤ K * N.scale := by
    have ht := ENNReal.toReal_mono (by simp) hupper
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    change dist y z ≤ _ at ht
    convert ht using 1 <;> dsimp [K] <;> ring
  exact (not_lt_of_ge (hdiam.trans hupper')) hKscale

end PoincareConjecture.RiemannianMetric
