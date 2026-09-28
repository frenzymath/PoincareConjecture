import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Levels.Capture
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Levels.GraphMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Levels.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.TransportComponentDiameter

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open Poincare.Riemannian.Soul Poincare.Geometry.Riemannian.SpaceForm
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem exists_remote_projective_neck_scale_lower_bound
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ (ε r : ℝ), 0 < ε → 0 < r → ε ≤ ε₀ → ∀ (Φ : RoundCylinderSpace → M),
        IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
          (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) →
        (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
          Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) →
        RoundCylinderClose ε 0 (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g Φ z v w) →
        ∀ q₀ : UnitTwoSphere, 2 ≤ busemannExhaustion p (Φ (q₀, 0)) →
          p ∉ Φ '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2)) → s₀ ≤ r := by
  let := g.toMetricSpace
  let f := busemannExhaustion p
  obtain ⟨d, hd, hlow⟩ :=
    g.exists_uniform_exhaustion_low_level_component_diameter D hc hsec p
  obtain ⟨l, hl, hsmooth⟩ := g.exists_smooth_projective_neck_level_transport D hc hsec p
  let W := (8 * (Real.pi + 1) + 6) / l
  have hW : 0 < W := by dsimp [W]; positivity
  have hWl : l * W = 8 * (Real.pi + 1) + 6 := by dsimp [W]; field_simp
  obtain ⟨ε₁, hε₁, hεquarter, htransport⟩ := hsmooth W hW.le
  let K := 4 * Real.pi * (1 + 8 / l)
  have hK : 0 < K := by dsimp [K]; positivity
  let s₀ := min (1 / (2 * (2 * W + 4 * (Real.pi + 1)))) (d / K)
  have hs₀ : 0 < s₀ := lt_min (by positivity) (div_pos hd hK)
  refine ⟨min ε₁ (1 / (W + 1)), lt_min hε₁ (by positivity), s₀, hs₀, ?_⟩
  intro ε r hε hr hεsmall Φ hΦ hfiber hclose q₀ hremote hpout
  have hεsmall₁ := hεsmall.trans (min_le_left _ _)
  have hεone : ε ≤ 1 := by linarith [hεsmall₁.trans hεquarter]
  have hWdom : W < ε⁻¹ := by
    have hh := (le_div_iff₀ (by positivity : 0 < W + 1)).mp
      (hεsmall.trans (min_le_right _ _))
    rw [← one_div]
    apply (lt_div_iff₀ hε).mpr
    nlinarith
  by_contra! hsmall
  have hscale : (2 * W + 4 * (Real.pi + 1)) * r ≤ 1 / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (2 * W + 4 * (Real.pi + 1)))).mp
      (hsmall.trans_le (min_le_left _ _))
    nlinarith
  have hKscale : K * r < d := by
    have hh := (lt_div_iff₀ hK).mp (hsmall.trans_le (min_le_right _ _))
    nlinarith
  obtain ⟨u, V, Q, hu, herror, hcpos, hcb, hreg, hband, hV, hAV, hVU,
      hQ, hmaps, honto, hinj, hQbound, hslab⟩ :=
    htransport ε r hε hr hεsmall₁ hWdom Φ hΦ hfiber hclose q₀ hremote hscale hpout
  let U := {x | 1 / 2 < f x ∧ f x < f (Φ (q₀, 0)) + 1 + 1 / 2}
  have hdom {t : ℝ} (ht : t ∈ Icc (-W) W) : t ∈ Ioo (-ε⁻¹) ε⁻¹ :=
    ⟨(neg_lt_neg hWdom).trans_le ht.1, ht.2.trans_lt hWdom⟩
  have hderiv (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (-W) W) :
      (l / 2) * r ≤ |deriv (fun a : ℝ => u (Φ (q, a))) t| := by
    rw [(hasDerivAt_cylinderCover_comp_axis Φ hΦ.contMDiffOn hu q (hdom ht)).deriv]
    exact (hslab q t ht).2.2
  have hU : Φ '' (univ ×ˢ Ioo (-W) W) ⊆ U := by
    rintro _ ⟨⟨q, t⟩, ht, rfl⟩
    exact (hslab q t ⟨ht.2.1.le, ht.2.2.le⟩).1
  have hcenter (q : UnitTwoSphere) :
      |u (Φ (q, 0)) - u (Φ (q₀, 0))| < ((l / 2) * r) * W := by
    let x := Φ (q, 0)
    let x₀ := Φ (q₀, 0)
    have hxU : x ∈ U := (hslab q 0 (by constructor <;> linarith)).1
    have hxC : x ∈ horoballIntersection p (f x₀ + 2) := by
      apply (busemannExhaustion_le_iff (by linarith : 0 ≤ f x₀ + 2)).mp
      linarith [hxU.2]
    have hx₀C : x₀ ∈ horoballIntersection p (f x₀ + 2) := by
      apply (busemannExhaustion_le_iff (by linarith : 0 ≤ f x₀ + 2)).mp
      linarith
    have hex := (herror x hxC (by linarith [hxU.1])).trans (min_le_left _ _)
    have hep := (herror x₀ hx₀C (by linarith)).trans (min_le_left _ _)
    have hdist : dist x x₀ ≤ (4 * (Real.pi + 1)) * r := by
      have hh := CylinderCover.toReal_edist_center_le g Φ hε hεone hr
        hΦ.contMDiffOn hclose q₀ (z := (q, 0)) (hdom (by constructor <;> linarith))
      simp only [abs_zero, mul_zero, zero_add] at hh
      exact hh
    have hosc₀ : |f x - f x₀| ≤ dist x x₀ := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (lipschitz_busemannExhaustion p).dist_le_mul x x₀
    have hosc := hosc₀.trans hdist
    have hb : |u x - u x₀| ≤ (4 * (Real.pi + 1) + 2) * r := by
      apply abs_le.mpr
      constructor <;> nlinarith [(abs_le.mp hex).1, (abs_le.mp hex).2,
        (abs_le.mp hep).1, (abs_le.mp hep).2, (abs_le.mp hosc).1, (abs_le.mp hosc).2]
    have hw : ((l / 2) * r) * W = (4 * (Real.pi + 1) + 3) * r := by
      nlinarith [congrArg (fun z : ℝ => z * r) hWl]
    exact hb.trans_lt (by rw [hw]; nlinarith)
  have hfiber' : ∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹,
      ∀ w ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2) :=
    fun z hz w hw => hfiber z ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
      w ⟨hw.1, hw.2.1.le, hw.2.2.le⟩
  obtain ⟨h, hh, hheight, _, hlevel, hP, hcomponent⟩ :=
    exists_projective_level_component_parametrization Φ hΦ hfiber' hu U hW hWdom
      (mul_pos (by positivity) hr) hU hderiv hcenter
  let P := fun q => Φ (q, h q)
  have hparam (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      g.tangentNorm (P q) (mfderiv (𝓡 2) (𝓡 3) P q v) ≤
        (2 * r * (1 + 8 / l)) * (roundSphereMetric 2).tangentNorm q v := by
    have hhbound := cylinderCover_levelGraph_tangentNorm_mfderiv_le g D Φ
      hε.le hεone hr hΦ.contMDiffOn hclose hu hh
      (fun q => hdom ⟨(hheight q).1.le, (hheight q).2.le⟩)
      (by positivity : 0 < l / 2) (by norm_num : (0 : ℝ) ≤ 2) hlevel
      (fun q => (hslab q _ ⟨(hheight q).1.le, (hheight q).2.le⟩).2.1)
      (fun q => (hslab q _ ⟨(hheight q).1.le, (hheight q).2.le⟩).2.2) q v
    have heq : 2 * (2 : ℝ) / (l / 2) = 8 / l := by ring
    simpa only [heq] using hhbound
  let A := {x | x ∈ U ∧ u x = u (Φ (q₀, 0))}
  have hA : IsCompact A := by
    have heq : A = {x | x ∈ U ∧ u x ∈ Icc 1 (u (Φ (q₀, 0)))} ∩
        u ⁻¹' {u (Φ (q₀, 0))} := by
      ext x
      simp only [A, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc]
      constructor
      · rintro ⟨hx, heq⟩
        exact ⟨⟨hx, heq ▸ hcpos.le, heq.le⟩, heq⟩
      · exact fun hx => ⟨hx.1.1, hx.2⟩
    rw [heq]
    exact hband.inter_right (isClosed_singleton.preimage hu.continuous)
  have hx : P q₀ ∈ A := ⟨hU ⟨(q₀, h q₀), ⟨mem_univ _, hheight q₀⟩, rfl⟩, hlevel q₀⟩
  have herror' (x : M) (hx : x ∈ horoballIntersection p (f (Φ (q₀, 0)) + 1 + 1))
      (hpos : 0 < f x) : |u x - f x| ≤ 1 / 8 := by
    apply (herror x ?_ hpos).trans (min_le_right _ _)
    simpa only [f, add_assoc, one_add_one_eq_two] using hx
  obtain ⟨y, hy, z, hz, hdiam⟩ := hlow (f (Φ (q₀, 0)) + 1) (by linarith) u hu hreg
    herror' (Q (P q₀)) (hmaps hx)
  have hupper := g.edist_transport_component_of_spherical_parametrization_le hu
    hA hV hAV hQ ⟨hmaps, hinj, honto⟩ hx hP (hcomponent q₀) hlevel
    (by norm_num : (0 : ℝ) < 2) (by positivity : 0 < 2 * r * (1 + 8 / l))
    (fun x hx v hv => hQbound x hx.1 hx.2 v hv) hparam hy hz
  have hupper' : dist y z ≤ K * r := by
    have ht := ENNReal.toReal_mono (by simp) hupper
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    change dist y z ≤ _ at ht
    convert ht using 1 <;> dsimp [K] <;> ring
  exact (not_lt_of_ge (hdiam.trans hupper')) hKscale

end PoincareConjecture.RiemannianMetric
