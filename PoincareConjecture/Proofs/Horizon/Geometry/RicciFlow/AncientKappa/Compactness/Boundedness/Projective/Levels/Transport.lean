import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ControlledTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.GapRate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.SlabDistance










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open Poincare.Riemannian.Soul
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem exists_smooth_projective_neck_level_transport
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    ∃ l : ℝ, 0 < l ∧ ∀ W : ℝ, 0 ≤ W →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧
        ∀ (ε r : ℝ), 0 < ε → 0 < r → ε ≤ ε₀ → W < ε⁻¹ →
        ∀ Φ : RoundCylinderSpace → M,
          IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
            (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) →
          (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
            Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) →
          RoundCylinderClose ε 0
            (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g Φ z v w) →
        ∀ q₀ : UnitTwoSphere, 2 ≤ f (Φ (q₀, 0)) →
          (2 * W + 4 * (Real.pi + 1)) * r ≤ 1 / 2 →
          p ∉ Φ '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2)) →
          let U := {x | 1 / 2 < f x ∧ f x < f (Φ (q₀, 0)) + 1 + 1 / 2}
          ∃ (u : M → ℝ) (V : Set M) (Q : M → M),
            ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u ∧
            (∀ x ∈ horoballIntersection p (f (Φ (q₀, 0)) + 2), 0 < f x →
              |u x - f x| ≤ min r (1 / 8)) ∧
            1 < u (Φ (q₀, 0)) ∧ u (Φ (q₀, 0)) < f (Φ (q₀, 0)) + 1 ∧
            (∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
            IsCompact {x | x ∈ U ∧ u x ∈ Icc 1 (u (Φ (q₀, 0)))} ∧
            IsOpen V ∧ {x | x ∈ U ∧ u x = u (Φ (q₀, 0))} ⊆ V ∧ V ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q V ∧
            MapsTo Q {x | x ∈ U ∧ u x = u (Φ (q₀, 0))} {x | x ∈ U ∧ u x = 1} ∧
            SurjOn Q {x | x ∈ U ∧ u x = u (Φ (q₀, 0))} {x | x ∈ U ∧ u x = 1} ∧
            InjOn Q {x | x ∈ U ∧ u x = u (Φ (q₀, 0))} ∧
            (∀ x ∈ U, u x = u (Φ (q₀, 0)) → ∀ v : TangentSpace (𝓡 3) x,
              mvfderiv (𝓡 3) u x v = 0 →
              g.tangentNorm (Q x) (mfderiv (𝓡 3) (𝓡 3) Q x v) ≤
                2 * g.tangentNorm x v) ∧
            ∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (-W) W →
              Φ (q, t) ∈ U ∧ g.tangentNorm (Φ (q, t)) (D.gradient u (Φ (q, t))) ≤ 2 ∧
              (l / 2) * r ≤ |mvfderiv (𝓡 3) u (Φ (q, t))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (q, t) (0, 1))| := by
  let := g.toMetricSpace
  let f := busemannExhaustion p
  obtain ⟨l, hl, hsmooth⟩ := g.exists_smooth_exhaustion_level_transport D hc hsec p
  refine ⟨l, hl, ?_⟩
  intro W hW
  obtain ⟨ε₀, hε₀, hεquarter, haxial⟩ :=
    CylinderCover.exists_axial_differential_lower_bound_of_gap_rate
      (G := 2) hl (by norm_num) hW
  refine ⟨ε₀, hε₀, hεquarter, ?_⟩
  intro ε r hε hr hεsmall hWdom Φ hΦ hfiber hclose q₀ hcenter hscale hpout
  let x₀ := Φ (q₀, 0)
  let C := horoballIntersection p (f x₀ + 2)
  let U := {x | 1 / 2 < f x ∧ f x < f x₀ + 1 + 1 / 2}
  obtain ⟨u, H, V, Q, _, hu, herror, hupper, hhess, hradial, hcpos, hcb,
    hregular, hcompact, hV, htopV, hVU, hQ, hmaps, honto, hinj, hbound⟩ :=
    hsmooth x₀ hcenter (min r (1 / 8)) (lt_min hr (by norm_num)) (min_le_right _ _)
  refine ⟨u, V, Q, hu, herror, hcpos, hcb, hregular, hcompact, hV, htopV, hVU,
    hQ, hmaps, honto, hinj, hbound, ?_⟩
  intro q t ht
  have hz : t ∈ Ioo (-ε⁻¹) ε⁻¹ :=
    ⟨(neg_lt_neg hWdom).trans_le ht.1, ht.2.trans_lt hWdom⟩
  have hd := CylinderCover.toReal_edist_center_le g Φ hε
    ((hεsmall.trans hεquarter).trans (by norm_num)) hr hΦ.contMDiffOn hclose q₀ (z := (q, t)) hz
  have hdhalf : dist (Φ (q, t)) x₀ ≤ 1 / 2 :=
    hd.trans ((mul_le_mul_of_nonneg_right (by linarith [(abs_le.mpr ht : |t| ≤ W)]) hr.le).trans hscale)
  have hosc0 : |f (Φ (q, t)) - f x₀| ≤ dist (Φ (q, t)) x₀ := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (lipschitz_busemannExhaustion p).dist_le_mul (Φ (q, t)) x₀
  have hosc := hosc0.trans hdhalf
  have hxone : 1 ≤ f (Φ (q, t)) := by linarith [(abs_le.mp hosc).1]
  have hxU : Φ (q, t) ∈ U := by
    constructor
    · linarith
    · linarith [(abs_le.mp hosc).2]
  have hxC : Φ (q, t) ∈ C :=
    (busemannExhaustion_le_iff (by linarith : 0 ≤ f x₀ + 2)).mp (by linarith [hxU.2])
  have hpC : p ∈ C := closedBall_subset_horoballIntersection p (f x₀ + 2)
    (by simp only [mem_closedBall, dist_self]; linarith)
  have hconvex (γ : ℝ → M) (L : ℝ) (hγ : g.IsGeodesicOn γ (Icc 0 L))
      (h0 : γ 0 ∈ C) (hL : γ L ∈ C) : MapsTo γ (Icc 0 L) C :=
    mapsTo_horoballIntersection_of_concaveOn
      (fun ray hray _ => g.concaveOn_busemann_of_nonnegativeSectional
        D hc hsec (fun _ _ => rfl) hray hγ) h0 hL
  have ha := haxial g D hc Φ hε hr hεsmall hΦ hfiber hclose hu hpC hconvex hhess hpout
    (z := (q, t)) hz (abs_le.mpr ht) hxC (hradial _ hxC hxone).1
    (hradial _ hxC hxone).2 (hupper _ hxC)
  refine ⟨hxU, hupper _ hxC, ?_⟩
  rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hr)] at ha
  have hmul := mul_le_mul_of_nonneg_right ha hr.le
  simpa only [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one, mul_left_comm r⁻¹] using hmul

end PoincareConjecture.RiemannianMetric
