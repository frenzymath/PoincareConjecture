import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ControlledTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.LevelTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul
open Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow

variable {M : Type*} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem exists_smooth_neck_level_transport
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    ∃ l : ℝ, 0 < l ∧ ∀ W : ℝ, 0 ≤ W →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧
        ∀ N : EpsilonNeck g, N.epsilon ≤ ε₀ → 2 ≤ f N.center →
          (2 * Real.pi + 2 * W) * N.scale ≤ 1 / 2 →
          p ∉ N.coordinate_map ''
            (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) →
          let U := {x | 1 / 2 < f x ∧ f x < f N.center + 1 + 1 / 2}
          ∃ (u : M → ℝ) (V : Set M) (Q : M → M),
            ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u ∧
            (∀ x ∈ horoballIntersection p (f N.center + 2), 0 < f x →
              |u x - f x| ≤ min N.scale (1 / 8)) ∧
            1 < u N.center ∧ u N.center < f N.center + 1 ∧
            (∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
            IsCompact {x | x ∈ U ∧ u x ∈ Icc 1 (u N.center)} ∧
            IsOpen V ∧ {x | x ∈ U ∧ u x = u N.center} ⊆ V ∧ V ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q V ∧
            MapsTo Q {x | x ∈ U ∧ u x = u N.center} {x | x ∈ U ∧ u x = 1} ∧
            SurjOn Q {x | x ∈ U ∧ u x = u N.center} {x | x ∈ U ∧ u x = 1} ∧
            InjOn Q {x | x ∈ U ∧ u x = u N.center} ∧
            (∀ x ∈ U, u x = u N.center → ∀ v : TangentSpace (𝓡 3) x,
              mvfderiv (𝓡 3) u x v = 0 →
              g.tangentNorm (Q x) (mfderiv (𝓡 3) (𝓡 3) Q x v) ≤
                2 * g.tangentNorm x v) ∧
            ∀ x ∈ N.carrier, |(N.coordinate_inverse x).2| ≤ W →
              x ∈ U ∧ g.tangentNorm x (D.gradient u x) ≤ 2 ∧
              l / 2 ≤ |mvfderiv (𝓡 3) u x (N.scale⁻¹ •
                mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
                  N.coordinate_map (N.coordinate_inverse x) (0, 1))| := by
  let := g.toMetricSpace
  let f := busemannExhaustion p
  obtain ⟨l, hl, hsmooth⟩ :=
    g.exists_smooth_exhaustion_level_transport D hc hsec p
  refine ⟨l, hl, ?_⟩
  intro W hW
  obtain ⟨ε₀, hε₀, hεquarter, haxial⟩ :=
    EpsilonNeck.exists_axial_differential_lower_bound_of_gap_rate
      (G := 2) hl (by norm_num) hW
  refine ⟨ε₀, hε₀, hεquarter, ?_⟩
  intro N hN hcenter hscale hpout
  let C := horoballIntersection p (f N.center + 2)
  let U := {x | 1 / 2 < f x ∧ f x < f N.center + 1 + 1 / 2}
  let e := min N.scale (1 / 8)
  have he : 0 < e := lt_min N.scale_pos (by norm_num)
  have heighth : e ≤ 1 / 8 := min_le_right _ _
  obtain ⟨u, H, V, Q, _, hu, herror, hupper, hhess, hradial, hcpos, hcb,
    hregular, hcompact, hV, htopV, hVU, hQ, hmaps, honto, hinj, hbound⟩ :=
    hsmooth N.center hcenter e he heighth
  have hUC : U ⊆ C := by
    intro x hx
    apply (busemannExhaustion_le_iff (by linarith : 0 ≤ f N.center + 2)).mp
    change f x ≤ f N.center + 2
    linarith [hx.2]
  refine ⟨u, V, Q, hu, herror, hcpos, hcb, hregular, hcompact, hV, htopV, hVU,
    hQ, hmaps, honto, hinj, hbound, ?_⟩
  intro x hx haxis
  have hd := N.toReal_edist_central_sphere_le_of_mem_carrier hx N.center_on_central_sphere
  have hdhalf : dist x N.center ≤ 1 / 2 :=
    hd.trans ((mul_le_mul_of_nonneg_right (by linarith) N.scale_pos.le).trans hscale)
  have hosc0 : |f x - f N.center| ≤ dist x N.center := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (lipschitz_busemannExhaustion p).dist_le_mul x N.center
  have hosc : |f x - f N.center| ≤ 1 / 2 := hosc0.trans hdhalf
  have hxone : 1 ≤ f x := by linarith [(abs_le.mp hosc).1]
  have hxU : x ∈ U := by
    constructor
    · linarith
    · linarith [(abs_le.mp hosc).2]
  have hxC := hUC hxU
  have hpC : p ∈ C := closedBall_subset_horoballIntersection p (f N.center + 2)
    (by simp only [mem_closedBall, dist_self]; linarith)
  have hconvex (γ : ℝ → M) (L : ℝ) (hγ : g.IsGeodesicOn γ (Icc 0 L))
      (h0 : γ 0 ∈ C) (hL : γ L ∈ C) : MapsTo γ (Icc 0 L) C :=
    mapsTo_horoballIntersection_of_concaveOn
      (fun ray hray _ => g.concaveOn_busemann_of_nonnegativeSectional
        D hc hsec (fun _ _ => rfl) hray hγ) h0 hL
  exact ⟨hxU, hupper x hxC, haxial D hc N hN hu hpC hconvex hhess hpout
    hx haxis hxC (hradial x hxC hxone).1 (hradial x hxC hxone).2 (hupper x hxC)⟩

end PoincareConjecture.RiemannianMetric
