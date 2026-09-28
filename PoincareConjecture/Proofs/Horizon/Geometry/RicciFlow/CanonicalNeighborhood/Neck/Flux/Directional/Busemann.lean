import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Directional.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Calibrated
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Directional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle
open Poincare.Riemannian.Soul

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_outward_busemann_gradient_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [MetricSpace M] [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}
        (N : EpsilonNeck g) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ x y : M, dist x y = (g.edist x y).toReal) →
        ∀ {ray : ℝ → M}, IsRay ray → N.epsilon ≤ ε₀ →
        ∀ {A B : Set M}, IsOpen A → frontier A = N.central_sphere →
        IsCompact (closure A) →
        ((N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
          (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A)) →
        ∀ {σ : ℝ},
        ((σ = -1 ∧ N.region (-N.epsilon⁻¹) 0 ⊆ A) ∨
          (σ = 1 ∧ N.region 0 N.epsilon⁻¹ ⊆ A)) →
        ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
          (N.coordinate_inverse x).2 ∈ Ioo (-1) 1 →
          ∃ a : TangentSpace (𝓡 3) x,
            g.tangentNorm x (σ • D.gradient (busemann ray) x - a) ≤ 1 / 4 ∧
            mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x a = N.scale⁻¹ := by
  obtain ⟨εa, hεa, halign⟩ := long_neck_geodesics_are_almost_axial_signed.{u}
    (show (0 : ℝ) < 1 / 4 by norm_num)
  let ε₀ := min εa (min (1 / 4) (1 / (4 * neckDepthConstant * (2 * Real.pi + 2))))
  have hε₀ : 0 < ε₀ := lt_min hεa (lt_min (by norm_num)
    (by have := neckDepthConstant_pos; positivity))
  refine ⟨ε₀, hε₀, ?_⟩
  intro M _ _ _ _ _ _ g N D hc hdist ray hray hN A B hA hfront hAc hhalf σ hkind
  have hNa : N.epsilon ≤ εa := hN.trans (min_le_left _ _)
  have hNq : N.epsilon ≤ 1 / 4 :=
    hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNs : N.epsilon ≤ 1 / (4 * neckDepthConstant * (2 * Real.pi + 2)) :=
    hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLip (p q : M) : |busemann ray p - busemann ray q| ≤ (g.edist p q).toReal := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hdist] using
      (lipschitz_busemann hray).dist_le_mul p q
  filter_upwards [ae_restrict_of_ae (g.ae_mDifferentiableAt_of_distance_lipschitz hLip),
    ae_restrict_mem N.carrier_open.measurableSet] with x hf hx
  intro haxisx
  obtain ⟨L, γ, τ, hL, hlong, hτ, hγ0, hgeo, hcarrier, hspeed, _, hsegment,
      _, hinit, hend, haxis, _, horient⟩ :=
    N.exists_long_outward_calibrated_segment D hc hdist hray hNq hNs hA hfront hAc
      hhalf hx (abs_le.mpr ⟨haxisx.1.le, haxisx.2.le⟩) hf
  subst x
  have hε := N.epsilon_pos
  have hτsign : τ = 1 ∨ τ = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hτ
  have hcoord := (N.coordinate_inverse_mem _ (hcarrier ⟨hL.le, le_rfl⟩)).2
  have hτσ : τ = -σ := by
    rcases hkind with ⟨rfl, hneg⟩ | ⟨rfl, hpos⟩
    · rcases hτsign with rfl | rfl
      · norm_num
      · exfalso
        apply hend (hneg ⟨hcarrier ⟨hL.le, le_rfl⟩, hcoord.1, ?_⟩)
        rw [haxis]
        exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
    · rcases hτsign with rfl | rfl
      · exfalso
        apply hend (hpos ⟨hcarrier ⟨hL.le, le_rfl⟩, ?_, hcoord.2⟩)
        rw [haxis]
        positivity
      · norm_num
  have hax := halign N hNa hlong hgeo (fun t ht => hcarrier ht) hspeed hsegment
    hτ horient 0 ⟨le_rfl, hL.le⟩
  rw [hinit, hτσ] at hax
  simp only [neg_smul, smul_neg, neg_neg] at hax
  let a : TangentSpace (𝓡 3) (γ 0) := N.scale⁻¹ •
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map
      (N.coordinate_inverse (γ 0)) (0, 1)
  refine ⟨a, ?_, ?_⟩
  · exact hax.le
  · have hd := N.axial_mvfderiv_coordinate_tangent (N.coordinate_inverse_mem (γ 0) hx) (0, 1)
    rw [N.coordinate_map_coordinate_inverse hx] at hd
    change mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) (γ 0)
      (N.scale⁻¹ • _) = N.scale⁻¹
    rw [map_smul, smul_eq_mul]
    exact (congrArg (fun t : ℝ => N.scale⁻¹ * t) hd).trans (mul_one _)

end PoincareConjecture.EpsilonNeck
