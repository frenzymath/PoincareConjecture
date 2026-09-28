import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ray
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.BusemannGradient












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal
open Poincare.Riemannian.Soul

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}



theorem exists_long_outward_calibrated_segment (N : EpsilonNeck g)
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray)
    (hε : N.epsilon ≤ 1 / 4)
    (hN : N.epsilon ≤ 1 / (4 * neckDepthConstant * (2 * Real.pi + 2)))
    {A B : Set M} (hA : IsOpen A) (hfront : frontier A = N.central_sphere)
    (hAc : IsCompact (closure A))
    (hhalf :
      (N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
      (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A))
    {x : M} (hx : x ∈ N.carrier) (haxisx : |(N.coordinate_inverse x).2| ≤ 1)
    (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (busemann ray) x) :
    ∃ (L : ℝ) (γ : ℝ → M) (σ : ℝ),
      0 < L ∧ N.scale / (100 * N.epsilon) < L ∧ |σ| = 1 ∧ γ 0 = x ∧
      g.IsGeodesicOn γ (Icc 0 L) ∧ MapsTo γ (Icc 0 L) N.carrier ∧
      (∀ t ∈ Icc 0 L,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
        ENNReal.ofReal (t - s) ≤ intrinsicEDist g N.carrier (γ s) (γ t)) ∧
      (∀ t ∈ Icc 0 L, busemann ray (γ t) = busemann ray x - t) ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1 = -D.gradient (busemann ray) (γ 0) ∧
      γ L ∉ A ∧
      (N.coordinate_inverse (γ L)).2 = σ / (2 * N.epsilon) ∧
      ((N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B ∧ σ = 1) ∨
        (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A ∧ σ = -1)) ∧
      σ * (N.coordinate_inverse (γ 0)).2 < σ * (N.coordinate_inverse (γ L)).2 := by
  have hi : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have ha : -N.epsilon⁻¹ < -N.epsilon⁻¹ / 2 := by linarith
  have hb : N.epsilon⁻¹ / 2 < N.epsilon⁻¹ := by linarith
  let K := closure A ∪ N.coordinate_map ''
    (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))
  have hK : IsCompact K := hAc.union (N.isCompact_coordinate_slab ha hb)
  obtain ⟨T, γ, hT, _, hγ0, hout, hγ, hspeed, hmin, hcal, hinit⟩ :=
    g.exists_ray_busemann_calibrated_segment_outside_compact D hc hdist hray hf hK 0
  have hstart : γ 0 ∈ N.carrier := hγ0.symm ▸ hx
  have haxis0 : |(N.coordinate_inverse (γ 0)).2| ≤ 1 := hγ0.symm ▸ haxisx
  obtain ⟨L, hL, hlong, hcarrier, haxisL, _⟩ :=
    N.exists_long_initial_segment_to_half_neck hT.le hε hγ hspeed hstart haxis0
      (fun h => hout (Or.inr h))
  have hsub : Icc 0 L ⊆ Icc 0 T := fun _ ht => ⟨ht.1, ht.2.trans hL.2⟩
  have hmetric : IsMinimizingOn γ (Icc 0 T) := by
    intro s hs t ht
    rw [hdist, hmin s hs t ht, ENNReal.toReal_ofReal (abs_nonneg _)]
  obtain ⟨σ, hσ, haxis⟩ : ∃ σ : ℝ, |σ| = 1 ∧
      (N.coordinate_inverse (γ L)).2 = σ / (2 * N.epsilon) := by
    rcases (abs_eq (show 0 ≤ N.epsilon⁻¹ / 2 by positivity)).mp haxisL with hp | hn
    · refine ⟨1, by norm_num, ?_⟩
      rw [hp]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    · refine ⟨-1, by norm_num, ?_⟩
      rw [hn]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  have hsign := N.minimizing_half_neck_outward_sign hdist hN hA hfront hhalf hmetric
    (fun h => hout (Or.inl (subset_closure h))) hstart haxis0
    ⟨hL.1.le, hL.2⟩ (hcarrier ⟨hL.1.le, le_rfl⟩) hσ haxis
  have hend := N.minimizing_half_neck_not_mem_compact_side hdist hN hA hfront hmetric
    (fun h => hout (Or.inl (subset_closure h))) hstart haxis0
    ⟨hL.1.le, hL.2⟩ (hcarrier ⟨hL.1.le, le_rfl⟩) hσ haxis
  refine ⟨L, γ, σ, hL.1, hlong, hσ, hγ0, (fun t ht => hγ t (hsub ht)),
    hcarrier, (fun t ht => hspeed t (hsub ht)),
    (fun s hs t ht => hmin s (hsub hs) t (hsub ht)), ?_,
    (fun t ht => hcal t (hsub ht)), hinit, hend, haxis, hsign, ?_⟩
  · intro s hs t ht hst
    have hdistst : g.edist (γ s) (γ t) = ENNReal.ofReal (t - s) := by
      rw [hmin s (hsub hs) t (hsub ht), abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    rw [← hdistst]
    apply le_sInf
    rintro l ⟨η, hη, hη0, hη1, _, rfl⟩
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hη hη0 hη1 zero_le_one
  · have hi4 : 4 ≤ N.epsilon⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ N.epsilon_pos).mpr (by linarith)
    rcases hsign with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · have heq : (1 : ℝ) / (2 * N.epsilon) = N.epsilon⁻¹ / 2 := by
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      rw [haxis, heq]
      nlinarith [(abs_le.mp haxis0).2]
    · have heq : (-1 : ℝ) / (2 * N.epsilon) = -(N.epsilon⁻¹ / 2) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [haxis, heq]
      nlinarith [(abs_le.mp haxis0).1]

end PoincareConjecture.EpsilonNeck
