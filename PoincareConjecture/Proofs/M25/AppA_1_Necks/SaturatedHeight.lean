import PoincareConjecture.Proofs.M25.Mathlib.SmoothClippedIdentity
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparatingComponents
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import Mathlib.Topology.EMetricSpace.Lipschitz











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}





theorem exists_saturatedAxialHeight (N : EpsilonNeck g)
    (hsep : N.IsSeparating) (a b : M)
    (ha : a ∈ N.region (-N.epsilon⁻¹) 0)
    (hb : b ∈ N.region 0 N.epsilon⁻¹) :
    ∃ H : M → ℝ,
      Continuous H ∧
      (∀ x ∈ N.carrier, H x = (N.coordinate_inverse x).2) ∧
      (∀ x ∈ connectedComponentIn N.central_sphereᶜ a \ N.carrier,
        H x = -N.epsilon⁻¹) ∧
      (∀ x ∈ connectedComponentIn N.central_sphereᶜ b \ N.carrier,
        H x = N.epsilon⁻¹) ∧
      (∀ x, x ∉ connectedComponent N.center → H x = 0) ∧
      (∀ x y : M,
        ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
          |H x - H y|) ≤ g.edist x y) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let A := connectedComponentIn N.central_sphereᶜ a
  let B := connectedComponentIn N.central_sphereᶜ b
  obtain ⟨a₀, b₀, _, _, hn, hp, hne, _, _, hcover⟩ :=
    N.exists_opposite_central_components hsep
  have heA := connectedComponentIn_eq (hn ha)
  have heB := connectedComponentIn_eq (hp hb)
  simp only [heA, heB] at hn hp hne hcover
  change N.region (-N.epsilon⁻¹) 0 ⊆ A at hn
  change N.region 0 N.epsilon⁻¹ ⊆ B at hp
  change A ≠ B at hne
  change A ∪ N.central_sphere ∪ B = connectedComponent N.center at hcover
  have hAB {x : M} (hxA : x ∈ A) (hxB : x ∈ B) : False :=
    hne ((connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxB).symm)
  have hAS : A ⊆ N.central_sphereᶜ := connectedComponentIn_subset _ _
  have hBS : B ⊆ N.central_sphereᶜ := connectedComponentIn_subset _ _
  have hAK : A ⊆ connectedComponent N.center := by
    intro x hx
    exact hcover ▸ Or.inl (Or.inl hx)
  have hBK : B ⊆ connectedComponent N.center := by
    intro x hx
    exact hcover ▸ Or.inr hx
  have hAopen : IsOpen A := N.isClosed_central_sphere.isOpen_compl.connectedComponentIn
  have hBopen : IsOpen B := N.isClosed_central_sphere.isOpen_compl.connectedComponentIn
  have hnegative {x : M} (hx : x ∈ N.carrier) (hxA : x ∈ A) :
      (N.coordinate_inverse x).2 < 0 := by
    rcases lt_trichotomy (N.coordinate_inverse x).2 0 with h | h | h
    · exact h
    · exact False.elim (hAS hxA ((N.mem_central_sphere_iff x).mpr ⟨hx, h⟩))
    · exact False.elim (hAB hxA (hp ⟨hx, h, (N.coordinate_inverse_mem x hx).2.2⟩))
  have hpositive {x : M} (hx : x ∈ N.carrier) (hxB : x ∈ B) :
      0 < (N.coordinate_inverse x).2 := by
    rcases lt_trichotomy (N.coordinate_inverse x).2 0 with h | h | h
    · exact False.elim (hAB (hn ⟨hx, (N.coordinate_inverse_mem x hx).2.1, h⟩) hxB)
    · exact False.elim (hBS hxB ((N.mem_central_sphere_iff x).mpr ⟨hx, h⟩))
    · exact h
  let H : M → ℝ := fun x => if x ∈ N.carrier then (N.coordinate_inverse x).2
    else if x ∈ A then -N.epsilon⁻¹ else if x ∈ B then N.epsilon⁻¹ else 0
  have hHout {x : M} (hx : x ∉ connectedComponent N.center) : H x = 0 := by
    simp only [H, if_neg (fun hc => hx (N.m25_carrier_subset_connectedComponent hc)),
      if_neg (fun h => hx (hAK h)), if_neg (fun h => hx (hBK h))]
  let c := N.scale * Real.sqrt (1 - N.epsilon)
  have hc : 0 < c :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have happrox (δ : ℝ) (hδ : 0 < δ) :
      ∃ G : M → ℝ, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ G ∧
        (∀ x, |G x - H x| < δ) ∧
        (∀ x v, |mvfderiv (𝓡 3) G x v| ≤ (1 / c) * g.tangentNorm x v) := by
    obtain ⟨p, q, χ, hpL, hp0, hq0, hqL, hχ, hleft, hright, hderiv, hclose⟩ :=
      Real.exists_smooth_clipped_identity hL hδ
    let G : M → ℝ := fun x => if x ∈ N.carrier then χ (N.coordinate_inverse x).2
      else if x ∈ A then χ (-N.epsilon⁻¹) else if x ∈ B then χ N.epsilon⁻¹ else 0
    have hGout {x : M} (hx : x ∉ connectedComponent N.center) : G x = 0 := by
      simp only [G, if_neg (fun hc => hx (N.m25_carrier_subset_connectedComponent hc)),
        if_neg (fun h => hx (hAK h)), if_neg (fun h => hx (hBK h))]
    have hGapprox (x : M) : |G x - H x| < δ := by
      by_cases hx : x ∈ N.carrier
      · simpa only [G, H, if_pos hx] using
          hclose (N.coordinate_inverse x).2 (Ioo_subset_Icc_self (N.coordinate_inverse_mem x hx).2)
      · by_cases hxA : x ∈ A
        · simpa only [G, H, if_neg hx, if_pos hxA] using
            hclose (-N.epsilon⁻¹) ⟨le_rfl, by linarith⟩
        · by_cases hxB : x ∈ B
          · simpa only [G, H, if_neg hx, if_neg hxA, if_pos hxB] using
              hclose N.epsilon⁻¹ ⟨by linarith, le_rfl⟩
          · simpa only [G, H, if_neg hx, if_neg hxA, if_neg hxB, sub_self, abs_zero] using hδ
    let C := N.coordinate_map '' (univ ×ˢ Icc p q)
    have hC : IsCompact C := N.isCompact_coordinate_slab hpL hqL
    have hCU : C ⊆ N.carrier := by
      rintro x ⟨z, hz, rfl⟩
      exact N.coordinate_map_mem ⟨mem_univ _, hpL.trans_le hz.2.1, hz.2.2.trans_lt hqL⟩
    have hmemC {x : M} (hx : x ∈ N.carrier)
        (hs : (N.coordinate_inverse x).2 ∈ Icc p q) : x ∈ C :=
      ⟨N.coordinate_inverse x, ⟨mem_univ _, hs⟩, N.coordinate_map_inverse hx⟩
    have hGin {x : M} (hx : x ∈ N.carrier) :
        G =ᶠ[𝓝 x] fun y => χ (N.coordinate_inverse y).2 := by
      filter_upwards [N.carrier_open.mem_nhds hx] with y hy
      simp only [G, if_pos hy]
    have hGconstant {x : M} (hx : x ∉ N.carrier) :
        ∃ r : ℝ, G =ᶠ[𝓝 x] fun _ => r := by
      have hxC : x ∉ C := fun h => hx (hCU h)
      by_cases hxA : x ∈ A
      · refine ⟨χ (-N.epsilon⁻¹), ?_⟩
        filter_upwards [hAopen.mem_nhds hxA, hC.isClosed.isOpen_compl.mem_nhds hxC]
          with y hyA hyC
        by_cases hy : y ∈ N.carrier
        · have hlow : (N.coordinate_inverse y).2 ≤ p := by
            by_contra h
            exact hyC (hmemC hy ⟨(lt_of_not_ge h).le,
              (hnegative hy hyA).le.trans hq0.le⟩)
          simpa only [G, if_pos hy] using hleft (N.coordinate_inverse y).2 hlow
        · simp only [G, if_neg hy, if_pos hyA]
      · by_cases hxB : x ∈ B
        · refine ⟨χ N.epsilon⁻¹, ?_⟩
          filter_upwards [hBopen.mem_nhds hxB, hC.isClosed.isOpen_compl.mem_nhds hxC]
            with y hyB hyC
          have hyA : y ∉ A := fun h => hAB h hyB
          by_cases hy : y ∈ N.carrier
          · have hhigh : q ≤ (N.coordinate_inverse y).2 := by
              by_contra h
              exact hyC (hmemC hy ⟨hp0.le.trans (hpositive hy hyB).le,
                (lt_of_not_ge h).le⟩)
            simpa only [G, if_pos hy] using hright (N.coordinate_inverse y).2 hhigh
          · simp only [G, if_neg hy, if_neg hyA, if_pos hyB]
        · have hxK : x ∉ connectedComponent N.center := by
            intro h
            rcases hcover.symm ▸ h with (h | h) | h
            · exact hxA h
            · exact hx (N.central_sphere_subset h)
            · exact hxB h
          refine ⟨0, ?_⟩
          filter_upwards [isClosed_connectedComponent.isOpen_compl.mem_nhds hxK] with y hy
          exact hGout hy
    have hGsmooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ G := by
      intro x
      by_cases hx : x ∈ N.carrier
      · have haxis := contMDiff_snd.contMDiffAt.comp x
          (N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hx))
        exact (hχ.contMDiff.contMDiffAt.comp x haxis).congr_of_eventuallyEq (hGin hx)
      · obtain ⟨r, hr⟩ := hGconstant hx
        exact (contMDiffAt_const (c := r)).congr_of_eventuallyEq hr
    refine ⟨G, hGsmooth, hGapprox, ?_⟩
    intro x v
    by_cases hx : x ∈ N.carrier
    · have he : G =ᶠ[𝓝 x] N.axialCutoff χ := by
        filter_upwards [N.carrier_open.mem_nhds hx] with y hy
        simp only [G, if_pos hy, N.axialCutoff_eq_of_mem χ hy]
      have hd : mvfderiv (𝓡 3) G x = mvfderiv (𝓡 3) (N.axialCutoff χ) x := by
        unfold mvfderiv
        rw [he.mfderiv_eq, he.eq_of_nhds]
      rw [hd, ← N.connection.inner_gradient,
        N.gradient_axialCutoff N.connection hχ hx]
      simp only [map_smul, smul_apply, smul_eq_mul, N.connection.inner_gradient, abs_mul]
      have hax : |mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v| ≤
          g.tangentNorm x v / c :=
        (le_div_iff₀ hc).mpr (by
          simpa only [c, mul_comm] using N.axial_mvfderiv_bound hx v)
      calc
        _ ≤ 1 * (g.tangentNorm x v / c) :=
          mul_le_mul (hderiv _) hax (abs_nonneg _) zero_le_one
        _ = _ := by ring
    · obtain ⟨r, hr⟩ := hGconstant hx
      unfold mvfderiv
      rw [hr.mfderiv_eq, hr.eq_of_nhds]
      simp only [mfderiv_const, ContinuousLinearMap.comp_zero, zero_apply, abs_zero]
      exact mul_nonneg (div_nonneg zero_le_one hc.le) (Real.sqrt_nonneg _)
  have hdist (x y : M) : ENNReal.ofReal (c * |H x - H y|) ≤ g.edist x y := by
    by_cases htop : g.edist x y = ⊤
    · rw [htop]
      exact le_top
    rw [ENNReal.ofReal_le_iff_le_toReal htop]
    by_contra hnot
    have hgap : 0 < c * |H x - H y| - (g.edist x y).toReal :=
      sub_pos.mpr (lt_of_not_ge hnot)
    let δ := (c * |H x - H y| - (g.edist x y).toReal) / (4 * c)
    have hδ : 0 < δ := div_pos hgap (mul_pos (by norm_num) hc)
    obtain ⟨G, hGsmooth, hnear, hgrad⟩ := happrox δ hδ
    let K : ℝ≥0 := ⟨1 / c, (div_pos zero_lt_one hc).le⟩
    have hGdist := g.edist_le_mul_edist_of_derivative_bound
      (hGsmooth.of_le (by simp)) (K := K) (div_pos zero_lt_one hc) hgrad x y
    have hK : ENNReal.ofReal (1 / c) = (K : ℝ≥0∞) := by
      change ENNReal.ofReal (K : ℝ) = (K : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    have hbound : ENNReal.ofReal (c * |G x - G y|) ≤ g.edist x y := by
      calc
        _ = ENNReal.ofReal c * EDist.edist (G x) (G y) := by
          rw [ENNReal.ofReal_mul hc.le, edist_dist, Real.dist_eq]
        _ ≤ ENNReal.ofReal c * ((K : ℝ≥0∞) * g.edist x y) :=
          mul_le_mul' le_rfl hGdist
        _ = g.edist x y := by
          rw [← hK, ← mul_assoc, ← ENNReal.ofReal_mul hc.le,
            mul_one_div_cancel hc.ne', ENNReal.ofReal_one, one_mul]
    have hreal := (ENNReal.ofReal_le_iff_le_toReal htop).mp hbound
    have hsum : |H x - H y| < |G x - G y| + 2 * δ := by
      have ht := (abs_sub_le (H x) (G x) (H y)).trans
        (add_le_add le_rfl (abs_sub_le (G x) (G y) (H y)))
      rw [abs_sub_comm (H x) (G x)] at ht
      linarith [hnear x, hnear y]
    have hδeq : 4 * c * δ = c * |H x - H y| - (g.edist x y).toReal := by
      dsimp only [δ]
      field_simp
    have hscaled := mul_lt_mul_of_pos_left hsum hc
    nlinarith
  have hcont : Continuous H := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    let K : ℝ≥0 := ⟨1 / c, (div_pos zero_lt_one hc).le⟩
    have hK : ENNReal.ofReal (1 / c) = (K : ℝ≥0∞) := by
      change ENNReal.ofReal (K : ℝ) = (K : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    have hLip : LipschitzWith K H := by
      intro x y
      calc
        EDist.edist (H x) (H y) = ENNReal.ofReal (1 / c) *
            ENNReal.ofReal (c * |H x - H y|) := by
          rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one hc.le),
            ← mul_assoc, one_div_mul_cancel hc.ne', one_mul, edist_dist, Real.dist_eq]
        _ ≤ ENNReal.ofReal (1 / c) * g.edist x y := mul_le_mul' le_rfl (hdist x y)
        _ = (K : ℝ≥0∞) * EDist.edist x y := by rw [hK]; rfl
    exact hLip.continuous
  refine ⟨H, hcont, ?_, ?_, ?_, ?_, hdist⟩
  · intro x hx
    simp only [H, if_pos hx]
  · intro x hx
    change x ∈ A \ N.carrier at hx
    simp only [H, if_neg hx.2, if_pos hx.1]
  · intro x hx
    change x ∈ B \ N.carrier at hx
    have hxA : x ∉ A := fun h => hAB h hx.1
    simp only [H, if_neg hx.2, if_neg hxA, if_pos hx.1]
  · intro x hx
    exact hHout hx

end PoincareConjecture.EpsilonNeck
