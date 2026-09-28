import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnular
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularHomotopy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory Real Topology
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

set_option maxHeartbeats 1200000 in

theorem m60Sphere_annular_replacement (g : RiemannianMetric n M) :
    M60SphereAnnularReplacement g := by
  intro s hs c scale hscale v hv hnull dim e he hei hread hvalue hjet R hR eta heta
  let F : ℕ → LoopPlane → M := fun j z => s j ((chartAt LoopPlane (c j)).symm (scale j • z))
  have hF (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) 1 (F j) :=
    (hs j).comp (((suSphereChart_smooth (c j)).of_le (by simp)).comp
      ((scale j • ContinuousLinearMap.id ℝ LoopPlane).contDiff.contMDiff))
  let f : ℕ → C(LoopPlane, M) := fun j => ⟨F j, (hF j).continuous⟩
  let V : C(LoopPlane, M) := ⟨v ∘ m60SphereParameter,
    hv.continuous.comp m60SphereParameter_contMDiff.continuous⟩
  let a : C(LoopPlane, M) := ⟨v ∘ suAnnularCap R,
    hv.continuous.comp (suAnnularCap_smooth R).continuous⟩
  have hV : ContMDiff (𝓡 2) (𝓡 n) 1 V :=
    hv.comp (m60SphereParameter_contMDiff.of_le (by simp))
  have ha : ContMDiff (𝓡 2) (𝓡 n) 1 a :=
    hv.comp ((suAnnularCap_smooth R).of_le (by simp))
  have hlim : Tendsto f atTop (𝓝 V) :=
    suObservation_tendsto_compactOpen he.continuous hei.isEmbedding f V hvalue
  obtain ⟨L₀, hL₀, hlate⟩ := suObservation_eventually_metric_bound g he hread F hF hV hjet
    (isCompact_closedBall (0 : LoopPlane) (R + 1))
  obtain ⟨L₁, hL₁, hcapbound⟩ := suObservation_metric_bound_on_compact g he hread ha
    (isCompact_closedBall (0 : LoopPlane) (R + 1))
  let L := L₀ + L₁
  have hL : 0 < L := add_pos hL₀ hL₁
  obtain ⟨C, U, B, hU, hdiag, hB, h0, h1, _, hC, hspace, hsmall⟩ := suAnnular_contraction g
  obtain ⟨H, hH, hdensity⟩ := suAnnularBlend_density_bound g
  let K₁ := 4 * π * R * (H / 2 * (B * L))
  let K₂ := 4 * π * R * (B * L) ^ 2
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp only [K₂]; positivity
  let A := eta / (4 * (K₁ + 1))
  have hA : 0 < A := div_pos heta (by positivity)
  obtain ⟨W, hW, hdiagW, hWU, htime⟩ := hsmall A hA
  obtain ⟨hvcont, p, hvnull⟩ := hnull
  let vs : C(UnitTwoSphere, M) := ⟨v, hvcont⟩
  have hn : vs.Nullhomotopic := ⟨p, hvnull⟩
  obtain ⟨Hcap⟩ := suNullSphere_relative_caps vs hn
    ⟨m60SphereParameter, m60SphereParameter_contMDiff.continuous⟩
    ⟨suAnnularCap R, (suAnnularCap_smooth R).continuous⟩
    {z : LoopPlane | ‖z‖ = R} (fun z hz => (suAnnularCap_boundary hR hz).symm)
  have hcapcircle (t : unitInterval) (z : LoopPlane) (hz : ‖z‖ = R) : Hcap (t, z) = V z :=
    Hcap.eq_fst t hz
  obtain ⟨epsilon, hepsilon, hnear⟩ := suCircle_family_neighborhood
    ((V.continuous.comp continuous_snd).prodMk Hcap.continuous) hW hR
    (fun t z hz => by rw [hcapcircle t z hz]; exact hdiagW rfl)
  let d := min (R / 4) (min (1 / 4) (min (epsilon / 4) (eta / (4 * (K₂ + 1)))))
  have hd : 0 < d := lt_min (by positivity) (lt_min (by norm_num)
    (lt_min (by positivity) (div_pos heta (by positivity))))
  have hdR : d ≤ R / 4 := min_le_left _ _
  have hd1 : d ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hde : d ≤ epsilon / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hdeta : d ≤ eta / (4 * (K₂ + 1)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hRd : 2 * d < R := by linarith
  have hdlt : d < R := by linarith
  have hwidth : 2 * d < 1 := by linarith
  let K : Set LoopPlane := closedBall 0 (R + 2 * d) ∩ {z | R - 2 * d ≤ ‖z‖}
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) (R + 2 * d)).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hlimpairs : ∀ x ∈ (univ : Set unitInterval) ×ˢ K, (V x.2, Hcap x) ∈ W := by
    intro x hx
    apply hnear x.1 x.2
    · have hl : R - 2 * d ≤ ‖x.2‖ := hx.2.2
      linarith
    · have hh := mem_closedBall_zero_iff.mp hx.2.1
      linarith
  have hpairs := suCompactOpen_eventually_pairs f V hlim Hcap.toContinuousMap
    (isCompact_univ.prod hK) hW hlimpairs
  have hfirst := suCompactOpen_eventually_pairs f V hlim
    ⟨fun x => V x.2, V.continuous.comp continuous_snd⟩
    (isCompact_univ.prod (isCompact_closedBall (0 : LoopPlane) (R + 1))) hU
    (fun _ _ => hdiag rfl)
  have herror : 4 * π * R * (H * A / 2 * (B * L) + d * (B * L) ^ 2) ≤ eta := by
    have hAa : A * (4 * (K₁ + 1)) = eta := by
      dsimp only [A]
      exact div_mul_cancel₀ _ (by positivity)
    have hdd := (le_div_iff₀ (by positivity : 0 < 4 * (K₂ + 1))).mp hdeta
    have h₁ : K₁ * A ≤ eta / 4 := by nlinarith
    have h₂ : K₂ * d ≤ eta / 4 := by nlinarith
    calc
      _ = K₁ * A + K₂ * d := by dsimp only [K₁, K₂]; ring
      _ ≤ eta := by linarith
  filter_upwards [hlate, hpairs, hfirst] with j hj hpairj hfirstj
  have hfirstj' (z : LoopPlane) (hz : ‖z‖ < R + 2 * d) : (f j z, V z) ∈ U :=
    hfirstj (0, z) ⟨mem_univ _, mem_closedBall_zero_iff.mpr (by linarith)⟩
  have hfamily (x : unitInterval × LoopPlane) (hlo : R - 2 * d < ‖x.2‖)
      (hhi : ‖x.2‖ < R + 2 * d) : (f j x.2, Hcap x) ∈ W :=
    hpairj x ⟨mem_univ _, mem_closedBall_zero_iff.mpr hhi.le, hlo.le⟩
  have hcapnear (z : LoopPlane) (hlo : R - 2 * d < ‖z‖)
      (hhi : ‖z‖ < R + 2 * d) : (F j z, a z) ∈ W := by
    simpa only [Hcap.apply_one, ContinuousMap.comp_apply, f, a, vs,
      ContinuousMap.coe_mk, Function.comp_apply] using hfamily (1, z) hlo hhi
  let D := suAnnularBlend C (F j) a R d
  have hD : ContMDiff (𝓡 2) (𝓡 n) 1 D := suAnnularBlend_contMDiff C h0 h1
    (fun t ht q hq => hC (t, q) ⟨ht, hq⟩) (hF j) ha hd hRd
    (fun z hlo hhi => hWU (hcapnear z hlo hhi))
  let P := fun z : LoopPlane => D ((scale j)⁻¹ • z)
  have hP : ContMDiff (𝓡 2) (𝓡 n) 1 P :=
    hD.comp (((scale j)⁻¹ • ContinuousLinearMap.id ℝ LoopPlane).contDiff.contMDiff)
  have hPout (z : LoopPlane) (hz : scale j * (R + d) < ‖z‖) :
      P z = s j ((chartAt LoopPlane (c j)).symm z) := by
    have hr : R + d ≤ ‖(scale j)⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hscale j).le), ← div_eq_inv_mul]
      exact ((lt_div_iff₀ (hscale j)).mpr (by nlinarith only [hz])).le
    change suAnnularBlend C (F j) a R d ((scale j)⁻¹ • z) = _
    rw [suAnnularBlend_outer C (F j) a hr]
    change s j ((chartAt LoopPlane (c j)).symm (scale j • ((scale j)⁻¹ • z))) = _
    rw [smul_inv_smul₀ (hscale j).ne']
  let h := suSpherePlanePatch (s j) (c j) P
  have hh : ContMDiff (𝓡 2) (𝓡 n) 1 h :=
    suSpherePlanePatch_contMDiff (hs j) (c j) hP hPout
  have hparam (z : LoopPlane) : h ((chartAt LoopPlane (c j)).symm (scale j • z)) = D z := by
    change suSpherePlanePatch (s j) (c j) P ((chartAt LoopPlane (c j)).symm (scale j • z)) = _
    rw [suSpherePlanePatch_parameter]
    change D ((scale j)⁻¹ • (scale j • z)) = D z
    rw [inv_smul_smul₀ (hscale j).ne']
  obtain ⟨Bmap, G, hBmap, hGout⟩ := suAnnularBlend_plane_homotopy C h0 h1
    (fun t ht q hq => (hC (t, q) ⟨ht, hq⟩).continuousAt)
    (f j) V a Hcap.toHomotopy hd hfirstj'
    (fun x hlo hhi => hWU (hfamily x hlo hhi))
  let G' : C(unitInterval × LoopPlane, M) :=
    ⟨fun x => G (x.1, (scale j)⁻¹ • x.2),
      G.continuous.comp (f := fun x : unitInterval × LoopPlane => (x.1, (scale j)⁻¹ • x.2))
        (continuous_fst.prodMk (continuous_snd.const_smul ((scale j)⁻¹)))⟩
  have hG'out (t : unitInterval) (z : LoopPlane) (hz : scale j * (R + d) < ‖z‖) :
      G' (t, z) = s j ((chartAt LoopPlane (c j)).symm z) := by
    have hr : R + d ≤ ‖(scale j)⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hscale j).le), ← div_eq_inv_mul]
      exact ((lt_div_iff₀ (hscale j)).mpr (by nlinarith only [hz])).le
    change G (t, (scale j)⁻¹ • z) = _
    rw [hGout t _ hr]
    change s j ((chartAt LoopPlane (c j)).symm (scale j • ((scale j)⁻¹ • z))) = _
    rw [smul_inv_smul₀ (hscale j).ne']
  have hG'zero (z : LoopPlane) : G' (0, z) = s j ((chartAt LoopPlane (c j)).symm z) := by
    change G (0, (scale j)⁻¹ • z) = _
    rw [G.apply_zero]
    change s j ((chartAt LoopPlane (c j)).symm (scale j • ((scale j)⁻¹ • z))) = _
    rw [smul_inv_smul₀ (hscale j).ne']
  obtain ⟨h', hh', heq⟩ := suSpherePlanePatch_homotopic
    ⟨s j, (hs j).continuous⟩ (c j) G' hG'out hG'zero
  have hend : (fun z => G' (1, z)) = P := by
    funext z
    change G (1, (scale j)⁻¹ • z) = _
    rw [G.apply_one, hBmap]
    rfl
  have heqh : (⟨h, hh.continuous⟩ : C(UnitTwoSphere, M)) = h' := by
    ext p
    rw [heq, hend]
    rfl
  refine ⟨h, hh, by rw [heqh]; exact hh', ?_⟩
  obtain ⟨hiF, hareaF⟩ := suSphereArea_rescaled g (hs j) (c j) (hscale j)
  obtain ⟨hiD, hareaD⟩ := suSphereArea_rescaled g hh (c j) (hscale j)
  have heqD : (fun z => h ((chartAt LoopPlane (c j)).symm (scale j • z))) = D := funext hparam
  rw [heqD] at hiD hareaD
  obtain ⟨hia, _, hareaa⟩ := suAnnularCap_area g hv hR
  change (∫ z in ball (0 : LoopPlane) R, m60AreaDensity g a z) = _ at hareaa
  have hcollar := suAnnular_area_estimate g hD hd hdlt (fun z hz => by
    have hlo : R - d < ‖z‖ := not_le.mp (by simpa only [mem_closedBall_zero_iff] using hz.2)
    have hhi : ‖z‖ < R + d := mem_ball_zero_iff.mp hz.1
    have hp := hcapnear z (by linarith) (by linarith)
    have hzK : z ∈ closedBall (0 : LoopPlane) (R + 1) :=
      mem_closedBall_zero_iff.mpr (by linarith)
    exact hdensity C W (fun x hx => (hC x ⟨hx.1, hWU hx.2⟩).mdifferentiableAt one_ne_zero)
      A B L hA.le hB hL.le (fun x hx => (htime x hx).le)
      (fun x hx => hspace x ⟨hx.1, hWU hx.2⟩) (F j) a (hF j) ha R d hd z
      (norm_pos_iff.mp (by linarith)) hlo hhi hp (fun w => by
        have h₀ := hj z hzK w
        have h₁ := hcapbound z hzK w
        dsimp only [L]
        nlinarith))
  have hbook := suAnnularBlend_area_bookkeeping g C (F j) a hd hiF hia hiD
    (hcollar.2.trans herror)
  rw [hareaD, hareaF, hareaa] at hbook
  exact hbook

end PoincareConjecture.M60
