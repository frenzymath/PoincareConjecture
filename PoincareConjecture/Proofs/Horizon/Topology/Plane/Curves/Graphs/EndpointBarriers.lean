


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.TransverseCuts
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.Quadrants








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

private theorem exists_graph_endpoint_barrier
    {lo : ℝ → ℝ} {c d : ℝ} (hlo : DifferentiableAt ℝ lo c)
    {K : ℝ × ℝ → ℝ × ℝ} (hK : ContDiffAt ℝ 1 K 0)
    (haxis : ∀ s : ℝ, K (s, 0) = (c + s * d, lo (c + s * d)))
    (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (hpositive : 0 < d * ℓ (1, deriv lo c))
    (hzero : ∀ᶠ z in 𝓝 (0 : ℝ), ℓ (K (0, z) - (c, lo c)) = 0)
    {C W : Set (ℝ × ℝ)} (hW : IsOpen W) (hcW : (c, lo c) ∈ W)
    (hsep : ∀ q ∈ C ∩ W, ℓ (q - (c, lo c)) ≤ 0) :
    ∃ δ > 0, ∀ s z : ℝ, |s| < δ → |z| < δ → 0 < s → K (s, z) ∉ C := by
  let f : ℝ × ℝ → ℝ := fun q => ℓ (K q - (c, lo c))
  have hf : ContDiffAt ℝ 1 f 0 :=
    ℓ.contDiff.contDiffAt.comp 0 (hK.sub contDiffAt_const)
  have harg : HasDerivAt (fun s : ℝ => c + s * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c
  have hloc : HasDerivAt lo (deriv lo c) (c + 0 * d) := by simpa using hlo.hasDerivAt
  have hgraph := (harg.prodMk (hloc.comp 0 harg)).sub_const (c, lo c)
  have hlin := ℓ.hasFDerivAt.comp_hasDerivAt 0 hgraph
  have hval : ℓ (d, deriv lo c * d) = d * ℓ (1, deriv lo c) := by
    have he : (d, deriv lo c * d) = d • ((1 : ℝ), deriv lo c) := by
      ext <;> simp [smul_eq_mul, mul_comm]
    rw [he, map_smul]
    rfl
  have hdaxis : HasDerivAt (fun s : ℝ => f (s, 0)) (d * ℓ (1, deriv lo c)) 0 := by
    have heq : (fun s : ℝ => f (s, 0)) =
        (fun s => ℓ ((c + s * d, lo (c + s * d)) - (c, lo c))) := by
      funext s
      dsimp [f]
      rw [haxis]
      rfl
    rw [heq]
    simpa only [Function.comp_def, hval] using hlin
  have hpath : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hdf : HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ), (0 : ℝ)) :=
    hf.differentiableAt_one.hasFDerivAt
  have hdpath : HasDerivAt (fun s : ℝ => f (s, 0)) (fderiv ℝ f 0 (1, 0)) 0 :=
    hdf.comp_hasDerivAt (f := fun s : ℝ => (s, (0 : ℝ))) 0 hpath
  have hpos : 0 < fderiv ℝ f 0 (1, 0) := by
    rw [← hdaxis.unique hdpath]
    exact hpositive
  have hz : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → f q = 0 := by
    filter_upwards [continuousAt_snd.tendsto.eventually hzero] with q hq hq0
    simpa only [f, ← hq0, Prod.eta] using hq
  obtain ⟨ρ, hρ, hsign⟩ := Poincare.Analysis.exists_first_coordinate_sign_radius hf hpos hz
  have hK0 : K 0 = (c, lo c) := by
    change K ((0 : ℝ), (0 : ℝ)) = _
    simpa only [zero_mul, add_zero] using haxis 0
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp
    (hK.continuousAt.preimage_mem_nhds (hW.mem_nhds (hK0.symm ▸ hcW)))
  refine ⟨min ρ η, lt_min hρ hη, fun s z hs hz hspos hmem => ?_⟩
  have hsρ := hs.trans_le (min_le_left _ _)
  have hzρ := hz.trans_le (min_le_left _ _)
  have hlocal : K (s, z) ∈ W := hball (show (s, z) ∈ Metric.ball (0 : ℝ × ℝ) η by
    simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using
      And.intro (hs.trans_le (min_le_right _ _)) (hz.trans_le (min_le_right _ _)))
  exact (not_lt_of_ge (hsep _ ⟨hmem, hlocal⟩)) ((hsign s z hsρ hzρ).1.mpr hspos)

namespace TransverseGraphCuts

variable {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
  (P : TransverseGraphCuts lo a b ua wa ub wb)

private theorem coordinates_axis_mem_source
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (hab : a < b) (hI : Icc a b ⊆ X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t, 0) ∈ (P.coordinates hX hlo).source := by
  rw [coordinates, obliqueStripCoordinates_source]
  refine ⟨⟨by linarith [P.radius_pos], P.radius_pos⟩, ?_⟩
  rw [P.A_zero, P.B_zero]
  apply hI
  constructor <;> nlinarith [ht.1, ht.2]

private theorem exists_left_endpoint_barrier
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (hab : a < b) (hI : Icc a b ⊆ X)
    (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (hcut : ℓ (ua, wa) = 0)
    (htangent : 0 < ℓ (1, deriv lo a))
    {C W : Set (ℝ × ℝ)} (hW : IsOpen W) (haW : (a, lo a) ∈ W)
    (hsep : ∀ q ∈ C ∩ W, ℓ (q - (a, lo a)) ≤ 0) :
    ∃ δ > 0, ∀ t z : ℝ, |t| < δ → |z| < δ → 0 < t →
      P.coordinates hX hlo (t, z) ∉ C := by
  have h0 := P.coordinates_axis_mem_source hX hlo hab hI (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hK : ContDiffAt ℝ 1 (P.coordinates hX hlo) 0 :=
    (((P.smooth_coordinates hX hlo) 0 h0).contDiffAt
      ((P.coordinates hX hlo).open_source.mem_nhds h0)).of_le (by simp)
  have haxis (s : ℝ) : P.coordinates hX hlo (s, 0) = (a + s * (b - a), lo (a + s * (b - a))) := by
    rw [P.coordinates_apply, obliqueStripMap_bottom P.A_zero P.B_zero]
  have hzero : ∀ᶠ z in 𝓝 (0 : ℝ), ℓ (P.coordinates hX hlo (0, z) - (a, lo a)) = 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-P.radius) P.radius from
      ⟨by linarith [P.radius_pos], P.radius_pos⟩)] with z hz
    rw [P.coordinates_apply, obliqueStripMap_left, P.left_line_identity hz]
    have he : (a + P.left.parameter.symm z * ua, lo a + P.left.parameter.symm z * wa) -
        (a, lo a) = P.left.parameter.symm z • (ua, wa) := by
      ext <;> simp [smul_eq_mul]
    rw [he, map_smul, hcut, smul_zero]
  exact exists_graph_endpoint_barrier
    (((hlo a (hI (left_mem_Icc.mpr hab.le))).contDiffAt
      (hX.mem_nhds (hI (left_mem_Icc.mpr hab.le)))).differentiableAt (by simp))
    hK haxis ℓ (mul_pos (sub_pos.mpr hab) htangent) hzero hW haW hsep

private theorem exists_right_endpoint_barrier
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (hab : a < b) (hI : Icc a b ⊆ X)
    (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (hcut : ℓ (ub, wb) = 0)
    (htangent : ℓ (1, deriv lo b) < 0)
    {C W : Set (ℝ × ℝ)} (hW : IsOpen W) (hbW : (b, lo b) ∈ W)
    (hsep : ∀ q ∈ C ∩ W, ℓ (q - (b, lo b)) ≤ 0) :
    ∃ δ > 0, ∀ t z : ℝ, |1 - t| < δ → |z| < δ → t < 1 →
      P.coordinates hX hlo (t, z) ∉ C := by
  have h1 := P.coordinates_axis_mem_source hX hlo hab hI (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  let K : ℝ × ℝ → ℝ × ℝ := fun q => P.coordinates hX hlo (1 - q.1, q.2)
  have hK : ContDiffAt ℝ 1 K 0 := by
    have h := (((P.smooth_coordinates hX hlo) (1, 0) h1).contDiffAt
      ((P.coordinates hX hlo).open_source.mem_nhds h1)).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
    have hg : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (1 - q.1, q.2)) (0 : ℝ × ℝ) :=
      (contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd
    have hp : ContDiffAt ℝ 1 (P.coordinates hX hlo)
        ((fun q : ℝ × ℝ => (1 - q.1, q.2)) 0) := by
      simpa only [Prod.fst_zero, Prod.snd_zero, sub_zero] using h
    exact hp.comp (f := fun q : ℝ × ℝ => (1 - q.1, q.2)) 0 hg
  have haxis (s : ℝ) : K (s, 0) = (b + s * (a - b), lo (b + s * (a - b))) := by
    dsimp [K]
    rw [P.coordinates_apply, obliqueStripMap_bottom P.A_zero P.B_zero]
    have he : a + (1 - s) * (b - a) = b + s * (a - b) := by ring
    rw [he]
  have hzero : ∀ᶠ z in 𝓝 (0 : ℝ), ℓ (K (0, z) - (b, lo b)) = 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-P.radius) P.radius from
      ⟨by linarith [P.radius_pos], P.radius_pos⟩)] with z hz
    dsimp [K]
    rw [sub_zero, P.coordinates_apply, obliqueStripMap_right, P.right_line_identity hz]
    have he : (b + P.right.parameter.symm z * ub, lo b + P.right.parameter.symm z * wb) -
        (b, lo b) = P.right.parameter.symm z • (ub, wb) := by
      ext <;> simp [smul_eq_mul]
    rw [he, map_smul, hcut, smul_zero]
  obtain ⟨δ, hδ, hlocal⟩ := exists_graph_endpoint_barrier
    (((hlo b (hI (right_mem_Icc.mpr hab.le))).contDiffAt
      (hX.mem_nhds (hI (right_mem_Icc.mpr hab.le)))).differentiableAt (by simp))
    hK haxis ℓ (mul_pos_of_neg_of_neg (sub_neg.mpr hab) htangent) hzero hW hbW hsep
  refine ⟨δ, hδ, fun t z ht hz ht1 => ?_⟩
  simpa only [K, sub_sub_cancel] using hlocal (1 - t) z ht hz (sub_pos.mpr ht1)

private theorem exists_height_tube {u v : ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (haxis : ∀ t ∈ Icc u v, (t, (0 : ℝ)) ∈ W) :
    ∃ δ > 0, ∀ t ∈ Icc u v, ∀ z : ℝ, |z| < δ → (t, z) ∈ W := by
  have hsub : Icc u v ×ˢ {(0 : ℝ)} ⊆ W := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact haxis t ht
  obtain ⟨U, V, _, hV, hIU, h0V, hUV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hW hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (h0V (mem_singleton (0 : ℝ))))
  refine ⟨δ, hδ, fun t ht z hz => hUV ⟨hIU ht, hball ?_⟩⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz




theorem exists_avoiding_strip
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (hab : a < b) (hI : Icc a b ⊆ X)
    {C : Set (ℝ × ℝ)} (hC : IsClosed C)
    (havoid : ∀ x ∈ Ioo a b, (x, lo x) ∉ C)
    (ℓa ℓb : (ℝ × ℝ) →L[ℝ] ℝ)
    (hcutA : ℓa (ua, wa) = 0) (hcutB : ℓb (ub, wb) = 0)
    (htangentA : 0 < ℓa (1, deriv lo a)) (htangentB : ℓb (1, deriv lo b) < 0)
    {Wa Wb : Set (ℝ × ℝ)} (hWa : IsOpen Wa) (hWb : IsOpen Wb)
    (haW : (a, lo a) ∈ Wa) (hbW : (b, lo b) ∈ Wb)
    (hsepA : ∀ q ∈ C ∩ Wa, ℓa (q - (a, lo a)) ≤ 0)
    (hsepB : ∀ q ∈ C ∩ Wb, ℓb (q - (b, lo b)) ≤ 0) :
    ∃ δ > 0, δ ≤ P.radius ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < δ → (t, z) ∈ (P.coordinates hX hlo).source) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ → P.coordinates hX hlo (t, z) ∉ C) ∧
      (∀ z : ℝ, |z| < δ →
        P.coordinates hX hlo (0, z) =
          (a + P.left.parameter.symm z * ua, lo a + P.left.parameter.symm z * wa) ∧
        P.coordinates hX hlo (1, z) =
          (b + P.right.parameter.symm z * ub, lo b + P.right.parameter.symm z * wb)) := by
  obtain ⟨α, hα, hleft⟩ :=
    P.exists_left_endpoint_barrier hX hlo hab hI ℓa hcutA htangentA hWa haW hsepA
  obtain ⟨β, hβ, hright⟩ :=
    P.exists_right_endpoint_barrier hX hlo hab hI ℓb hcutB htangentB hWb hbW hsepB
  let η := min α β
  have hη : 0 < η := lt_min hα hβ
  let H := P.coordinates hX hlo
  obtain ⟨δs, hδs, hsource⟩ := exists_height_tube H.open_source
    (fun t ht => P.coordinates_axis_mem_source hX hlo hab hI ht)
  let W : Set (ℝ × ℝ) := H.source ∩ H ⁻¹' Cᶜ
  have hW : IsOpen W := H.continuousOn.isOpen_inter_preimage H.open_source hC.isOpen_compl
  have hmid : ∀ t ∈ Icc η (1 - η), (t, (0 : ℝ)) ∈ W := by
    intro t ht
    have ht0 : 0 < t := hη.trans_le ht.1
    have ht1 : t < 1 := by linarith [ht.2]
    refine ⟨P.coordinates_axis_mem_source hX hlo hab hI ⟨ht0.le, ht1.le⟩, ?_⟩
    change P.coordinates hX hlo (t, 0) ∉ C
    rw [P.coordinates_apply, obliqueStripMap_bottom P.A_zero P.B_zero]
    apply havoid
    constructor <;> nlinarith
  obtain ⟨δm, hδm, hmiddle⟩ := exists_height_tube hW hmid
  let δ := min P.radius (min δs (min α (min β δm)))
  have hδ : 0 < δ := lt_min P.radius_pos (lt_min hδs (lt_min hα (lt_min hβ hδm)))
  have hδP : δ ≤ P.radius := min_le_left _ _
  have hδs' : δ ≤ δs := (min_le_right _ _).trans (min_le_left _ _)
  have hδα : δ ≤ α :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδβ : δ ≤ β :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hδm' : δ ≤ δm :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ, hδ, hδP, fun t ht z hz => hsource t ht z (hz.trans_le hδs'), ?_, ?_⟩
  · intro t ht z hz
    by_cases hta : t < η
    · exact hleft t z (by rw [abs_of_pos ht.1]; exact hta.trans_le (min_le_left _ _))
        (hz.trans_le hδα) ht.1
    by_cases htb : 1 - t < η
    · exact hright t z (by rw [abs_of_pos (sub_pos.mpr ht.2)]; exact htb.trans_le (min_le_right _ _))
        (hz.trans_le hδβ) ht.2
    · exact (hmiddle t ⟨le_of_not_gt hta, by linarith⟩ z (hz.trans_le hδm')).2
  · intro z hz
    have hzP : z ∈ Ioo (-P.radius) P.radius := abs_lt.mp (hz.trans_le hδP)
    constructor
    · rw [P.coordinates_apply, obliqueStripMap_left, P.left_line_identity hzP]
    · rw [P.coordinates_apply, obliqueStripMap_right, P.right_line_identity hzP]

end TransverseGraphCuts

end Poincare.Topology.Plane.Curves
