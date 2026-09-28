import PoincareConjecture.Proofs.M32.Claim11_34.AnnulusSeparation
import PoincareConjecture.Proofs.M32.Claim11_34.HornNonFilling













set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32




theorem strongNeck_centralSphere_subset_normalizedBall
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) (hhalf : epsilon < 1 / 2) :
    N.central_sphere ⊆ (F.metric t).ball N.center
      ((2 * Real.pi + 1) / Real.sqrt ((F.connection t).scalarCurvature N.center)) := by
  let P := spatialNeck N hhalf
  intro y hy
  have hdist := P.edist_central_sphere_le_two_pi_mul_scale
    P.center_on_central_sphere hy
  change (F.metric t).edist N.center y ≤ ENNReal.ofReal (2 * Real.pi * N.scale) at hdist
  have hscale : N.scale =
      (Real.sqrt ((F.connection t).scalarCurvature N.center))⁻¹ := by
    rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, Real.sqrt_eq_rpow]
  have hradius : (2 * Real.pi + 1) * N.scale =
      (2 * Real.pi + 1) / Real.sqrt ((F.connection t).scalarCurvature N.center) := by
    rw [hscale, div_eq_mul_inv]
  change (F.metric t).edist N.center y < ENNReal.ofReal _
  apply hdist.trans_lt
  rw [← hradius]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by positivity) N.scale_pos)).mpr (by nlinarith [N.scale_pos])





theorem terminalBlowupSequence_eventually_horn_annulus_separation :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
        [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
        [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
        [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
        [∀ k, SecondCountableTopology (M k)]
        {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
        (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
        (Q : ∀ k, SingularLimitConclusion (H k))
        (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
        (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
        (hdiv : Tendsto (fun k =>
          ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)
        (_hM04 : RicciFlowCurvatureTheory.{u}) (A : RepairedNeckCapTopologyTheory.{u})
        {K B : ℝ} {accuracy : ℕ → ℝ},
        0 < K → 0 < B → (∀ k, (H k).r₀⁻¹ ^ 2 < K) →
        (∀ k, (H k).analytic_constant = B) →
        (∀ k, accuracy k ≤ epsilon₀) → (∀ k, accuracy k ≤ A.epsilon₀) →
        ∀ horn : ∀ k, StrongHorn (Q k).extension (accuracy k),
          (∀ k, x k ∈ (horn k).carrier) →
          (∀ k, ∀ y ∈ (horn k).boundary_sphere,
            ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K) →
          ∀ N : ∀ k, GeneralizedStrongNeck (Q k).extension.extended (T k) (accuracy k),
            (∀ k, (N k).center = x k) →
            BlowupBaseBallsCompact (terminalBlowupSequence H Q x hpos hdiv) →
            (∀ k, (N k).central_sphere ⊆
              (terminalBlowupSequence H Q x hpos hdiv).baseBall k (2 * Real.pi + 1)) ∧
            ∀ R : ℝ, 2 * Real.pi + 3 < R → ∀ᶠ k : ℕ in atTop,
              ∃ yNeg yPos : ((Q k).extension.extended.slice (T k)).carrier,
                yNeg ∈ (terminalBlowupSequence H Q x hpos hdiv).baseBall k (2 * R) \
                  (terminalBlowupSequence H Q x hpos hdiv).baseBall k R ∧
                yPos ∈ (terminalBlowupSequence H Q x hpos hdiv).baseBall k (2 * R) \
                  (terminalBlowupSequence H Q x hpos hdiv).baseBall k R ∧
                ¬ JoinedIn (N k).central_sphereᶜ yNeg yPos := by
  obtain ⟨epsilon₁, hpos₁, hsmall₁, _, hnoFill⟩ :=
    terminalBlowupSequence_eventually_horn_neck_no_filling.{u}
  obtain ⟨epsilon₂, hpos₂, _, htransport⟩ := exists_horn_boundary_sphere_transport.{u}
  refine ⟨min epsilon₁ epsilon₂, lt_min hpos₁ hpos₂,
    (min_le_left _ _).trans hsmall₁, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H Q x hpos hdiv hM04 A K B accuracy
    hK hB hcutoff hconstant hsmall hA horn hx hboundary N hcenter hballs
  have hsmall₁' (k : ℕ) : accuracy k ≤ epsilon₁ :=
    (hsmall k).trans (min_le_left _ _)
  have hhalf (k : ℕ) : accuracy k < 1 / 2 :=
    ((hsmall₁' k).trans hsmall₁).trans_lt (by norm_num)
  constructor
  · intro k y hy
    have hball := strongNeck_centralSphere_subset_normalizedBall (N k) (hhalf k) hy
    change ((Q k).extension.extended.metric (T k)).edist (N k).center y <
      ENNReal.ofReal ((2 * Real.pi + 1) /
        Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature
          (N k).center)) at hball
    change ((Q k).extension.extended.metric (T k)).edist (x k) y <
      ENNReal.ofReal ((2 * Real.pi + 1) /
        Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))
    simpa only [hcenter k] using hball
  · intro R hR
    have hRpos : 0 < R := by linarith [Real.pi_pos]
    have hnoFill' := hnoFill H Q x hpos hdiv hM04 A hK hB hcutoff hconstant
      hsmall₁' hA horn hx hboundary N hcenter
    have hinside := terminalBlowupSequence_baseBalls_subset_horns H Q x hpos hdiv
      hM04 hK hB hcutoff hconstant horn hx hboundary (2 * R + 1) (by positivity)
    filter_upwards [hnoFill', hballs (2 * R) (by positivity), hinside] with k hfill hcompact hin
    let g := (Q k).extension.extended.metric (T k)
    let P := spatialNeck (N k) (hhalf k)
    have hscale : (N k).scale =
        (Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))⁻¹ := by
      rw [(N k).scale_scalar, neg_div, Real.rpow_neg (N k).scalar_center_pos.le,
        Real.sqrt_eq_rpow, hcenter k]
    have hballEq (a : ℝ) : g.ball P.center (a * P.scale) =
        (terminalBlowupSequence H Q x hpos hdiv).baseBall k a := by
      change g.ball (N k).center (a * (N k).scale) =
        g.ball (x k) (a /
          Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))
      rw [hcenter k, hscale, div_eq_mul_inv]
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : ((Q k).extension.extended.slice (T k)).carrier → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : ((Q k).extension.extended.slice (T k)).carrier → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace ((Q k).extension.extended.slice (T k)).carrier :=
      EMetricSpace.ofRiemannianMetric (𝓡 3) _
    have hcontinuous : Continuous (fun y => g.edist (x k) y) :=
      continuous_const.edist continuous_id
    have hclosure : closure (g.ball P.center (2 * R * P.scale)) ⊆ (horn k).carrier := by
      rw [hballEq]
      apply subset_trans ?_ hin
      have hclosed : IsClosed {y | g.edist (x k) y ≤
          ENNReal.ofReal ((2 * R) /
            Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))} :=
        isClosed_le hcontinuous continuous_const
      have hsub : closure ((terminalBlowupSequence H Q x hpos hdiv).baseBall k (2 * R)) ⊆
          {y | g.edist (x k) y ≤ ENNReal.ofReal ((2 * R) /
            Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))} := by
        apply closure_minimal ?_ hclosed
        intro y hy
        change g.edist (x k) y < ENNReal.ofReal ((2 * R) /
          Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k))) at hy
        exact hy.le
      intro y hy
      change g.edist (x k) y < ENNReal.ofReal ((2 * R + 1) /
        Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))
      have hle : g.edist (x k) y ≤ ENNReal.ofReal ((2 * R) /
          Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k))) :=
        hsub hy
      apply hle.trans_lt
      apply (ENNReal.ofReal_lt_ofReal_iff
        (div_pos (by positivity) (Real.sqrt_pos.2 (hpos k)))).mpr
      exact (div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 (hpos k))).2 (by linarith)
    obtain ⟨_, _, _, _, _, hsep⟩ := htransport (Q k).extension (N k).epsilon_pos
      ((hsmall k).trans (min_le_right _ _)) (horn k) P rfl (by
        change (N k).center ∈ (horn k).carrier
        rw [hcenter k]
        exact hx k)
    have hcompact' : IsCompact (closure (g.ball P.center (2 * R * P.scale))) := by
      rwa [hballEq]
    obtain ⟨yNeg, yPos, hym, hyp, hnot⟩ :=
      exists_neck_annulus_points_not_joined_of_no_filling P hsep hfill hR hcompact' hclosure
    refine ⟨yNeg, yPos, ?_, ?_, hnot⟩
    · change yNeg ∈ g.ball P.center (2 * R * P.scale) \ g.ball P.center (R * P.scale) at hym
      rw [hballEq, hballEq] at hym
      exact hym
    · change yPos ∈ g.ball P.center (2 * R * P.scale) \ g.ball P.center (R * P.scale) at hyp
      rw [hballEq, hballEq] at hyp
      exact hyp

end PoincareConjecture.M32
