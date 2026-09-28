import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.ScalarRatio
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.FullDomainComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.TranslatedNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Boundary.Reparameterization



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}




theorem eventually_static_neck_terminal_recenter
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    {ε δ l u : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 10000000000000)
    (hεδ : 2 * ε ≤ δ) (hδhalf : δ < 1 / 2) (hl : 0 < l) (hu : 0 < u)
    (hbudget : (32 + 6 * (2000000000004 : ℝ) ^ 2) * ε ^ 2 < δ ^ 2) :
    ∀ᶠ t in 𝓝[<] T,
      ∀ N : EpsilonNeck ((H.terminalFlow P04).metric t),
        N.epsilon = ε → N.carrier ⊆ A →
        l ≤ N.connection.scalarCurvature N.center →
        N.connection.scalarCurvature N.center ≤ u →
        ∀ (s : ℝ) (q : UnitTwoSphere),
          MapsTo (fun z : ℝ => z + s) (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹) →
          ∃ K : EpsilonNeck (H.terminalMetric P04),
            K.epsilon = δ ∧ K.connection = H.terminalConnection P04 ∧
            K.center = N.coordinate_map (q, s) ∧
            K.central_sphere = range (fun p : UnitTwoSphere => N.coordinate_map (p, s)) ∧
            K.carrier = N.region (-δ⁻¹ + s) (δ⁻¹ + s) ∧
            ∀ a b : ℝ, -δ⁻¹ ≤ a → b ≤ δ⁻¹ →
              K.region a b = N.region (a + s) (b + s) := by
  obtain ⟨t₀, _, ht₀, hcomparison⟩ :=
    H.exists_late_static_neck_terminal_full_domain_comparison P04 hA hε
      (by linarith) hl hu
  filter_upwards [Ioo_mem_nhdsLT ht₀,
    H.eventually_static_neck_terminal_scalar_ratio P04 hA hε hsmall hl]
    with t ht hscalar
  intro N hNe hNA hql hqu s q hsub
  have hδ : 0 < δ := (by linarith : 0 < 2 * ε).trans_le hεδ
  have hs : s ∈ Ioo (-ε⁻¹) ε⁻¹ := by
    simpa only [zero_add] using hsub
      (show (0 : ℝ) ∈ Ioo (-δ⁻¹) δ⁻¹ from
        ⟨neg_neg_of_pos (inv_pos.mpr hδ), inv_pos.mpr hδ⟩)
  have hy : N.coordinate_map (q, s) ∈ N.carrier :=
    N.coordinate_map_mem ⟨mem_univ _, by simpa only [hNe] using hs⟩
  obtain ⟨hQ, hscalar⟩ := hscalar N hNe hNA hql
  obtain ⟨hR, hcmax, hcerror⟩ := hscalar _ hy
  obtain ⟨_, hsmooth, bound, hbound, hjet⟩ :=
    hcomparison t ⟨ht.1.le, ht.2⟩ N hNe hNA hql hqu
  simp only [H.terminalFlow_scalar_at_terminal, H.terminalFlow_metric_at_terminal]
    at hsmooth hjet
  let Q := (H.terminalConnection P04).scalarCurvature N.center
  let R := (H.terminalConnection P04).scalarCurvature (N.coordinate_map (q, s))
  let B : RoundCylinderTwoTensor := fun z v w => Q *
    roundCylinderPullback (H.terminalMetric P04) N.coordinate_map z v w
  have hclose := RoundCylinderTranslation.close_scaled_pullback_of_linear_error
    hε hεδ (div_pos hR hQ).le hcmax (by norm_num) hcerror s hsmooth
    (fun z hz => (hjet z hz).trans (by nlinarith : bound ≤ 4 * ε ^ 2)) hsub hbudget
  have hsub' : MapsTo (fun z : ℝ => 1 * z + s)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
    simpa only [one_mul, hNe] using hsub
  have htensor : (fun z v w => R / Q * RoundCylinderTranslation.pullback s B z v w) =
      (fun z v w => R * RoundCylinderAffine.pullback 1 s
        (roundCylinderPullback (H.terminalMetric P04) N.coordinate_map) z v w) := by
    funext z v w
    dsimp only [RoundCylinderTangent, TangentSpace] at v w ⊢
    simp only [RoundCylinderTranslation.pullback, B, RoundCylinderAffine.pullback,
      RoundCylinderTranslation.space, RoundCylinderAffine.space, one_mul]
    rw [← mul_assoc, div_mul_cancel₀ _ hQ.ne']
    simp only [Prod.eta]
    exact congrArg (fun a : ℝ => R * roundCylinderPullback (H.terminalMetric P04)
      N.coordinate_map (z.1, a + s) v w) (one_mul z.2).symm
  change RoundCylinderClose δ 0
    (fun z v w => R / Q * RoundCylinderTranslation.pullback s B z v w) at hclose
  rw [htensor] at hclose
  have hactual := N.affine_pullback_close (s := s) hsub'
    (H.terminalMetric P04) R hclose
  let K := N.affineWithMetric (by norm_num : (0 : ℝ) < 1) s hsub'
    (H.terminalMetric P04) (H.terminalConnection P04) hδ hδhalf q hR hactual
  refine ⟨K, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact N.affineWithMetric_central_sphere _ _ _ _ _ _ _ _ _ _
  · simpa only [one_mul] using
      N.affineWithMetric_carrier (by norm_num : (0 : ℝ) < 1) s hsub'
        (H.terminalMetric P04) (H.terminalConnection P04) hδ hδhalf q hR hactual
  · intro a b ha hb
    simpa only [one_mul] using
      N.affineWithMetric_region_of_bounds (by norm_num : (0 : ℝ) < 1) s hsub'
        (H.terminalMetric P04) (H.terminalConnection P04) hδ hδhalf q hR hactual ha hb

end PoincareConjecture.SingularTimeAssumptions
