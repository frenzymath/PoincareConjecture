import PoincareConjecture.Proofs.M32.Claim11_34.PrescribedSphere
import PoincareConjecture.Proofs.M32.Claim11_34.HornSeparation
import PoincareConjecture.Proofs.M32.Claim11_32.HornBalls
import PoincareConjecture.Proofs.M32.Mathlib.ProductCompactBoundary
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.MonotoneContinuity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

private theorem cylinder_not_isCompact_of_frontier_subset_middleSphere
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {U K : Set M} (C : OpenCylinderModel U) (hU : IsOpen U) (hKU : K ⊆ U)
    (hint : (interior K).Nonempty) (hfront : frontier K ⊆ C.middleSphere) :
    ¬ IsCompact K := by
  let a := affineHomeomorph (2 : ℝ) (-1) (by norm_num)
  have ha : a '' Ioo (0 : ℝ) 1 = Ioo (-1 : ℝ) 1 := by
    change affineHomeomorph (2 : ℝ) (-1) _ '' Ioo (0 : ℝ) 1 = _
    convert affineHomeomorph_image_Ioo (2 : ℝ) (-1) 0 1 (by norm_num) using 1
    norm_num
  let b : Ioo (0 : ℝ) 1 ≃ₜ ℝ :=
    ((a.image (Ioo (0 : ℝ) 1)).trans (Homeomorph.setCongr ha)).trans
      (orderIsoIooNegOneOne ℝ).symm.toHomeomorph
  let half : Ioo (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  let rho : U ≃ₜ UnitTwoSphere × ℝ :=
    C.homeomorph.symm.trans ((Homeomorph.refl UnitTwoSphere).prodCongr b)
  apply not_isCompact_of_product_chart_frontier hU hKU rho hint
    (a := b half)
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨⟨q, t⟩, ⟨_, ht⟩, hpoint⟩ := hfront hx
  have ht' : t = (1 / 2 : ℝ) := ht
  subst t
  have hcoordinate : C.homeomorph (q, half) = x := by
    apply Subtype.ext
    exact (C.coordinate_eq (q, half)).trans hpoint
  have hinverse : C.homeomorph.symm x = (q, half) := by
    rw [← hcoordinate, C.homeomorph.symm_apply_apply]
  change b (C.homeomorph.symm x).2 = b half
  rw [hinverse]

theorem exists_horn_neck_nonfilling_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      epsilon₀ ≤ 1 / (64 * Real.pi) ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
        (E : GeneralizedFlowExtension F T) (A : RepairedNeckCapTopologyTheory.{u}),
        0 < epsilon → epsilon ≤ epsilon₀ → epsilon ≤ A.epsilon₀ →
        ∀ (horn : StrongHorn E epsilon)
          (N : GeneralizedStrongNeck E.extended T epsilon),
          N.center ∈ horn.carrier →
          N.coordinate_map '' (univ ×ˢ Icc (-(32 * Real.pi)) (32 * Real.pi)) ⊆
            horn.carrier →
          ∀ K : Set (E.extended.slice T).carrier, K ⊆ horn.carrier →
            (interior K).Nonempty → frontier K ⊆ N.central_sphere → ¬ IsCompact K := by
  obtain ⟨epsilon₁, hpos₁, hsmall₁, hfixed₁, htransport⟩ :=
    exists_tube_prescribed_sphere_compact_transport.{u}
  obtain ⟨epsilon₂, hpos₂, _, htube⟩ := exists_horn_neckCap_tube_threshold.{u}
  refine ⟨min epsilon₁ epsilon₂, lt_min hpos₁ hpos₂,
    (min_le_left _ _).trans hsmall₁, (min_le_left _ _).trans hfixed₁, ?_⟩
  intro F T epsilon E A hepos he hA horn N hcenter hcollar K hK hint hfront
  have he₁ : epsilon ≤ epsilon₁ := he.trans (min_le_left _ _)
  have hhalf : epsilon < 1 / 2 := (he₁.trans hsmall₁).trans_lt (by norm_num)
  let P := spatialNeck N hhalf
  obtain ⟨C⟩ := htube E A hepos (he.trans (min_le_right _ _)) hA horn
  have hhorn : horn.carrier ⊆ C.tube.carrier := C.contains_X
  have hC : C.tube.epsilon ≤ epsilon₁ := by
    rw [C.epsilon_eq]
    exact he₁
  have hPU : P.closedCollar (32 * Real.pi) ⊆ C.tube.carrier :=
    hcollar.trans hhorn
  obtain ⟨e, _, _, _, _, hsphere, heU⟩ := htransport C.tube P hC he₁
    (hhorn hcenter) hPU
  have hKU : e '' K ⊆ C.tube.carrier := by
    rw [← heU]
    exact image_mono (hK.trans hhorn)
  have hint' : (interior (e '' K)).Nonempty := by
    rw [← e.image_interior]
    exact hint.image e
  have hfront' : frontier (e '' K) ⊆ C.tube.cylinder.middleSphere := by
    rw [← e.image_frontier, ← hsphere]
    exact image_mono hfront
  intro hcompact
  exact cylinder_not_isCompact_of_frontier_subset_middleSphere C.tube.cylinder
    C.tube.carrier_open hKU hint' hfront' (hcompact.image e.continuous)

private theorem strongNeck_fixedCollar_subset_ball
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) (hhalf : epsilon < 1 / 2)
    (hsmall : epsilon ≤ 1 / (64 * Real.pi)) :
    N.coordinate_map '' (univ ×ˢ Icc (-(32 * Real.pi)) (32 * Real.pi)) ⊆
      (F.metric t).ball N.center
        ((66 * Real.pi + 1) / Real.sqrt ((F.connection t).scalarCurvature N.center)) := by
  let P := spatialNeck N hhalf
  have hr : 32 * Real.pi < P.epsilon⁻¹ := by
    have hbound : 64 * Real.pi ≤ epsilon⁻¹ := by
      simpa only [one_div, inv_inv] using inv_anti₀ N.epsilon_pos hsmall
    change 32 * Real.pi < epsilon⁻¹
    linarith [Real.pi_pos]
  intro y hy
  have hyP : y ∈ P.closedCollar (32 * Real.pi) := hy
  have hcarrier := P.closedCollar_subset_carrier hr hyP
  have hheight : |(P.coordinate_inverse y).2| ≤ 32 * Real.pi := by
    obtain ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩ := hyP
    have hdomain : (q, a) ∈ P.cylinderDomain :=
      ⟨mem_univ _, by constructor <;> linarith [ha.1, ha.2]⟩
    rw [P.coordinate_inverse_coordinate_map hdomain]
    exact abs_le.mpr ha
  have hdist := P.edist_central_sphere_le_of_mem_carrier hcarrier
    P.center_on_central_sphere
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have hcomm : (F.metric t).edist P.center y = (F.metric t).edist y P.center :=
    Manifold.riemannianEDist_comm
  have hupper : (F.metric t).edist N.center y ≤
      ENNReal.ofReal ((66 * Real.pi) * N.scale) := by
    change (F.metric t).edist P.center y ≤ _
    rw [hcomm]
    apply hdist.trans
    apply ENNReal.ofReal_le_ofReal
    change (2 * Real.pi + 2 * |(P.coordinate_inverse y).2|) * N.scale ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hheight N.scale_pos.le]
  have hscale : N.scale =
      (Real.sqrt ((F.connection t).scalarCurvature N.center))⁻¹ := by
    rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, Real.sqrt_eq_rpow]
  have hstrict : (66 * Real.pi) * N.scale < (66 * Real.pi + 1) * N.scale := by
    nlinarith [N.scale_pos]
  have hradius : (66 * Real.pi + 1) * N.scale =
      (66 * Real.pi + 1) / Real.sqrt ((F.connection t).scalarCurvature N.center) := by
    rw [hscale, div_eq_mul_inv]
  change (F.metric t).edist N.center y < ENNReal.ofReal _
  apply hupper.trans_lt
  rw [← hradius]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by positivity) N.scale_pos)).mpr hstrict

theorem terminalBlowupSequence_eventually_horn_neck_no_filling :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      epsilon₀ ≤ 1 / (64 * Real.pi) ∧
      ∀ {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
        [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
        [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
        [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
        [∀ k, SecondCountableTopology (M k)]
        {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
        (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
        (Q : ∀ k, SingularLimitConclusion (H k))
        (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
        (_hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
        (_hdiv : Tendsto (fun k =>
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
            ∀ᶠ k : ℕ in atTop, ∀ K0 : Set ((Q k).extension.extended.slice (T k)).carrier,
              K0 ⊆ (horn k).carrier → (interior K0).Nonempty →
              frontier K0 ⊆ (N k).central_sphere → ¬ IsCompact K0 := by
  obtain ⟨epsilon₀, hpos₀, hsmall₀, hfixed₀, hnoFill⟩ :=
    exists_horn_neck_nonfilling_threshold.{u}
  refine ⟨epsilon₀, hpos₀, hsmall₀, hfixed₀, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H Q x hpos hdiv hM04 A K B accuracy
    hK hB hcutoff hconstant hsmall hA horn hx hboundary N hcenter
  have hballs := terminalBlowupSequence_baseBalls_subset_horns H Q x hpos hdiv
    hM04 hK hB hcutoff hconstant horn hx hboundary
    (66 * Real.pi + 1) (by positivity)
  filter_upwards [hballs] with k hk
  have hhalf : accuracy k < 1 / 2 := ((hsmall k).trans hsmall₀).trans_lt (by norm_num)
  have hcollar : (N k).coordinate_map ''
      (univ ×ˢ Icc (-(32 * Real.pi)) (32 * Real.pi)) ⊆ (horn k).carrier := by
    apply subset_trans ?_ hk
    intro y hy
    have hball := strongNeck_fixedCollar_subset_ball (N k) hhalf
      ((hsmall k).trans hfixed₀) hy
    change ((Q k).extension.extended.metric (T k)).edist (N k).center y <
      ENNReal.ofReal ((66 * Real.pi + 1) /
        Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature
          (N k).center)) at hball
    change ((Q k).extension.extended.metric (T k)).edist (x k) y <
      ENNReal.ofReal ((66 * Real.pi + 1) /
        Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))
    simpa only [hcenter k] using hball
  apply hnoFill (Q k).extension A (N k).epsilon_pos (hsmall k) (hA k) (horn k) (N k)
  · rw [hcenter k]
    exact hx k
  · exact hcollar

end PoincareConjecture.M32
