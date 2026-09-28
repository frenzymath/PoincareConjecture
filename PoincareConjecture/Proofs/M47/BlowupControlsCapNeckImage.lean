import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckComparison
import PoincareConjecture.Proofs.M34.Standard.CapNeckImageIdentities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem exists_cap_neck_image_of_normalized_comparison
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace E₃ M] [ChartedSpace E₃ X]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (N : EpsilonNeck g) (D : LeviCivitaData h)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hsource : N.carrier ⊆ phi.source)
    (hR : 0 < D.scalarCurvature (phi N.center))
    (hclose : RoundCylinderClose N.epsilon 0 (fun z u u' =>
      D.scalarCurvature (phi N.center) * roundCylinderPullback h (phi ∘ N.coordinate_map) z u u')) :
    ∃ E : EpsilonNeck h,
      E.epsilon = N.epsilon ∧ E.center = phi N.center ∧ E.connection = D ∧
      E.carrier = phi '' N.carrier ∧ E.central_sphere = phi '' N.central_sphere ∧
      E.coordinate_map = phi ∘ N.coordinate_map ∧
      E.coordinate_inverse = N.coordinate_inverse ∘ phi.symm ∧
      ∀ a b : ℝ, -N.epsilon⁻¹ ≤ a → b ≤ N.epsilon⁻¹ →
        E.region a b = phi '' N.region a b := by
  classical
  have hcenter := N.center_on_central_sphere
  rw [N.central_sphere_eq] at hcenter
  obtain ⟨⟨q, z⟩, hz, hq⟩ := hcenter
  have hz0 : z = 0 := hz.2
  subst z
  let r := D.scalarCurvature (phi N.center) ^ (-1 / 2 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hR _
  have hscale : r⁻¹ ^ 2 = D.scalarCurvature (phi N.center) := by
    dsimp only [r]
    rw [inv_pow, ← Real.rpow_mul_natCast hR.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  have hdom : Ioo (-N.epsilon⁻¹ + 0) (N.epsilon⁻¹ + 0) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by simp only [add_zero]; exact Subset.rfl
  have hsource' : N.region (-N.epsilon⁻¹ + 0) (N.epsilon⁻¹ + 0) ⊆ phi.source :=
    fun _ hx => hsource hx.1
  have hR' : 0 < D.scalarCurvature (phi (N.coordinate_map (q, 0))) := by
    simpa only [hq] using hR
  have hr' : r = D.scalarCurvature (phi (N.coordinate_map (q, 0))) ^ (-1 / 2 : ℝ) := by
    rw [hq]
  have hclose' : RoundCylinderClose N.epsilon 0 (fun z u u' => r⁻¹ ^ 2 *
      roundCylinderPullback h (fun z => phi (N.coordinate_map (z.1, z.2 + 0))) z u u') := by
    simpa only [add_zero, hscale, Function.comp_def, Prod.mk.eta] using hclose
  let E := N.imageShift phi.toOpenPartialHomeomorph phi.contMDiffOn_toFun
    phi.contMDiffOn_invFun N.epsilon_pos N.epsilon_lt_half hdom hsource' D q hr hR' hr' hclose'
  have hsets := N.imageShift_zero_sets phi.toOpenPartialHomeomorph phi.contMDiffOn_toFun
    phi.contMDiffOn_invFun N.epsilon_pos N.epsilon_lt_half hdom hsource' D q hr hR' hr'
    hclose' rfl rfl
  refine ⟨E, rfl, ?_, rfl, hsets.1, hsets.2, ?_, ?_, ?_⟩
  · exact congrArg phi hq
  · funext z
    change phi (N.coordinate_map (z.1, z.2 + 0)) = phi (N.coordinate_map z)
    simp only [add_zero]
  · funext x
    change ((N.coordinate_inverse (phi.symm x)).1,
      (N.coordinate_inverse (phi.symm x)).2 - 0) = N.coordinate_inverse (phi.symm x)
    simp only [sub_zero]
  · intro a b ha hb
    convert N.imageShift_region phi.toOpenPartialHomeomorph
      phi.contMDiffOn_toFun phi.contMDiffOn_invFun N.epsilon_pos N.epsilon_lt_half hdom
      hsource' D q hr hR' hr' hclose' a b ha hb using 1
    simp only [add_zero]
    rfl

theorem exists_actualCap_image_neck_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A s : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hstheta : s ≤ theta)
    (N : EpsilonNeck (standard.flow.metric s))
    (hconnection : N.connection = standard.flow.connection s)
    (hsource : N.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (hs : s ∈ J),
      let phi := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      ∃ E : EpsilonNeck (F.metric (t + s / Q)),
        E.epsilon = N.epsilon ∧ E.center = phi N.center ∧
        E.connection = F.connection (t + s / Q) ∧
        E.carrier = phi '' N.carrier ∧ E.central_sphere = phi '' N.central_sphere ∧
        E.coordinate_map = phi ∘ N.coordinate_map ∧
        E.coordinate_inverse = N.coordinate_inverse ∘ phi.symm ∧
        ∀ a b : ℝ, -N.epsilon⁻¹ ≤ a → b ≤ N.epsilon⁻¹ →
          E.region a b = phi '' N.region a b := by
  obtain ⟨eta0, heta0, hcompare⟩ := exists_actualCap_neck_normalized_comparison_tolerance
    standard htheta hA hstheta N hconnection hsource
  refine ⟨eta0, heta0, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetasmall comparison hh hs
  have h := hcompare F hinitial S hS t hT hn i J U e initial eta heta hetasmall
    comparison hh hs
  apply exists_cap_neck_image_of_normalized_comparison N
    (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2)))
    (actualCapSliceChart e initial comparison s hs) _ h.1 h.2
  rw [actualCapSliceChart_source, hinitial]
  exact hsource

end PoincareConjecture.M47
