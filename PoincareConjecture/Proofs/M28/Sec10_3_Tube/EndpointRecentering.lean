import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckCenterConnector
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapCoreConnector
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar











noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28



def endpointConnectorBudget (epsilon C : ℝ) : ℝ :=
  max C 2 + 8 * standardSpherePathCeiling + 4 / epsilon



theorem endpointConnectorBudget_pos {epsilon C : ℝ} (hepsilon : 0 < epsilon) :
    0 < endpointConnectorBudget epsilon C := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hL := standardSpherePathCeiling_pos
  have hfrac : 0 < 4 / epsilon := div_pos (by norm_num) hepsilon
  unfold endpointConnectorBudget
  linarith

private theorem source_endpoint_scalar_lower {C Q R : ℝ} (hQ : 0 < Q)
    (hsource : R = 8 * Q ∨ 32 * (max C 2) ^ 4 * Q < R) : 8 * Q ≤ R := by
  rcases hsource with hlow | hhigh
  · rw [hlow]
  · have hB : 2 ≤ max C 2 := le_max_right C 2
    have hsq : 1 ≤ (max C 2) ^ 2 := by
      nlinarith only [sq_nonneg (max C 2 - 1), hB]
    have hpow : 1 ≤ (max C 2) ^ 4 := by
      nlinarith only [sq_nonneg ((max C 2) ^ 2 - 1), hsq]
    have hcoeff : (8 : ℝ) ≤ 32 * (max C 2) ^ 4 := by nlinarith only [hpow]
    exact (mul_le_mul_of_nonneg_right hcoeff hQ.le).trans hhigh.le

private theorem endpoint_scalar_readouts {C Q R S : ℝ}
    (hupper : S ≤ max C 2 * R) (hlower : R ≤ max C 2 * S) :
    (R = 8 * Q → S ≤ 8 * max C 2 * Q) ∧
      (32 * (max C 2) ^ 4 * Q < R → 32 * (max C 2) ^ 3 * Q < S) := by
  constructor
  · intro hR
    calc
      S ≤ max C 2 * R := hupper
      _ = 8 * max C 2 * Q := by rw [hR]; ring
  · intro hR
    have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
    apply (mul_lt_mul_iff_right₀ hB).mp
    calc
      max C 2 * (32 * (max C 2) ^ 3 * Q) = 32 * (max C 2) ^ 4 * Q := by ring
      _ < R := hR
      _ ≤ max C 2 * S := hlower

private theorem exists_reverse_unit_connector
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] (g : RiemannianMetric 3 M)
    {U : Set M} {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1))
    (hγU : MapsTo γ (Icc (0 : ℝ) 1) U) :
    ∃ δ : ℝ → M, δ 0 = γ 1 ∧ δ 1 = γ 0 ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 δ (Icc (0 : ℝ) 1) ∧
      MapsTo δ (Icc (0 : ℝ) 1) U ∧
      g.pathELength δ 0 1 = g.pathELength γ 0 1 := by
  have hreverse : MapsTo (fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2]
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun t : ℝ => 1 - t) :=
    contMDiff_const.sub contMDiff_id
  refine ⟨γ ∘ (fun t : ℝ => 1 - t), by simp, by simp,
    hγ.comp hsmooth.contMDiffOn hreverse, hγU.comp hreverse, ?_⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 3) (γ ∘ (fun t : ℝ => 1 - t)) 0 1 =
    Manifold.pathELength (𝓡 3) γ 0 1
  simpa only [sub_self, sub_zero] using
    (Manifold.pathELength_comp_of_antitoneOn (I := 𝓡 3) (γ := γ)
      (f := fun t : ℝ => 1 - t) zero_le_one
      (fun _ _ _ _ h => sub_le_sub_left h 1)
      ((differentiable_const (1 : ℝ)).sub differentiable_id).differentiableOn
      (by simpa only [sub_self, sub_zero] using hγ.mdifferentiableOn one_ne_zero))




theorem exists_neck_endpoint_recentering_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (epsilon C : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (N : EpsilonNeck g) (Q : ℝ) (p : M),
        0 < Q → N.epsilon = epsilon → p ∈ N.carrier →
        (D.scalarCurvature p = 8 * Q ∨
          32 * (max C 2) ^ 4 * Q < D.scalarCurvature p) →
        0 < D.scalarCurvature N.center ∧
        D.scalarCurvature N.center ≤ max C 2 * D.scalarCurvature p ∧
        D.scalarCurvature p ≤ max C 2 * D.scalarCurvature N.center ∧
        N.scale ≤ Q ^ (-1 / 2 : ℝ) ∧
        (D.scalarCurvature p = 8 * Q →
          D.scalarCurvature N.center ≤ 8 * max C 2 * Q) ∧
        (32 * (max C 2) ^ 4 * Q < D.scalarCurvature p →
          32 * (max C 2) ^ 3 * Q < D.scalarCurvature N.center) ∧
        (∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = N.center ∧
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
          MapsTo γ (Icc (0 : ℝ) 1) N.carrier ∧
          g.pathELength γ 0 1 <
            ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ))) ∧
        (∃ γ : ℝ → M, γ 0 = N.center ∧ γ 1 = p ∧
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
          MapsTo γ (Icc (0 : ℝ) 1) N.carrier ∧
          g.pathELength γ 0 1 <
            ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ))) := by
  obtain ⟨epsilon₀, hpos, hsmall, hratio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C hepsilon hsmall' M _ _ _ _ g D N Q p hQ hNepsilon hp hsource
  have hP := source_endpoint_scalar_lower hQ hsource
  have hPpos : 0 < D.scalarCurvature p := by linarith only [hP, hQ]
  have hc : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have hcpos : 0 < D.scalarCurvature N.center := by
    rw [← N.connection.scalarCurvature_eq_m28 D N.center]
    exact N.scalar_center_pos
  have hNsmall : N.epsilon ≤ epsilon₀ := hNepsilon ▸ hsmall'
  have hcenter := hratio M g D N hNsmall N.center hc p hp
  have hpoint := hratio M g D N hNsmall p hp N.center hc
  have hupper : D.scalarCurvature N.center ≤ max C 2 * D.scalarCurvature p :=
    hcenter.trans (mul_le_mul_of_nonneg_right (le_max_right C 2) hPpos.le)
  have hlower : D.scalarCurvature p ≤ max C 2 * D.scalarCurvature N.center :=
    hpoint.trans (mul_le_mul_of_nonneg_right (le_max_right C 2) hcpos.le)
  have hQcenter : Q ≤ D.scalarCurvature N.center := by
    linarith only [hQ, hP, hpoint]
  have hscale : N.scale ≤ Q ^ (-1 / 2 : ℝ) := by
    rw [N.scale_eq_scalar, N.connection.scalarCurvature_eq_m28 D N.center]
    exact Real.rpow_le_rpow_of_nonpos hQ hQcenter (by norm_num)
  have hL := standardSpherePathCeiling_pos
  have hinv := inv_pos.mpr hepsilon
  have hcoeff : 0 ≤ 2 * epsilon⁻¹ + 4 * standardSpherePathCeiling := by positivity
  have hbudget : 2 * epsilon⁻¹ + 4 * standardSpherePathCeiling ≤
      endpointConnectorBudget epsilon C := by
    have hB : 2 ≤ max C 2 := le_max_right C 2
    unfold endpointConnectorBudget
    rw [div_eq_mul_inv]
    linarith only [hB, hL, hinv]
  obtain ⟨γ, hγ0, hγ1, hγ, hγN, hγlen⟩ := exists_neck_center_connector N hp
  rw [hNepsilon] at hγlen
  have hγbound : g.pathELength γ 0 1 <
      ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ)) := by
    apply hγlen.trans_le
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left hscale hcoeff).trans
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hQ.le _))
  obtain ⟨δ, hδ0, hδ1, hδ, hδN, hδlen⟩ := exists_reverse_unit_connector g hγ hγN
  obtain ⟨hlow, hhigh⟩ := endpoint_scalar_readouts (Q := Q) hupper hlower
  refine ⟨hcpos, hupper, hlower, hscale, hlow, hhigh,
    ⟨γ, hγ0, hγ1, hγ, hγN, hγbound⟩,
    ⟨δ, hδ0.trans hγ1, hδ1.trans hγ0, hδ, hδN, ?_⟩⟩
  rw [hδlen]
  exact hγbound




theorem exists_cap_endpoint_recentering
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (K : CapCertificate g) (D : LeviCivitaData g)
    {epsilon C Q : ℝ} (hepsilon : 0 < epsilon) (hK : K.cap_constant ≤ C)
    (hQ : 0 < Q) {p : M} (hp : p ∈ K.carrier)
    (hsource : D.scalarCurvature p = 8 * Q ∨
      32 * (max C 2) ^ 4 * Q < D.scalarCurvature p) :
    ∃ c ∈ K.core,
      0 < D.scalarCurvature c ∧
      D.scalarCurvature c < max C 2 * D.scalarCurvature p ∧
      D.scalarCurvature p < max C 2 * D.scalarCurvature c ∧
      (D.scalarCurvature p = 8 * Q → D.scalarCurvature c ≤ 8 * max C 2 * Q) ∧
      (32 * (max C 2) ^ 4 * Q < D.scalarCurvature p →
        32 * (max C 2) ^ 3 * Q < D.scalarCurvature c) ∧
      (∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = c ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
        MapsTo γ (Icc (0 : ℝ) 1) K.carrier ∧
        g.pathELength γ 0 1 <
          ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ))) ∧
      (∃ γ : ℝ → M, γ 0 = c ∧ γ 1 = p ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
        MapsTo γ (Icc (0 : ℝ) 1) K.carrier ∧
        g.pathELength γ 0 1 <
          ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ))) := by
  have hP := source_endpoint_scalar_lower hQ hsource
  have hQp : Q ≤ D.scalarCurvature p := by linarith only [hP, hQ]
  obtain ⟨c, hc, hcpos, hupper, hlower, hforward, hbackward⟩ :=
    K.exists_core_connectors D (hK.trans (le_max_left C 2)) hQ hp hQp
  have hbudget : max C 2 ≤ endpointConnectorBudget epsilon C := by
    have hL := standardSpherePathCeiling_pos
    have hfrac : 0 < 4 / epsilon := div_pos (by norm_num) hepsilon
    unfold endpointConnectorBudget
    linarith only [hL, hfrac]
  have hceiling : ENNReal.ofReal (max C 2 * Q ^ (-1 / 2 : ℝ)) ≤
      ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ)) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hQ.le _))
  obtain ⟨hlow, hhigh⟩ := endpoint_scalar_readouts (Q := Q) hupper.le hlower.le
  obtain ⟨γ, hγ0, hγ1, hγ, hγK, hγlen⟩ := hforward
  obtain ⟨δ, hδ0, hδ1, hδ, hδK, hδlen⟩ := hbackward
  exact ⟨c, hc, hcpos, hupper, hlower, hlow, hhigh,
    ⟨γ, hγ0, hγ1, hγ, hγK, hγlen.trans_le hceiling⟩,
    ⟨δ, hδ0, hδ1, hδ, hδK, hδlen.trans_le hceiling⟩⟩

end PoincareConjecture.M28
