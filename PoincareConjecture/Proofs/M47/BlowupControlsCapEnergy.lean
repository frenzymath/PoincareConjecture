import PoincareConjecture.Proofs.M47.BlowupControlsCapLocalization
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJets
import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M47

local notation "E" => StandardCapSpace
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance capEnergyCoefficientNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capEnergyCoefficientSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

private theorem cap_bilinear_family_evaluation {J : Set ℝ}
    (A : ℝ × E → Bilin) (hA : ContDiffOn ℝ ∞ A (J ×ˢ univ))
    {U : Set E} (hU : IsOpen U)
    (X : Fin 2 → (y : E) → TangentSpace (𝓡 3) y)
    (hX : ∀ i, ContMDiffOn (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E)) ∞ (T% (X i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => A p (X 0 p.2) (X 1 p.2)) (J ×ˢ U) := by
  have hXi (i : Fin 2) : ContDiffOn ℝ ∞ (X i) U := by
    intro x hx
    have h := (Bundle.contMDiffAt_totalSpace.mp
      ((hX i).contMDiffAt (hU.mem_nhds hx))).2
    have hs : ContDiffAt ℝ ∞ (X i) x := by
      simpa using contMDiffAt_iff_contDiffAt.mp h
    exact hs.contDiffWithinAt
  have hXiJoint (i : Fin 2) : ContDiffOn ℝ ∞ (fun p : ℝ × E => X i p.2) (J ×ˢ U) :=
    (hXi i).comp contDiffOn_snd (fun _ hp => hp.2)
  have hscalar := ((hA.mono (prod_mono Subset.rfl (subset_univ U))).clm_apply
    (hXiJoint 0)).clm_apply (hXiJoint 1)
  have hid : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × E => (p.1, p.2)) (J ×ˢ U) :=
    contMDiffOn_fst.prodMk_space contMDiffOn_snd
  exact hscalar.contMDiffOn.comp hid (fun _ hp => hp)

theorem continuousOn_cap_global_comparison_energy {J : Set ℝ}
    (F : RicciFlow 3 E J) (A : ℝ × E → Bilin)
    (hA : ∀ t, ContDiff ℝ ∞ (fun y => A (t, y)))
    (hJoint : ContDiffOn ℝ ∞ A (J ×ˢ univ)) (m : ℕ) :
    ContinuousOn (fun p : ℝ × E => singularMetricJetErrorSquared
      (F.metric p.1) (F.connection p.1) (fun y v => A (p.1, y) (v 0) (v 1)) m p.2)
      (J ×ˢ univ) := by
  let C : ℝ × E → Bilin := fun p => A p - (F.metric p.1).euclideanCoefficients p.2
  have hC (t : ℝ) : ContDiff ℝ ∞ (fun y => C (t, y)) :=
    (hA t).sub (contDiff_iff_contDiffAt.mpr (F.metric t).contDiffAt_euclideanCoefficients)
  have hCJ : ContDiffOn ℝ ∞ C (J ×ˢ univ) :=
    hJoint.sub (M44.contDiffOn_euclideanCoefficients_within F)
  let T : ℝ → CovariantTensorEvaluation 3 E 2 := fun t y v => C (t, y) (v 0) (v 1)
  have hT (t : ℝ) : IsSmoothCovariantTensor (T t) := M36.comparison_bilinear_isSmooth (hC t)
  have hTime (U : Set E) (hU : IsOpen U)
      (X : Fin 2 → (y : E) → TangentSpace (𝓡 3) y)
      (hX : ∀ i, ContMDiffOn (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E)) ∞ (T% (X i)) U) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => T p.1 p.2 (fun i => X i p.2)) (J ×ˢ U) :=
    cap_bilinear_family_evaluation C hCJ hU X hX
  change ContinuousOn (fun p : ℝ × E => ∑ j ∈ Finset.range (m + 1),
    ((F.metric p.1).tensorNorm
      ((F.connection p.1).iteratedCovariantTensorDerivative (T p.1) j) p.2) ^ 2) (J ×ˢ univ)
  apply continuousOn_finsetSum
  intro j _
  have hsmooth (k : ℕ) (s : ℝ) :
      IsSmoothCovariantTensor ((F.connection s).iteratedCovariantTensorDerivative (T s) k) := by
    induction k with
    | zero => exact hT s
    | succ k ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative _ ih
  exact (M04.contMDiffOn_flow_tensorNorm_sq F
    (fun s => (F.connection s).iteratedCovariantTensorDerivative (T s) j)
    (fun s => hsmooth j s)
    (fun U hU X hX => M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F
      hT hTime j hU hX)).continuousOn

theorem continuousOn_cap_local_comparison_energy {J : Set ℝ}
    (F : RicciFlow 3 E J) {U : Set E} (hU : IsOpen U) (A : ℝ × E → Bilin)
    (hA : ∀ t, ContDiffOn ℝ ∞ (fun y => A (t, y)) U)
    (hJoint : ContDiffOn ℝ ∞ A (J ×ˢ U)) (m : ℕ) :
    ContinuousOn (fun p : ℝ × E => singularMetricJetErrorSquared
      (F.metric p.1) (F.connection p.1) (fun y v => A (p.1, y) (v 0) (v 1)) m p.2)
      (J ×ˢ U) := by
  intro p hp
  obtain ⟨B, hB, hBJ, V, hV, hpV, _hVU, heq⟩ :=
    exists_cap_coefficient_family_germ hU A hA hJoint hp.2
  have hcont := (continuousOn_cap_global_comparison_energy F B hB hBJ m
    p ⟨hp.1, mem_univ p.2⟩).mono (prod_mono Subset.rfl (subset_univ U))
  apply hcont.congr_of_eventuallyEq_of_mem (hx := hp)
  have hVnear : Prod.snd ⁻¹' V ∈ 𝓝 p :=
    continuous_snd.continuousAt.preimage_mem_nhds (hV.mem_nhds hpV)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hVnear] with q hq
  apply M44.singularMetricJetErrorSquared_congr_germ
  filter_upwards [hV.mem_nhds hq] with y hy
  funext v
  exact congrArg (fun B : Bilin => B (v 0) (v 1)) (heq q.1 y hy).symm

end PoincareConjecture.M47
