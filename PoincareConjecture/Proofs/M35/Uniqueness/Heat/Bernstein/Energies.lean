import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatQuadratic
import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

def vectorHeatCovectorJet {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    (X : ℝ → StandardCapSpace → StandardCapSpace) (m : ℕ) (t : ℝ) :
    CovariantTensorEvaluation 3 StandardCapSpace (1 + m) :=
  (G.flow.connection t).iteratedCovariantTensorDerivative
    (killingCovector (G.flow.metric t) (X t)) m

def vectorHeatJetEnergy {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    (X : ℝ → StandardCapSpace → StandardCapSpace) (m : ℕ) (t : ℝ)
    (x : StandardCapSpace) : ℝ :=
  ((G.flow.metric t).tensorNorm (vectorHeatCovectorJet G X m t) x) ^ 2

theorem vectorHeatCovectorJet_smooth {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ t, ContDiff ℝ ∞ (X t)) (m : ℕ) (t : ℝ) :
    IsSmoothCovariantTensor (vectorHeatCovectorJet G X m t) := by
  induction m with
  | zero => exact isSmoothCovariantTensor_killingCovector _ _ (hX t)
  | succ m ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative _ ih

theorem vectorHeatJetEnergy_nonneg {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (X : ℝ → StandardCapSpace → StandardCapSpace)
    (m : ℕ) (t : ℝ) (x : StandardCapSpace) : 0 ≤ vectorHeatJetEnergy G X m t x :=
  sq_nonneg _

theorem vectorHeatJetEnergy_zero {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (X : ℝ → StandardCapSpace → StandardCapSpace)
    (t : ℝ) (x : StandardCapSpace) :
    vectorHeatJetEnergy G X 0 t x = (G.flow.metric t).inner x (X t x) (X t x) :=
  killingCovector_normSq _ _ _

theorem vectorHeatJetEnergy_positive_joint {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (hG : 0 < G.lifetime)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ t, ContDiff ℝ ∞ (X t))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ))
    (m : ℕ) : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry (vectorHeatJetEnergy G X m)) (Ioo 0 G.lifetime ×ˢ univ) := by
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
    (K := Ioo 0 G.lifetime) Ioo_subset_Ico_self ordConnected_Ioo
    (show (Ioo 0 G.lifetime).Nontrivial from
      ⟨G.lifetime / 3, ⟨by linarith, by linarith⟩,
        2 * G.lifetime / 3, ⟨by linarith, by linarith⟩, by linarith⟩)
  have hα (s) := isSmoothCovariantTensor_killingCovector (G.flow.metric s) (X s) (hX s)
  apply M04.contMDiffOn_flow_tensorNorm_sq F (vectorHeatCovectorJet G X m)
    (vectorHeatCovectorJet_smooth G X hX m)
  intro U hU Y hY
  exact M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F hα
    (killingCovector_joint_flow F X hJoint) m hU hY

theorem vectorHeatJetEnergy_space_smooth {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ t, ContDiff ℝ ∞ (X t)) (m : ℕ) (t : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (vectorHeatJetEnergy G X m t) :=
  M04.contMDiff_tensorNorm_sq _ (vectorHeatCovectorJet_smooth G X hX m t)

end PoincareConjecture.M35.Uniqueness
