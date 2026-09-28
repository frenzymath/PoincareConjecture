import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderParameterJets
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderIntrinsicJetBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy



theorem endAxialTranslation_comp_coordinate_contMDiffOn
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g) (j : ℕ) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (endAxialTranslation e j ∘ e.coordinate) (univ ×ˢ Ioi (0 : ℝ)) := by
  intro z hz
  have hs := endAxialTranslation_contMDiffAt e (j : ℝ) hz.2
    (add_pos_of_pos_of_nonneg hz.2 (Nat.cast_nonneg j))
  exact (hs.comp z (end_coordinate_contMDiffAt e hz.2)).contMDiffWithinAt



theorem partialFlow_endCylinder_intrinsicJetError_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    (e : StandardCylindricalEnd g0.metric)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (p₀ : endReferenceRegion e)
    {T : ℝ} (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc 0 T, ∀ q : UnitTwoSphere,
      ∀ r ∈ Icc (17 / 5 : ℝ) (23 / 5),
        roundCylinderJetErrorSquared t
          (roundCylinderPullback (F.flow.metric t)
            (endAxialTranslation e (k + 1 : ℕ) ∘ e.coordinate)) m (q, r) < ε ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_roundCylinderJetErrorSquared_bound_of_parametrizedJets_on_Icc
    hT.2.2 (J := Icc (17 / 5 : ℝ) (23 / 5)) isCompact_Icc m
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  choose N hN using fun j : Fin (m + 1) =>
    partialFlow_endCylinderParameterDifference_iteratedFDeriv_tendsto
      P E0 F e qH qA qS p₀ hT j hδ
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk t ht q r hr
  have hbound := hb t ht (F.flow.metric t) (isOpen_univ.prod isOpen_Ioi)
    (endAxialTranslation_comp_coordinate_contMDiffOn e (k + 1)) (q, r)
    ⟨mem_univ _, by change 0 < r; linarith [hr.1]⟩ hr δ hδ.le (fun j hj => ?_)
  · apply hbound.trans_lt
    calc
      C * δ ^ 2 < (C + 1) ^ 2 * δ ^ 2 :=
        mul_lt_mul_of_pos_right (by nlinarith [sq_nonneg C]) (sq_pos_of_pos hδ)
      _ = ((C + 1) * δ) ^ 2 := (mul_pow _ _ _).symm
      _ = ε ^ 2 := by
        congr 1
        dsimp [δ]
        field_simp
  · let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hN i k ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hk) t ht q r hr).le

end PoincareConjecture.M34
