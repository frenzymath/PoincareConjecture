import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousInteriorJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffPrincipalSource









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_continuous_cutoff_principal_source (K : Set V)
    (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) {s : ℕ}
    (hA : ∀ i j w, w.length ≤ s + 1 →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t i j))))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : ι → dirichletForm K) (hu : HasContinuousInteriorJets K u (s + 2)) :
    ∃ G : ι → L2, HasContinuousWeakJet G s ∧ ∀ t (φ : 𝓢(V, ℝ)),
      principalEnergy K (A t) (intoDirichletForm K
        (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) (u t) =
          inner ℝ (G t) (φ.toLp 2 volume) := by
  have hp (i j : Fin n) : ∃ d : ι → L2,
      (∀ t, HasWeakSchwartzDerivative
        (schwartzMultiplier (A t i j) (schwartzMultiplier χ (dirichletPartial K j (u t))))
          (d t) (EuclideanSpace.single i (1 : ℝ))) ∧ HasContinuousWeakJet d s :=
    ((hu.partial_product (s := s + 1) χ hχ hχK j).mul (fun t => A t i j)
      (hA i j)).exists_derivative i
  choose d hd hdjet using hp
  let cross : Fin n → Fin n → ι → L2 := fun i j t =>
    schwartzMultiplier (A t i j)
      (schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (dirichletPartial K j (u t)))
  have hcross (i j : Fin n) : HasContinuousWeakJet (cross i j) s := by
    have hχd : HasCompactSupport
        ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) :=
      hχ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
    have hχdK : tsupport ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) ⊆
        interior K := (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hχK
    exact ((hu.partial_product (s := s + 1)
      (∂_{EuclideanSpace.single i (1 : ℝ)} χ) hχd hχdK j).mono (Nat.le_succ s)).mul
        (fun t => A t i j) (fun w hw => hA i j w (hw.trans (Nat.le_succ s)))
  refine ⟨fun t => ∑ i, ∑ j, (cross i j t - d i j t),
    HasContinuousWeakJet.sum _ (fun i => HasContinuousWeakJet.sum _
      (fun j => (hcross i j).sub (hdjet i j))), ?_⟩
  intro t φ
  simp only [principalEnergy, dirichletPartial_into, cutoffSupportedTest,
    lineDeriv_schwartzProduct_toLp, map_add, inner_add_left, sum_inner, inner_sub_left]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hdij := hd i j t φ
  have hmain : inner ℝ (schwartzMultiplier (A t i j)
      (schwartzMultiplier χ ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume)))
        (dirichletPartial K j (u t)) = -inner ℝ (d i j t) (φ.toLp 2 volume) := by
    rw [schwartzMultiplier_selfAdjoint, schwartzMultiplier_selfAdjoint, real_inner_comm]
    rw [schwartzMultiplier_commute χ (A t i j)]
    exact (neg_eq_iff_eq_neg.mpr hdij).symm
  have hother : inner ℝ (schwartzMultiplier (A t i j)
      (schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (φ.toLp 2 volume)))
        (dirichletPartial K j (u t)) = inner ℝ (cross i j t) (φ.toLp 2 volume) := by
    simp only [cross]
    rw [schwartzMultiplier_selfAdjoint, schwartzMultiplier_selfAdjoint, real_inner_comm,
      schwartzMultiplier_commute]
  rw [hmain, hother]
  ring

end PoincareConjecture.M35.Uniqueness.Heat
