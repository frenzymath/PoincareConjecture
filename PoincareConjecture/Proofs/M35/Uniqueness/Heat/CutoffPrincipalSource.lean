import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFiniteJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def cutoffSupportedTest (K : Set V) (χ : 𝓢(V, ℝ)) (hχK : tsupport χ ⊆ K)
    (φ : 𝓢(V, ℝ)) : supportedTests K :=
  ⟨schwartzProduct χ φ, fun x hx => by
    change χ x * φ x = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hχK h)), zero_mul]⟩

theorem exists_cutoff_principal_source (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : dirichletForm K) {s : ℕ} (hu : HasInteriorWeakJets K u (s + 2)) :
    ∃ G : L2, HasFiniteWeakJet G s ∧ ∀ φ : 𝓢(V, ℝ),
      principalEnergy K A (intoDirichletForm K
        (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) u =
          inner ℝ G (φ.toLp 2 volume) := by
  have hp (i j : Fin n) : ∃ d : L2,
      HasWeakSchwartzDerivative
        (schwartzMultiplier (schwartzProduct χ (A i j)) (dirichletPartial K j u)) d
        (EuclideanSpace.single i (1 : ℝ)) ∧ HasFiniteWeakJet d s :=
    (hu.partial_product (s := s + 1) (schwartzProduct χ (A i j))
      hχ.mul_right (tsupport_mul_subset_left.trans hχK) j).exists_derivative i
  choose d hd hdjet using hp
  let cross : Fin n → Fin n → L2 := fun i j =>
    schwartzMultiplier (schwartzProduct (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (A i j))
      (dirichletPartial K j u)
  have hcross (i j : Fin n) : HasFiniteWeakJet (cross i j) s := by
    have hχd : HasCompactSupport
        ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) :=
      hχ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
    have hχdK : tsupport ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) ⊆
        interior K := (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hχK
    exact (hu.partial_product (s := s + 1)
      (schwartzProduct (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (A i j))
      hχd.mul_right (tsupport_mul_subset_left.trans hχdK) j).mono (Nat.le_succ s)
  refine ⟨∑ i, ∑ j, (cross i j - d i j),
    HasFiniteWeakJet.sum _ (fun i => HasFiniteWeakJet.sum _
      (fun j => (hcross i j).sub (hdjet i j))), ?_⟩
  intro φ
  simp only [principalEnergy, dirichletPartial_into, cutoffSupportedTest,
    lineDeriv_schwartzProduct_toLp, map_add, inner_add_left,
    sum_inner, inner_sub_left]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hdij := hd i j φ
  simp only [schwartzMultiplier_product] at hdij
  have hmain : inner ℝ (schwartzMultiplier (A i j)
      (schwartzMultiplier χ ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume)))
        (dirichletPartial K j u) =
      -inner ℝ (d i j) (φ.toLp 2 volume) := by
    rw [schwartzMultiplier_selfAdjoint, schwartzMultiplier_selfAdjoint, real_inner_comm]
    exact (neg_eq_iff_eq_neg.mpr hdij).symm
  have hother : inner ℝ (schwartzMultiplier (A i j)
      (schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (φ.toLp 2 volume)))
        (dirichletPartial K j u) = inner ℝ (cross i j) (φ.toLp 2 volume) := by
    simp only [cross, schwartzMultiplier_product]
    rw [schwartzMultiplier_selfAdjoint, schwartzMultiplier_selfAdjoint, real_inner_comm]
  rw [hmain, hother]
  ring

end PoincareConjecture.M35.Uniqueness.Heat
