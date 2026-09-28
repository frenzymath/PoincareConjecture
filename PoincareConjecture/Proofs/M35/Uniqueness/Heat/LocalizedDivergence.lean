import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletWeak

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

theorem schwartzMultiplier_product (a b : 𝓢(V, ℝ)) (u : L2) :
    schwartzMultiplier (schwartzProduct a b) u =
      schwartzMultiplier a (schwartzMultiplier b u) := by
  apply Lp.ext
  filter_upwards [schwartzMultiplier_coe (schwartzProduct a b) u,
    schwartzMultiplier_coe a (schwartzMultiplier b u), schwartzMultiplier_coe b u]
    with x hp ha hb
  rw [hp, ha, hb, schwartzProduct_apply, mul_assoc]

theorem schwartzMultiplier_commute (a b : 𝓢(V, ℝ)) (u : L2) :
    schwartzMultiplier a (schwartzMultiplier b u) =
      schwartzMultiplier b (schwartzMultiplier a u) := by
  apply Lp.ext
  filter_upwards [schwartzMultiplier_coe a (schwartzMultiplier b u),
    schwartzMultiplier_coe b u, schwartzMultiplier_coe b (schwartzMultiplier a u),
    schwartzMultiplier_coe a u] with x hab hb hba ha
  rw [hab, hb, hba, ha, mul_left_comm]

def localizedDivergenceSource (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ))
    (η : 𝓢(V, ℝ)) (u : dirichletForm K) (G : L2) : L2 :=
  schwartzMultiplier η G - ∑ i, ∑ j,
    (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} η)
      (schwartzMultiplier (A i j) (dirichletPartial K i u)) +
    (schwartzMultiplier (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} η))
      (dirichletPartial K j u) +
    schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
      (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} η)))
      (dirichletInclusion K u : L2)))

theorem localized_dirichlet_divergence (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (η : 𝓢(V, ℝ)) (hηK : tsupport η ⊆ K)
    (u : dirichletForm K) (G : L2)
    (heq : ∀ φ : supportedTests K, principalEnergy K A u (intoDirichletForm K φ) =
      inner ℝ G ((φ : 𝓢(V, ℝ)).toLp 2 volume)) :
    ∀ φ : 𝓢(V, ℝ),
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (localizedDirichletPartial K η u i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
          inner ℝ (localizedDivergenceSource K A η u G) (φ.toLp 2 volume) := by
  intro φ
  let ψ : supportedTests K := ⟨schwartzProduct η φ, fun x hx => by
    change η x * φ x = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hηK h)), zero_mul]⟩
  have hmain := heq ψ
  simp only [principalEnergy, dirichletPartial_into] at hmain
  dsimp only [ψ] at hmain
  simp only [lineDeriv_schwartzProduct_toLp, schwartzProduct_toLp,
    inner_add_right, Finset.sum_add_distrib] at hmain
  have hcut (i j : Fin n) := (dirichletPartial_weak K u j).mul _ _ _
    (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} η)) φ
  have hcutSum := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext (fun i => funext (fun j => hcut i j)))
  simp only [inner_add_left, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    schwartzMultiplier_product] at hcutSum
  simp only [localizedDirichletPartial, map_add, inner_add_left, Finset.sum_add_distrib,
    localizedDivergenceSource, inner_sub_left, sum_inner, inner_add_left]
  simp_rw [schwartzMultiplier_selfAdjoint] at hmain
  have hcomm (i j : Fin n) :
      inner ℝ (schwartzMultiplier (A i j) (schwartzMultiplier η (dirichletPartial K i u)))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume) =
      inner ℝ (dirichletPartial K i u) (schwartzMultiplier (A i j)
        (schwartzMultiplier η ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume))) := by
    rw [schwartzMultiplier_commute, schwartzMultiplier_selfAdjoint,
      schwartzMultiplier_selfAdjoint]
  simp_rw [hcomm]
  simp only [schwartzMultiplier_product] at hcutSum ⊢
  have hcross (i j : Fin n) :
      inner ℝ (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} η)
        (schwartzMultiplier (A i j) (dirichletPartial K i u))) (φ.toLp 2 volume) =
      inner ℝ (dirichletPartial K i u) (schwartzMultiplier (A i j)
        (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} η) (φ.toLp 2 volume))) := by
    rw [schwartzMultiplier_selfAdjoint, schwartzMultiplier_selfAdjoint]
  simp_rw [hcross]
  have hG := schwartzMultiplier_selfAdjoint η G (φ.toLp 2 volume)
  linarith only [hmain, hcutSum, hG]

end PoincareConjecture.M35.Uniqueness.Heat
