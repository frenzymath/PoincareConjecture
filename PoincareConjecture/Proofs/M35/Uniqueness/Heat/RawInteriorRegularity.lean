import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorSecondDerivatives
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.VectorDivergence
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawStrongHeat











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_raw_compact_heat_interior_secondDerivatives
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    (u : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (Z : PiLp 2 (fun _ : Fin n => dirichletValue K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) Z =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (rawLowerFormOperator D hK.isClosed η hη u) -
            principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z u)
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k : Fin n) :
    ∃ W : Fin n → Fin n → L2, ∀ i j,
      HasWeakSchwartzDerivative (localizedDirichletPartial K χ (u k) i)
        (W i j) (EuclideanSpace.single j (1 : ℝ)) := by
  obtain ⟨δ, hδ, hδK⟩ := hχ.exists_cthickening_subset_open isOpen_interior hχK
  let r : ℝ := δ / 3
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hthick : cthickening (3 * r) (tsupport χ) ⊆ K := by
    have he : 3 * r = δ := by dsimp only [r]; ring
    rw [he]
    exact hδK.trans interior_subset
  let A := rawCutoffPrincipalCoefficient g η hη
  obtain ⟨ell, hEll, hell⟩ := exists_rawCutoffPrincipalCoefficient_ellipticity g hK η hη hηK
  obtain ⟨B, hB, hAB⟩ := exists_schwartz_matrix_derivative_bound A
  have hweak := vector_component_divergence K A
    (rawCutoffPrincipalCoefficient_symmetric g η hη) u
    (rawLowerFormOperator D hK.isClosed η hη u) Z heq k
  let G : L2 := ((rawLowerFormOperator D hK.isClosed η hη u) k : L2) - (Z k : L2)
  obtain ⟨W, hW⟩ := exists_localized_dirichlet_secondDerivatives K A χ hχ
    (hχK.trans interior_subset) (u k) G hweak hr hEll hB
    (fun x hx => hell x (hthick hx)) hAB
  exact ⟨W, fun i j => (hW i j).2⟩

end PoincareConjecture.M35.Uniqueness.Heat
