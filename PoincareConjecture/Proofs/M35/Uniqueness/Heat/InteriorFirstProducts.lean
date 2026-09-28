import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawInteriorRegularity

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

theorem weakSchwartzDerivative_sub {u d f e : L2} {v : V}
    (hu : HasWeakSchwartzDerivative u d v) (hf : HasWeakSchwartzDerivative f e v) :
    HasWeakSchwartzDerivative (u - f) (d - e) v := by
  intro φ
  simp only [inner_sub_left, hu φ, hf φ]
  ring

theorem weakSchwartzDerivative_congr {u f d : L2} {v : V}
    (huf : u = f) (hf : HasWeakSchwartzDerivative f d v) :
    HasWeakSchwartzDerivative u d v := huf ▸ hf

def HasInteriorSecondDerivatives (K : Set V) (u : dirichletForm K) : Prop :=
  ∀ a : 𝓢(V, ℝ), HasCompactSupport a → tsupport a ⊆ interior K →
    ∃ W : Fin n → Fin n → L2, ∀ i j,
      HasWeakSchwartzDerivative (localizedDirichletPartial K a u i)
        (W i j) (EuclideanSpace.single j (1 : ℝ))

theorem exists_weak_derivative_partial_product (K : Set V) (u : dirichletForm K)
    (hu : HasInteriorSecondDerivatives K u) (a : 𝓢(V, ℝ))
    (ha : HasCompactSupport a) (haK : tsupport a ⊆ interior K) (i j : Fin n) :
    ∃ d : L2, HasWeakSchwartzDerivative
      (schwartzMultiplier a (dirichletPartial K i u)) d (EuclideanSpace.single j (1 : ℝ)) := by
  obtain ⟨W, hW⟩ := hu a ha haK
  have hcut := (dirichletPartial_weak K u j).mul _ _ _
    (∂_{EuclideanSpace.single i (1 : ℝ)} a)
  have h := weakSchwartzDerivative_sub (hW i j) hcut
  have he : localizedDirichletPartial K a u i -
      schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} a)
        (dirichletInclusion K u : L2) = schwartzMultiplier a (dirichletPartial K i u) :=
    add_sub_cancel_right _ _
  rw [he] at h
  exact ⟨_, h⟩

theorem raw_compact_heat_hasInteriorSecondDerivatives
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
    (k : Fin n) : HasInteriorSecondDerivatives K (u k) :=
  fun a ha haK => exists_raw_compact_heat_interior_secondDerivatives D hK η hη hηK
    u Z heq a ha haK k

end PoincareConjecture.M35.Uniqueness.Heat
