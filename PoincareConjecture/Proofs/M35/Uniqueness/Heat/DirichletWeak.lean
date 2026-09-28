import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalFormOperator
import PoincareConjecture.Proofs.M03.Existence.DeTurckHigherDomainNative

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

theorem dirichletPartial_weak (K : Set V) (u : dirichletForm K) (i : Fin n) :
    HasWeakSchwartzDerivative (dirichletInclusion K u : L2)
      (dirichletPartial K i u) (EuclideanSpace.single i (1 : ℝ)) := by
  intro φ
  have he : (fun v : dirichletForm K => inner ℝ (dirichletPartial K i v) (φ.toLp 2 volume)) =
      (fun v => -inner ℝ (dirichletInclusion K v : L2)
        ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume)) := by
    apply (intoDirichletForm_denseRange K).equalizer
      ((dirichletPartial K i).continuous.inner continuous_const)
      ((((dirichletValue K).subtypeL.continuous.comp
        (dirichletInclusion K).continuous).inner continuous_const).neg)
    funext f
    have h := inner_schwartzLineDeriv (f : 𝓢(V, ℝ)) φ (EuclideanSpace.single i (1 : ℝ))
    change inner ℝ ((∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))).toLp 2 volume)
      (φ.toLp 2 volume) =
        -inner ℝ ((f : 𝓢(V, ℝ)).toLp 2 volume)
          ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume)
    linarith only [h]
  exact congrFun he u

def localizedDirichletValue (K : Set V) (η : 𝓢(V, ℝ))
    (u : dirichletForm K) : L2 :=
  schwartzMultiplier η (dirichletInclusion K u : L2)

def localizedDirichletPartial (K : Set V) (η : 𝓢(V, ℝ))
    (u : dirichletForm K) (i : Fin n) : L2 :=
  schwartzMultiplier η (dirichletPartial K i u) +
    schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} η)
      (dirichletInclusion K u : L2)

theorem localizedDirichletPartial_weak (K : Set V) (η : 𝓢(V, ℝ))
    (u : dirichletForm K) (i : Fin n) :
    HasWeakSchwartzDerivative (localizedDirichletValue K η u)
      (localizedDirichletPartial K η u i) (EuclideanSpace.single i (1 : ℝ)) :=
  (dirichletPartial_weak K u i).mul _ _ _ η

theorem localizedDirichletValue_ae_support (K : Set V) (η : 𝓢(V, ℝ))
    (u : dirichletForm K) :
    ∀ᵐ x ∂volume, x ∉ tsupport η → localizedDirichletValue K η u x = 0 := by
  filter_upwards [schwartzMultiplier_coe η (dirichletInclusion K u : L2)] with x hx hnot
  change schwartzMultiplier η (dirichletInclusion K u : L2) x = 0
  rw [hx, image_eq_zero_of_notMem_tsupport hnot, zero_mul]

end PoincareConjecture.M35.Uniqueness.Heat
