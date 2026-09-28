import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowAlgebra
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integralCurves_eqOn_of_local_agreement (f g : E → E)
    {k : ℝ≥0} (hg : LipschitzWith k g) (γ η : ℝ → E)
    (hγ : ∀ t, HasDerivAt γ (g (γ t)) t)
    (hη : ∀ t, HasDerivAt η (f (η t)) t)
    {I : Set ℝ} (hI : IsPreconnected I)
    (hnear : ∀ t ∈ I, γ t = η t → g =ᶠ[𝓝 (η t)] f)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h₀ : γ t₀ = η t₀) : EqOn γ η I := by
  let : PreconnectedSpace I := Subtype.preconnectedSpace hI
  have hcγ : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  have hcη : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  have hclosed : IsClosed {t : I | γ t = η t} :=
    isClosed_eq (hcγ.comp continuous_subtype_val) (hcη.comp continuous_subtype_val)
  have hopen : IsOpen {t : I | γ t = η t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hag : ∀ᶠ s in 𝓝 (t : ℝ), g (η s) = f (η s) :=
      (hη t).continuousAt.eventually (hnear t t.2 ht)
    have hηg : ∀ᶠ s in 𝓝 (t : ℝ),
        HasDerivAt η (g (η s)) s ∧ η s ∈ (univ : Set E) := by
      filter_upwards [hag] with s hs
      rw [hs]
      exact ⟨hη s, mem_univ _⟩
    have heq : γ =ᶠ[𝓝 (t : ℝ)] η := ODE_solution_unique_of_eventually
      (v := fun _ x => g x) (s := fun _ => univ)
      (Eventually.of_forall fun _ => hg.lipschitzOnWith)
      (Eventually.of_forall fun s => ⟨hγ s, mem_univ _⟩) hηg ht
    exact continuous_subtype_val.continuousAt.eventually heq
  have hall : {t : I | γ t = η t} = univ :=
    (show IsClopen {t : I | γ t = η t} from ⟨hclosed, hopen⟩).eq_univ ⟨⟨t₀, ht₀⟩, h₀⟩
  intro t ht
  exact (Set.eq_univ_iff_forall.mp hall) ⟨t, ht⟩

end PoincareConjecture.M25.Topology3D
