import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal
import PoincareConjecture.Proofs.M47.TerminalSourceIndexedCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

theorem terminalSource_exists_strict_diagonal_chart_covers
    (Data : ℕ → ℕ → Type v)
    (C : ∀ j n, Data j n → GeneralizedSliceCarrier.{u})
    (g : ∀ j n (d : Data j n), RiemannianMetric 3 (C j n d).carrier)
    (p : ∀ j n (d : Data j n), (C j n d).carrier)
    (A R rho : ℕ → ℝ) (N : ℕ → ℕ)
    (hstage : ∀ j, ∀ᶠ n in atTop, ∃ d : Data j n,
      Nonempty (TerminalSourceIndexedChartCover (g j n d) (p j n d)
        (A j) (R j) (rho j) (N j))) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ data : ∀ k j, j ≤ k → Data j (sigma k),
        Nonempty (∀ k j (hjk : j ≤ k),
          TerminalSourceIndexedChartCover
            (g j (sigma k) (data k j hjk)) (p j (sigma k) (data k j hjk))
            (A j) (R j) (rho j) (N j)) := by
  classical
  obtain ⟨sigma, hsigma, hselect⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually hstage
  let data : ∀ k j, j ≤ k → Data j (sigma k) :=
    fun k j hjk => (hselect k j hjk).choose
  refine ⟨sigma, hsigma, data, ⟨?_⟩⟩
  exact fun k j hjk => Classical.choice (hselect k j hjk).choose_spec

end PoincareConjecture.M47
