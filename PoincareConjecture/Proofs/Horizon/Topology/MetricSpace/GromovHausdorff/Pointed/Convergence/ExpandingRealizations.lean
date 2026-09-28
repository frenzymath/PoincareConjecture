import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology

namespace Poincare.GromovHausdorff
universe u



theorem exists_subseq_expanding_pointed_realizations
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (hconv : PointedGHConvergesUnbounded X Y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ s : ℕ → ℝ, (∀ j : ℕ, (j : ℝ) + 1 < s j) ∧
        ∃ hs : ∀ j, 0 < s j,
          ∃ Q : ∀ j, PointedGHRealization
            (ballModel (X (φ j)) (s j) (hs j))
            (ballModel Y ((j : ℝ) + 2) (by positivity)),
            ∀ j, pointedHausdorffDist (Q j) < 1 / ((j : ℝ) + 1) := by
  classical
  let R : ℕ → ℝ := fun j => (j : ℝ) + 2
  have hR (j : ℕ) : 0 < R j := by dsimp [R]; positivity
  let ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose δ hδ hpos hconvR using fun j => hconv (R j) (hR j)
  have hgood (n : ℕ) : ∀ᶠ j in atTop,
      -1 < δ n j ∧
        pointedGHDistance (ballModel (X j) (R n + δ n j) (hpos n j))
          (ballModel Y (R n) (hR n)) < ε n / 2 :=
    ((hδ n).eventually_const_lt (by norm_num)).and
      ((hconvR n).2.eventually_lt_const (by positivity))
  obtain ⟨φ, hφ, hφgood⟩ :=
    Filter.Tendsto.subseq_mem hgood (u := id) tendsto_id
  let s : ℕ → ℝ := fun j => R j + δ j (φ j)
  have hs (j : ℕ) : 0 < s j := hpos j (φ j)
  have hjs (j : ℕ) : (j : ℝ) + 1 < s j := by
    have hj : -1 < δ j (φ j) := (hφgood j).1
    dsimp [s, R]
    linarith
  have hex (j : ℕ) :
      ∃ Q : PointedGHRealization (ballModel (X (φ j)) (s j) (hs j))
          (ballModel Y (R j) (hR j)),
        pointedHausdorffDist Q < ε j := by
    obtain ⟨Q, hQ⟩ := exists_pointedGHRealization_lt_add
      (ballModel (X (φ j)) (s j) (hs j)) (ballModel Y (R j) (hR j))
      (show 0 < ε j / 2 by positivity)
    refine ⟨Q, ?_⟩
    have hj := (hφgood j).2
    change pointedGHDistance (ballModel (X (φ j)) (s j) (hs j))
      (ballModel Y (R j) (hR j)) < ε j / 2 at hj
    linarith
  choose Q hQ using hex
  refine ⟨φ, hφ, s, hjs, hs, Q, ?_⟩
  intro j
  simpa only [ε, one_div] using hQ j

end Poincare.GromovHausdorff
