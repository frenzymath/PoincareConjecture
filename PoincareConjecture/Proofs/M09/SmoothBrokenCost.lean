import PoincareConjecture.Proofs.M09.LineInteriorFamily
import PoincareConjecture.Proofs.M09.SmoothSquareAction
import PoincareConjecture.Proofs.M09.SquareActionComparison

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
  {A : LExponentialFamily F T τmax p} {Z W : TangentSpace (𝓡 n) p} {c b : ℝ}

local notation "Q" => EuclideanSpace ℝ (Fin n)

namespace LineInteriorFamily

noncomputable def prefixAction (D : LineInteriorFamily A Z W c b) (z : ℝ × Q) : ℝ :=
  backwardLLength F T 0 c (fun t ↦ D.family (z, Real.sqrt t))

noncomputable def tailAction (D : LineInteriorFamily A Z W c b) (y : Q) : ℝ :=
  backwardLLength F T 0 b (fun t ↦ D.family ((0, y), Real.sqrt t)) - D.prefixAction (0, y)

noncomputable def cost (D : LineInteriorFamily A Z W c b) (z : ℝ × Q) : ℝ :=
  D.prefixAction (z.1, lineInteriorCoordinate A Z W c z.1 + z.2) +
    D.tailAction (lineInteriorCoordinate A Z W c z.1 + z.2)

theorem action_contDiffAt (D : LineInteriorFamily A Z W c b)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hmax : b < τmax)
    (d : ℝ) (hd : 0 < d) (hdb : d ≤ b) (z : ℝ × Q) (hz : z ∈ D.parameters) :
    ContDiffAt ℝ ∞ (fun w ↦ backwardLLength F T 0 d
      (fun t ↦ D.family (w, Real.sqrt t))) z := by
  have h := contDiffAt_smoothSquareFamily_action F hM04 T τmax hτmax hwindow
    D.family D.domain D.domain_open D.smooth (z, d) ⟨hd, hdb.trans_lt hmax⟩ (fun r hr ↦
      D.segment_mem ⟨hz, mul_nonneg (Real.sqrt_nonneg d) hr.1,
        (mul_le_of_le_one_right (Real.sqrt_nonneg d) hr.2).trans (Real.sqrt_le_sqrt hdb)⟩)
  exact h.comp z (contDiffAt_id.prodMk contDiffAt_const)

theorem prefixAction_contDiffAt (D : LineInteriorFamily A Z W c b)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (z : ℝ × Q) (hz : z ∈ D.parameters) : ContDiffAt ℝ ∞ D.prefixAction z :=
  D.action_contDiffAt hM04 hτmax hwindow hmax c hc hcb.le z hz

theorem tailAction_contDiffAt (D : LineInteriorFamily A Z W c b)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (y : Q) (hy : (0, y) ∈ D.parameters) : ContDiffAt ℝ ∞ D.tailAction y := by
  exact ((D.action_contDiffAt hM04 hτmax hwindow hmax b (hc.trans hcb) le_rfl (0, y) hy).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).sub
      ((D.prefixAction_contDiffAt hM04 hτmax hwindow hc hcb hmax (0, y) hy).comp y
        (contDiffAt_const.prodMk contDiffAt_id))

theorem cost_contDiffAt (D : LineInteriorFamily A Z W c b)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax) :
    ContDiffAt ℝ ∞ D.cost (0, 0) := by
  let a := lineInteriorCoordinate A Z W c
  have ha : ContDiffAt ℝ ∞ (fun z : ℝ × Q ↦ a z.1 + z.2) (0, 0) :=
    (D.coordinate_smooth.comp (0, 0) contDiffAt_fst).add contDiffAt_snd
  have hL : ContDiffAt ℝ ∞ D.prefixAction (0, a 0 + 0) := by
    simpa only [add_zero] using
      D.prefixAction_contDiffAt hM04 hτmax hwindow hc hcb hmax (0, a 0) D.center_mem
  have hS : ContDiffAt ℝ ∞ D.tailAction (a 0 + 0) := by
    simpa only [add_zero] using
      D.tailAction_contDiffAt hM04 hτmax hwindow hc hcb hmax (a 0) D.center_mem
  exact (hL.comp (0, 0) (contDiffAt_fst.prodMk ha)).add (hS.comp (0, 0) ha)

theorem prefixAction_diagonal (D : LineInteriorFamily A Z W c b)
    (hc : 0 < c) (hcb : c < b) (hmax : b < τmax) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      D.prefixAction (r, lineInteriorCoordinate A Z W c r) = A.action (Z + r • W) c := by
  filter_upwards [D.diagonal_mem] with r hr
  exact lExponentialFamily_action_comp_sqrt_eq_of_eqOn A (Z + r • W) c hc (hcb.trans hmax)
    (fun s ↦ D.family ((r, lineInteriorCoordinate A Z W c r), s))
    (fun s hs ↦ D.recovery (r, lineInteriorCoordinate A Z W c r) hr s
      ⟨hs.1, hs.2.trans (Real.sqrt_le_sqrt hcb.le)⟩)

theorem cost_at_zero (D : LineInteriorFamily A Z W c b)
    (hc : 0 < c) (hcb : c < b) (hmax : b < τmax) : D.cost (0, 0) = A.action Z b := by
  have hrec : Set.EqOn (fun s ↦ D.family ((0, lineInteriorCoordinate A Z W c 0), s))
      (A.squareFamily Z) (Set.Icc 0 (Real.sqrt b)) := by
    intro s hs
    simpa only [zero_smul, add_zero] using D.recovery _ D.center_mem s hs
  have hb := lExponentialFamily_action_comp_sqrt_eq_of_eqOn A Z b (hc.trans hcb) hmax _ hrec
  simpa only [cost, tailAction, add_zero, ← add_sub_assoc, add_sub_cancel_left] using hb

theorem cost_isLocalMin (D : LineInteriorFamily A Z W c b)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b (hc.trans hcb) hmax)) :
    IsLocalMin D.cost (0, 0) := by
  let a := lineInteriorCoordinate A Z W c
  let k : ℝ × Q → ℝ × Q := fun z ↦ (z.1, a z.1 + z.2)
  let l : ℝ × Q → ℝ × Q := fun z ↦ (0, a z.1 + z.2)
  have ha : ContinuousAt (fun z : ℝ × Q ↦ a z.1 + z.2) (0, 0) :=
    ((D.coordinate_smooth.comp (0, 0) contDiffAt_fst).continuousAt).add continuousAt_snd
  have hk : ContinuousAt k (0, 0) := continuousAt_fst.prodMk ha
  have hl : ContinuousAt l (0, 0) := continuousAt_const.prodMk ha
  have hkN : ∀ᶠ z in 𝓝 ((0, 0) : ℝ × Q), k z ∈ D.parameters := by
    apply hk.preimage_mem_nhds
    simpa only [k, add_zero] using D.parameters_open.mem_nhds D.center_mem
  have hlN : ∀ᶠ z in 𝓝 ((0, 0) : ℝ × Q), l z ∈ D.parameters := by
    apply hl.preimage_mem_nhds
    simpa only [l, add_zero] using D.parameters_open.mem_nhds D.center_mem
  change ∀ᶠ z in 𝓝 ((0, 0) : ℝ × Q), D.cost (0, 0) ≤ D.cost z
  rw [D.cost_at_zero hc hcb hmax]
  filter_upwards [hkN, hlN] with z hz hz'
  let α : ℝ → M := fun s ↦ D.family (k z, s)
  let β : ℝ → M := fun s ↦ D.family (l z, s)
  let U : Set ℝ := (fun s ↦ (k z, s)) ⁻¹' D.domain ∩
    (fun s ↦ (l z, s)) ⁻¹' D.domain
  have hU : IsOpen U :=
    (D.domain_open.preimage (continuous_const.prodMk continuous_id)).inter
      (D.domain_open.preimage (continuous_const.prodMk continuous_id))
  have hI : Set.Icc 0 (Real.sqrt b) ⊆ U := fun s hs ↦
    ⟨D.segment_mem ⟨hz, hs⟩, D.segment_mem ⟨hz', hs⟩⟩
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U :=
    D.smooth.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn (fun _ hs ↦ hs.1)
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β U :=
    D.smooth.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn (fun _ hs ↦ hs.2)
  have hmeet : α (Real.sqrt c) = β (Real.sqrt c) :=
    (D.marked z.1 (a z.1 + z.2)).trans (D.marked 0 (a z.1 + z.2)).symm
  have hleft : α 0 = (A.path Z b (hc.trans hcb) hmax).curve 0 := by
    rw [A.path_eq]
    exact (D.left z.1 (a z.1 + z.2)).trans (A.gamma_at_zero Z).symm
  have hright : β (Real.sqrt b) = (A.path Z b (hc.trans hcb) hmax).curve b := by
    rw [A.path_eq]
    have h := D.right 0 (a z.1 + z.2)
    simp only [zero_smul, add_zero] at h
    apply h.trans
    simpa only [Real.sq_sqrt (hc.trans hcb).le] using A.square_agrees Z (Real.sqrt b)
      ⟨Real.sqrt_nonneg b, Real.sqrt_lt_sqrt (hc.trans hcb).le hmax⟩
  have hcomp := minimizing_action_le_broken_action F hM04 T τmax hτmax hwindow
    c b hc hcb hmax (A.path Z b (hc.trans hcb) hmax) hmin α β U hU hI hα hβ hmeet hleft hright
  rw [A.path_eq] at hcomp
  change A.action Z b ≤ _ at hcomp
  simpa only [cost, prefixAction, tailAction, α, β, k, l, a, add_sub_assoc] using hcomp

end LineInteriorFamily

end PoincareConjecture.Proofs.M09
