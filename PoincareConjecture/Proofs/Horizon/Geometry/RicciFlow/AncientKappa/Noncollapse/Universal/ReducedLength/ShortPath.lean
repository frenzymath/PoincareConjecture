import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.FlowControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ReducedLength.TerminalBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ShortSegment

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.M22UniversalNoncollapsingPredecessors

variable {d n : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] (K : AncientKappaSolution n M)

include H

theorem exists_short_terminal_path (p y : M)
    (hy : y ∈ (K.flow.metric (-1)).ball p (1 / 2))
    (hscalar : ∀ x ∈ (K.flow.metric (-1)).ball p 1,
      (K.flow.connection (-1)).scalarCurvature x ≤ 2) :
    ∃ W : Set ℝ, IsOpen W ∧ Icc (1 : ℝ) 2 ⊆ W ∧ ∃ q : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q W ∧ q 1 = p ∧ q 2 = y ∧
      (∀ s ∈ Icc (1 : ℝ) 2, (K.flow.connection (0 - s)).scalarCurvature (q s) ≤ 2) ∧
      (∀ s ∈ Icc (1 : ℝ) 2,
        (K.flow.metric (0 - s)).inner (q s) (curveVelocity q s) (curveVelocity q s) ≤
          Real.exp 4) := by
  let g := K.flow.metric (-1)
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hrange, hspeed⟩ :=
    g.exists_smooth_short_segment (K.complete (-1) (by norm_num)) p y (by norm_num) hy
  let a : ℝ → ℝ := fun s ↦ s - 1
  let q : ℝ → M := γ ∘ a
  let W := Ioo (1 - ε) (2 + ε)
  have ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ a := by
    apply contMDiff_iff_contDiff.mpr
    dsimp only [a]
    fun_prop
  have hmap : MapsTo a W (Ioo (-ε) (1 + ε)) := by
    intro s hs
    constructor <;> dsimp only [a] <;> linarith [hs.1, hs.2]
  have hW : Icc (1 : ℝ) 2 ⊆ W := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hunit (s : ℝ) (hs : s ∈ Icc (1 : ℝ) 2) : a s ∈ Icc (0 : ℝ) 1 := by
    constructor <;> dsimp only [a] <;> linarith [hs.1, hs.2]
  have hqrange (s : ℝ) (hs : s ∈ Icc (1 : ℝ) 2) : q s ∈ g.ball p 1 :=
    (hrange (a s) (hunit s hs)).trans_le (ENNReal.ofReal_le_ofReal (by norm_num))
  refine ⟨W, isOpen_Ioo, hW, q, hγ.comp ha.contMDiffOn hmap,
    by simpa [q, a] using hγ0, by norm_num [q, a, hγ1], ?_, ?_⟩
  · intro s hs
    exact (H.scalar_monotone K (by linarith [hs.1] : 0 - s ≤ -1) (by norm_num) (q s)).trans
      (hscalar (q s) (hqrange s hs))
  · intro s hs
    have hvel : curveVelocity (n := n) q s = curveVelocity (n := n) γ (a s) := by
      have hγat := (hγ (a s) (hmap (hW hs))).contMDiffAt (isOpen_Ioo.mem_nhds (hmap (hW hs)))
      have had : HasDerivAt a 1 s := (hasDerivAt_id s).sub_const 1
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ ∘ a) s 1 = _
      rw [mfderiv_comp_apply s (hγat.mdifferentiableAt (by simp))
        (ha.mdifferentiable (by simp) s), mfderiv_eq_fderiv, had.hasFDerivAt.fderiv]
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (a s) ((1 : ℝ) • 1) = _
      rw [one_smul]
      rfl
    have hnorm : (g.edist p y).toReal ^ 2 ≤ 1 := by
      have hd := ENNReal.toReal_lt_of_lt_ofReal hy
      have hz := ENNReal.toReal_nonneg (a := g.edist p y)
      nlinarith
    calc
      (K.flow.metric (0 - s)).inner (q s) (curveVelocity q s) (curveVelocity q s) ≤
          Real.exp 4 * g.inner (q s) (curveVelocity q s) (curveVelocity q s) :=
        H.metric_inner_le_exp_four K (by constructor <;> linarith [hs.1, hs.2])
          (q s) (hscalar (q s) (hqrange s hs)) (curveVelocity q s)
      _ = Real.exp 4 * (g.edist p y).toReal ^ 2 := by
        rw [hvel]
        exact congrArg (fun v : ℝ ↦ Real.exp 4 * v) (hspeed (a s) (hunit s hs))
      _ ≤ Real.exp 4 := by nlinarith [Real.exp_pos (4 : ℝ)]

end PoincareConjecture.M22UniversalNoncollapsingPredecessors
