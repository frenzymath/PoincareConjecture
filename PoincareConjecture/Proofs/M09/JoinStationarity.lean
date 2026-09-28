import PoincareConjecture.Proofs.M09.SquareActionComparison
import PoincareConjecture.Proofs.M09.SmoothSquareFirstVariation
import Mathlib.Analysis.Calculus.LocalExtr.Basic








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_join_momentum_pairing
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z W : TangentSpace (𝓡 n) p)
    (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b (hc.trans hcb) hmax))
    (haction : A.action W c = A.action Z c)
    (f g : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ f U)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ g U)
    (ρ : ℝ) (hρ : 0 < ρ) (hI : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ U)
    (hfcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), f (s, 0) = A.squareFamily W s)
    (hgcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), g (s, 0) = A.squareFamily Z s)
    (hfleft : ∀ u ∈ Set.Ioo (-ρ) ρ, f (0, u) = p)
    (hgleft : ∀ u ∈ Set.Ioo (-ρ) ρ, g (0, u) = p)
    (hgright : ∀ u ∈ Set.Ioo (-ρ) ρ, g (Real.sqrt b, u) = A.gamma Z b)
    (hjoin : ∀ u ∈ Set.Ioo (-ρ) ρ, f (Real.sqrt c, u) = g (Real.sqrt c, u)) :
    (F.metric (T - c)).inner (A.squareFamily W (Real.sqrt c))
        (curveVelocity (n := n) (A.squareFamily W) (Real.sqrt c))
        (curveVelocity (n := n) (fun u ↦ f (Real.sqrt c, u)) 0) =
      (F.metric (T - c)).inner (A.squareFamily Z (Real.sqrt c))
        (curveVelocity (n := n) (A.squareFamily Z) (Real.sqrt c))
        (curveVelocity (n := n) (fun u ↦ g (Real.sqrt c, u)) 0) := by
  have hb : 0 < b := hc.trans hcb
  have hcmax : c < τmax := hcb.trans hmax
  have hroot : Real.sqrt c ≤ Real.sqrt b := Real.sqrt_le_sqrt hcb.le
  have hIc : Set.Icc 0 (Real.sqrt c) ×ˢ Set.Ioo (-ρ) ρ ⊆ U := by
    intro z hz
    exact hI ⟨⟨hz.1.1, hz.1.2.trans hroot⟩, hz.2⟩
  have hfc : ∀ s ∈ Set.Icc 0 (Real.sqrt c), f (s, 0) = A.squareFamily W s :=
    fun s hs ↦ hfcenter s ⟨hs.1, hs.2.trans hroot⟩
  have hgc : ∀ s ∈ Set.Icc 0 (Real.sqrt c), g (s, 0) = A.squareFamily Z s :=
    fun s hs ↦ hgcenter s ⟨hs.1, hs.2.trans hroot⟩
  let H : ℝ → ℝ := fun u ↦ backwardLLength F T 0 c (fun t ↦ f (Real.sqrt t, u)) +
    backwardLLength F T 0 b (fun t ↦ g (Real.sqrt t, u)) -
      backwardLLength F T 0 c (fun t ↦ g (Real.sqrt t, u))
  have hH0 : H 0 = A.action Z b := by
    dsimp only [H]
    rw [lExponentialFamily_action_comp_sqrt_eq_of_eqOn A W c hc hcmax
        (fun s ↦ f (s, 0)) (fun s hs ↦ hfc s hs),
      lExponentialFamily_action_comp_sqrt_eq_of_eqOn A Z b hb hmax
        (fun s ↦ g (s, 0)) (fun s hs ↦ hgcenter s hs),
      lExponentialFamily_action_comp_sqrt_eq_of_eqOn A Z c hc hcmax
        (fun s ↦ g (s, 0)) (fun s hs ↦ hgc s hs), haction]
    ring
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨neg_lt_zero.mpr hρ, hρ⟩
  have hHmin : IsLocalMin H 0 := by
    change ∀ᶠ u in 𝓝 (0 : ℝ), H 0 ≤ H u
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with u hu
    rw [hH0]
    let D := (fun s : ℝ ↦ (s, u)) ⁻¹' U
    have hD : IsOpen D := hU.preimage (continuous_id.prodMk continuous_const)
    have hDI : Set.Icc 0 (Real.sqrt b) ⊆ D := fun s hs ↦ hI ⟨hs, hu⟩
    have hfD : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun s ↦ f (s, u)) D :=
      hf.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs ↦ hs)
    have hgD : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun s ↦ g (s, u)) D :=
      hg.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs ↦ hs)
    have hl : f (0, u) = (A.path Z b hb hmax).curve 0 := by
      simpa only [A.path_eq, A.gamma_at_zero] using hfleft u hu
    have hr : g (Real.sqrt b, u) = (A.path Z b hb hmax).curve b := by
      simpa only [A.path_eq] using hgright u hu
    have hcomp := minimizing_action_le_broken_action F hM04 T τmax hτmax hwindow
      c b hc hcb hmax (A.path Z b hb hmax) hmin (fun s ↦ f (s, u)) (fun s ↦ g (s, u))
      D hD hDI hfD hgD (hjoin u hu) hl hr
    rw [A.path_eq] at hcomp
    exact hcomp
  have hfixed (k : ℝ → M) (q : M) (hk : ∀ u ∈ Set.Ioo (-ρ) ρ, k u = q) :
      (curveVelocity (n := n) k 0 : Q) = 0 := by
    have heq : k =ᶠ[𝓝 (0 : ℝ)] (fun _ ↦ q) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hzero) (fun u hu ↦ hk u hu)
    unfold curveVelocity
    rw [heq.mfderiv_eq, mfderiv_const]
    rfl
  have hf0 := hfixed (fun u ↦ f (0, u)) p hfleft
  have hg0 := hfixed (fun u ↦ g (0, u)) p hgleft
  have hgb := hfixed (fun u ↦ g (Real.sqrt b, u)) (A.gamma Z b) hgright
  have hdf := hasDerivAt_smoothSquareFamily_action hM04 hL hτmax hwindow A W
    c hc hcmax f U hU hf ρ hρ hIc hfc
  have hdgb := hasDerivAt_smoothSquareFamily_action hM04 hL hτmax hwindow A Z
    b hb hmax g U hU hg ρ hρ hI hgcenter
  have hdgc := hasDerivAt_smoothSquareFamily_action hM04 hL hτmax hwindow A Z
    c hc hcmax g U hU hg ρ hρ hIc hgc
  simp only [hf0, map_zero, sub_zero] at hdf
  simp only [hg0, hgb, map_zero, sub_self] at hdgb
  simp only [hg0, map_zero, sub_zero] at hdgc
  have hderiv := (hdf.add hdgb).sub hdgc
  have hstat := hHmin.hasDerivAt_eq_zero hderiv
  exact sub_eq_zero.mp (by simpa only [add_zero] using hstat)

end PoincareConjecture.Proofs.M09
