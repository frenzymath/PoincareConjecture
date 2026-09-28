import PoincareConjecture.Proofs.M10.MinimizingLifts
import Mathlib.Analysis.Calculus.LocalExtr.Basic









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem reducedLength_eq_normalized_action_of_minimizing
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 τ (G.path Z τ hτ hmax)) :
    reducedLength F T p (G.gamma Z τ) τ =
      G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ) := by
  apply le_antisymm (reducedLength_le_normalized_action hL G Z τ hτ hmax)
  obtain ⟨path, hp, hq, _, hlength⟩ :=
    hL.reduced_length_attained τ hτ hmax.le p (G.gamma Z τ)
  have hcomp := hmin path
    (by rw [G.path_eq, G.gamma_at_zero]; exact hp)
    (by rw [G.path_eq]; exact hq)
  rw [G.path_eq] at hcomp
  rw [hlength]
  exact div_le_div_of_nonneg_right hcomp (by positivity)

set_option backward.isDefEq.respectTransparency false in

theorem reducedLength_differential_on_slice_range
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 τ (G.path Z τ hτ hmax))
    (hl : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ reducedLength F T p q τ)
      (G.gamma Z τ)) (W : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ reducedLength F T p q τ) (G.gamma Z τ)
        (G.toLExponentialFamily.sliceDifferential Z τ W) =
      (F.metric (T - τ)).inner (G.gamma Z τ) (curveVelocity (G.gamma Z) τ)
        (G.toLExponentialFamily.sliceDifferential Z τ W) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have htime : (Z, τ) ∈ (univ : Set (TangentSpace (𝓡 n) p)) ×ˢ Ioo 0 τmax :=
    ⟨mem_univ _, hτ, hmax⟩
  have hE : MDifferentiableAt (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n)
      (fun V ↦ G.gamma V τ) Z :=
    ((G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds htime)).comp Z
      (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  have hA : DifferentiableAt ℝ (fun V ↦ G.toLExponentialFamily.action V τ) Z :=
    ((G.action_smooth.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds htime)).comp Z
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  let c : ℝ := (2 * Real.sqrt τ)⁻¹
  let cost : TangentSpace (𝓡 n) p → ℝ :=
    fun V ↦ c * G.toLExponentialFamily.action V τ
  let pull : TangentSpace (𝓡 n) p → ℝ := fun V ↦ reducedLength F T p (G.gamma V τ) τ
  have hcost : DifferentiableAt ℝ cost Z := hA.const_mul c
  have hpull : DifferentiableAt ℝ pull Z := by
    exact (hl.comp (f := fun V ↦ G.gamma V τ) Z hE).differentiableAt
  have hcontact : cost Z = pull Z := by
    dsimp [cost, pull, c]
    rw [reducedLength_eq_normalized_action_of_minimizing hL G Z hτ hmax hmin,
      div_eq_mul_inv, mul_comm]
  have hlocal : IsLocalMin (cost - pull) Z := by
    apply Filter.Eventually.of_forall
    intro V
    have hle := reducedLength_le_normalized_action hL G V τ hτ hmax
    change cost Z - pull Z ≤ cost V - pull V
    rw [hcontact, sub_self]
    apply sub_nonneg.mpr
    simpa only [cost, pull, c, div_eq_mul_inv, mul_comm] using hle
  have hderiv := hlocal.fderiv_eq_zero
  rw [fderiv_sub hcost hpull] at hderiv
  have heq : fderiv ℝ pull Z = fderiv ℝ cost Z := (sub_eq_zero.mp hderiv).symm
  have hchain : fderiv ℝ pull Z W =
      mvfderiv (𝓡 n) (fun q ↦ reducedLength F T p q τ) (G.gamma Z τ)
        (G.toLExponentialFamily.sliceDifferential Z τ W) := by
    have h := mfderiv_comp_apply Z hl hE W
    rw [mfderiv_eq_fderiv] at h
    exact h
  rw [← hchain, heq]
  dsimp only [cost]
  rw [fderiv_const_mul hA c]
  simp only [smul_apply, smul_eq_mul]
  rw [G.action_initial_differential Z τ hτ hmax W]
  dsimp only [c]
  have hden : 2 * Real.sqrt τ ≠ 0 := by positivity
  field_simp


theorem reducedLength_differential_eq_terminal_pairing
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 τ (G.path Z τ hτ hmax))
    (hl : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ reducedLength F T p q τ)
      (G.gamma Z τ))
    (hsurj : Function.Surjective (G.toLExponentialFamily.sliceDifferential Z τ))
    (v : TangentSpace (𝓡 n) (G.gamma Z τ)) :
    mvfderiv (𝓡 n) (fun q ↦ reducedLength F T p q τ) (G.gamma Z τ) v =
      (F.metric (T - τ)).inner (G.gamma Z τ) (curveVelocity (G.gamma Z) τ) v := by
  obtain ⟨W, rfl⟩ := hsurj v
  exact reducedLength_differential_on_slice_range hL G Z hτ hmax hmin hl W

end PoincareConjecture.M10
