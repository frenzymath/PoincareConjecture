import PoincareConjecture.Proofs.M09.LocalRegularizedCurve
import PoincareConjecture.Proofs.M09.GeometricRestartFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => ℝ × (V × V)

structure RegularizedIntervalSolution {J : Set ℝ} (F : RicciFlow n M J)
    (T b s0 : ℝ) (q0 : TangentBundle (𝓡 n) M) where
  domain : Set ℝ
  open_domain : IsOpen domain
  preconnected_domain : IsPreconnected domain
  initial_mem : s0 ∈ domain
  time_mem : domain ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b)
  curve : ℝ → M
  isLocal : IsLocalRegularizedCurveOn F T curve domain
  initial_phase : curvePhase (n := n) curve s0 = q0

theorem LocalRegularizedRestartFamily.isLocalRegularizedCurveOn {J : Set ℝ}
    {F : RicciFlow n M J} {T b : ℝ} {p : M} {z0 : Z}
    (A : LocalRegularizedRestartFamily F T b p z0)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (z : Z) (hz : z ∈ A.neighborhood) :
    IsLocalRegularizedCurveOn F T (A.curve z)
      (Set.Ioo (z.1 - A.radius) (z.1 + A.radius)) := by
  let I := Set.Ioo (z.1 - A.radius) (z.1 + A.radius)
  have hmap : ContMDiff (𝓘(ℝ, ℝ)) ((𝓘(ℝ, Z)).prod (𝓘(ℝ, ℝ))) ∞
      (fun s : ℝ ↦ (z, s)) := contMDiff_const.prodMk contMDiff_id
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.curve z) I := by
    apply A.curve_smooth.comp hmap.contMDiffOn
    intro s hs
    refine ⟨hz, ?_, ?_⟩ <;> linarith [hs.1, hs.2]
  refine ⟨hsmooth, ?_⟩
  intro s hs
  exact (regularizedEquation_iff_local F hM04 T b hb hwindow (A.curve z)
    I I isOpen_Ioo (Set.Subset.refl _) isOpen_Ioo.uniqueDiffOn hsmooth
    (A.velocity_extension z hz) s hs (A.time_mem z hz s hs)).mp (A.equation z hz s hs)

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_regularizedIntervalSolution {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (s0 : ℝ)
    (hs0 : s0 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (q0 : TangentBundle (𝓡 n) M) :
    Nonempty (RegularizedIntervalSolution F T b s0 q0) := by
  rcases q0 with ⟨p, v⟩
  let e := chartAt V p
  let z0 : Z := (s0, (e p, (mfderiv (𝓡 n) (𝓡 n) e p) v))
  obtain ⟨A⟩ := nonempty_localRegularizedRestartFamily F hM04 T b hb hwindow p z0
    ⟨hs0, e.map_source (mem_chart_source V p)⟩
  refine ⟨{
    domain := Set.Ioo (s0 - A.radius) (s0 + A.radius)
    open_domain := isOpen_Ioo
    preconnected_domain := isPreconnected_Ioo
    initial_mem := ⟨by linarith [A.radius_pos], by linarith [A.radius_pos]⟩
    time_mem := fun s hs ↦ A.time_mem z0 A.center_mem s hs
    curve := A.curve z0
    isLocal := A.isLocalRegularizedCurveOn hM04 hb hwindow z0 A.center_mem
    initial_phase := ?_
  }⟩
  rw [A.initial_phase z0 A.center_mem]
  apply Bundle.TotalSpace.ext (e.left_inv (mem_chart_source V p))
  apply heq_of_eq
  exact congrArg (fun L : TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p ↦ L v)
    ((mdifferentiable_chart (I := 𝓡 n) p).symm_comp_deriv (mem_chart_source V p))

end PoincareConjecture.Proofs.M09
