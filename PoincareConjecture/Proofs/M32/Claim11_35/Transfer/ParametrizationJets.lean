import PoincareConjecture.Proofs.M32.Mathlib.FinitePullbackJets
import PoincareConjecture.Proofs.M32.Mathlib.SphereCylinderJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition
import Mathlib.Analysis.Normed.Module.Normalize















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators RealInnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture.M32

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private noncomputable def cylinderRadialDirection (x : E₃) : UnitTwoSphere := by
  classical
  exact if hx : x = 0 then ⟨EuclideanSpace.single 0 1, by simp⟩ else
    ⟨NormedSpace.normalize x, by
      simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩

private theorem cylinderRadialDirection_coe {x : E₃} (hx : x ≠ 0) :
    (cylinderRadialDirection x : E₃) = NormedSpace.normalize x := by
  simp only [cylinderRadialDirection, dif_neg hx]

private theorem cylinderRadialDirection_unit (q : UnitTwoSphere) :
    cylinderRadialDirection (q : E₃) = q := by
  apply Subtype.ext
  rw [cylinderRadialDirection_coe (ne_zero_of_mem_unit_sphere q)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere q)

private theorem cylinderRadialDirection_contMDiffAt {x : E₃} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 2) ∞ cylinderRadialDirection x := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y => (cylinderRadialDirection y : E₃)) x := by
    rw [contMDiffAt_iff_contDiffAt]
    apply (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul
      contDiffAt_id).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact cylinderRadialDirection_coe hy
  rw [contMDiffAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousAt, ?_⟩
  let v := -cylinderRadialDirection x
  let U : _ ≃ₗᵢ[ℝ] _ := (OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere v)).repr
  have hv : innerSL ℝ (v : E₃) (cylinderRadialDirection x : E₃) ≠ 1 := by
    have hn := norm_eq_of_mem_sphere (cylinderRadialDirection x)
    simp only [v, coe_neg_sphere, innerSL_apply_apply, inner_neg_left,
      real_inner_self_eq_norm_sq, hn]
    norm_num
  have hs : ContDiffAt ℝ ∞ (stereoToFun (v : E₃)) (cylinderRadialDirection x : E₃) :=
    contDiffOn_stereoToFun.contDiffAt
      ((isOpen_ne.preimage (innerSL ℝ (v : E₃)).continuous).mem_nhds hv)
  have h := (U.contDiff.contDiffAt.comp (cylinderRadialDirection x : E₃) hs).contMDiffAt.comp x hf
  convert! h using 1




theorem cylinder_exists_local_parametrization_jet_bound
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
    (Phi : RoundCylinderSpace → M)
    (hPhi : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Phi)
    (a : M) (q₀ : UnitTwoSphere) (s₀ R : ℝ) (m : ℕ)
    (ha : Phi (q₀, s₀) ∈ (extChartAt (𝓡 3) a).source) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ z : RoundCylinderSpace in 𝓝 (q₀, s₀),
      z.2 ∈ Icc (-R) R → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun p : RoundCylinderCoordinates =>
          (extChartAt (𝓡 3) a) (Phi ((chartAt E₂ z.1).symm p.1, p.2))) (0, z.2)‖ ≤ D := by
  classical
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  let A : E₃ × ℝ → M := fun z => Phi (cylinderRadialDirection z.1, z.2)
  have hAcoe (q : UnitTwoSphere) (s : ℝ) : A ((q : E₃), s) = Phi (q, s) := by
    dsimp only [A]
    rw [cylinderRadialDirection_unit]
  have hA (z : E₃ × ℝ) (hz : z.1 ≠ 0) :
      ContMDiffAt 𝓘(ℝ, E₃ × ℝ) (𝓡 3) ∞ A z :=
    (hPhi _).comp z (((cylinderRadialDirection_contMDiffAt hz).comp z
      (contDiffAt_fst (𝕜 := ℝ) (n := ∞)).contMDiffAt).prodMk
        (contDiffAt_snd (𝕜 := ℝ) (n := ∞)).contMDiffAt)
  let φ : E₃ × ℝ → E₃ := (extChartAt (𝓡 3) a) ∘ A
  have hφ (q : UnitTwoSphere) (s : ℝ)
      (hq : Phi (q, s) ∈ (extChartAt (𝓡 3) a).source) :
      ContDiffAt ℝ ∞ φ ((q : E₃), s) := by
    apply contMDiffAt_iff_contDiffAt.mp
    apply ((contMDiffOn_extChartAt (I := 𝓡 3) (x := a) (n := ∞)).contMDiffAt ?_).comp
      ((q : E₃), s) (hA _ (ne_zero_of_mem_unit_sphere q))
    simpa only [hAcoe, extChartAt_source] using (isOpen_extChartAt_source a).mem_nhds hq
  obtain ⟨D, hD, hjet⟩ := exists_eventually_finite_jet_bound (hφ q₀ s₀ ha) m
  choose B hB hBb using fun j : Fin (m + 1) =>
    sphereCylinder_chart_symm_uniform_jet_bound (E := E₃) (n := 2) 0 R j
  let B₀ : ℝ := max 1 (∑ j : Fin (m + 1), B j)
  have hB₀ : 1 ≤ B₀ := le_max_left _ _
  obtain ⟨C, hC, hcomp⟩ := exists_composition_finite_jet_bound
    (E := RoundCylinderCoordinates) (F := E₃ × ℝ) (G := E₃) m hD hB₀
  have hinc : Continuous (fun z : RoundCylinderSpace => ((z.1 : E₃), z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hnear : ∀ᶠ z : RoundCylinderSpace in 𝓝 (q₀, s₀),
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j φ ((z.1 : E₃), z.2)‖ ≤ D :=
    (hinc.continuousAt (x := (q₀, s₀))).tendsto.eventually hjet
  have hchart : ∀ᶠ z : RoundCylinderSpace in 𝓝 (q₀, s₀),
      Phi z ∈ (extChartAt (𝓡 3) a).source :=
    hPhi.continuous.continuousAt.tendsto.eventually ((isOpen_extChartAt_source a).mem_nhds ha)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hnear, hchart] with z hz hzc hs j hj
  let θ : RoundCylinderCoordinates → E₃ × ℝ := fun p =>
    (((chartAt E₂ z.1).symm p.1 : E₃), p.2)
  have hcenter : θ (0, z.2) = ((z.1 : E₃), z.2) := by
    dsimp only [θ]
    rw [sphere_chart_symm_zero]
  have hθ : ContDiffAt ℝ ∞ θ (0, z.2) := by
    apply (contMDiff_iff_contDiff.mp ?_).contDiffAt
    apply (contMDiff_prod_module_iff θ).mpr
    exact ⟨((contMDiff_coe_sphere (n := 2) (m := ∞)).comp contMDiff_fst).comp
      (cylinderChart_symm_smooth z.1), contDiff_snd.contMDiff⟩
  have hθjet (l : ℕ) (hl : l ≤ m) : ‖iteratedFDeriv ℝ l θ (0, z.2)‖ ≤ B₀ := by
    let i : Fin (m + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
    exact (hBb i z.1 (0, z.2) (by simp) hs).trans
      ((Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ i)).trans (le_max_right _ _))
  have hφz : ContDiffAt ℝ ∞ φ (θ (0, z.2)) := by
    rw [hcenter]
    exact hφ z.1 z.2 hzc
  have hφjet (l : ℕ) (hl : l ≤ m) : ‖iteratedFDeriv ℝ l φ (θ (0, z.2))‖ ≤ D := by
    rw [hcenter]
    exact hz l hl
  have heq : (fun p : RoundCylinderCoordinates => (extChartAt (𝓡 3) a)
      (Phi ((chartAt E₂ z.1).symm p.1, p.2))) = φ ∘ θ := by
    funext p
    exact congrArg (extChartAt (𝓡 3) a) (hAcoe _ _).symm
  rw [heq]
  exact hcomp θ φ (0, z.2) hθ hφz hθjet hφjet j hj

end PoincareConjecture.M32
