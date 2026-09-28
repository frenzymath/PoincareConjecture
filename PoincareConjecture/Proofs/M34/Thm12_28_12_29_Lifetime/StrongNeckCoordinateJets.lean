import PoincareConjecture.Proofs.M34.Mathlib.NeckLocalJetBounds
import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderParametrizedJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckAmbientExtension











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture.EpsilonNeck

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)




theorem exists_local_parametrization_jet_bound
    (a : M) (q₀ : UnitTwoSphere) (s₀ R : ℝ) (m : ℕ)
    (hs₀ : s₀ ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (ha : N.coordinate_map (q₀, s₀) ∈ (extChartAt (𝓡 3) a).source) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ z : RoundCylinderSpace in 𝓝 (q₀, s₀),
      z.2 ∈ Icc (-R) R → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun p : RoundCylinderCoordinates =>
          (extChartAt (𝓡 3) a)
            (N.coordinate_map ((chartAt E₂ z.1).symm p.1, p.2))) (0, z.2)‖ ≤ C := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  let φ : E₃ × ℝ → E₃ := (extChartAt (𝓡 3) a) ∘ N.ambientCoordinate
  have hφ : ContDiffAt ℝ ∞ φ ((q₀ : E₃), s₀) :=
    N.chart_ambientCoordinate_contDiffAt a (ne_zero_of_mem_unit_sphere q₀) hs₀
      (by simpa only [N.ambientCoordinate_coe] using ha)
  obtain ⟨D, hD, hjet⟩ := hφ.exists_eventually_finite_jet_bound m
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
  have haxial : ∀ᶠ z : RoundCylinderSpace in 𝓝 (q₀, s₀),
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hs₀)
  have hmap : ContinuousAt N.coordinate_map (q₀, s₀) :=
    (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs₀⟩)).continuousAt
  have hchart : ∀ᶠ z : RoundCylinderSpace in 𝓝 (q₀, s₀),
      N.coordinate_map z ∈ (extChartAt (𝓡 3) a).source :=
    hmap.tendsto.eventually ((isOpen_extChartAt_source a).mem_nhds ha)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hnear, haxial, hchart] with z hz hzs hzc hs j hj
  let θ : RoundCylinderCoordinates → E₃ × ℝ := fun p =>
    (((chartAt E₂ z.1).symm p.1 : E₃), p.2)
  have hcenter : θ (0, z.2) = ((z.1 : E₃), z.2) := by
    dsimp only [θ]
    rw [sphere_chart_symm_zero]
  have hθ : ContDiffAt ℝ ∞ θ (0, z.2) :=
    (contDiff_included_sphereCylinder_chart z.1).contDiffAt
  have hφz : ContDiffAt ℝ ∞ φ (θ (0, z.2)) := by
    rw [hcenter]
    exact N.chart_ambientCoordinate_contDiffAt a (ne_zero_of_mem_unit_sphere z.1) hzs
      (by simpa only [N.ambientCoordinate_coe] using hzc)
  have hθjet (l : ℕ) (hl : l ≤ m) :
      ‖iteratedFDeriv ℝ l θ (0, z.2)‖ ≤ B₀ := by
    let i : Fin (m + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
    exact (hBb i z.1 (0, z.2) (by simp) hs).trans
      ((Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ i)).trans (le_max_right _ _))
  have hφjet (l : ℕ) (hl : l ≤ m) :
      ‖iteratedFDeriv ℝ l φ (θ (0, z.2))‖ ≤ D := by
    rw [hcenter]
    exact hz l hl
  have heq : (fun p : RoundCylinderCoordinates => (extChartAt (𝓡 3) a)
      (N.coordinate_map ((chartAt E₂ z.1).symm p.1, p.2))) = φ ∘ θ := by
    funext p
    exact congrArg (extChartAt (𝓡 3) a) (N.ambientCoordinate_coe _ _).symm
  rw [heq]
  exact hcomp θ φ (0, z.2) hθ hφz hθjet hφjet j hj

end PoincareConjecture.EpsilonNeck
