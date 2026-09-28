import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.UpperLevel.Equation
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.EmbeddedCircle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Nested
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

def upperReconstruction (q : E2) : E3 := vector (q 0) (q 1) (upperSourceHeight q)

theorem upperReconstruction_contDiff : ContDiff Real ∞ upperReconstruction := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff Real ∞ (fun q : E2 => q 0)
    fun_prop
  · change ContDiff Real ∞ (fun q : E2 => q 1)
    fun_prop
  · change ContDiff Real ∞ upperSourceHeight
    unfold upperSourceHeight
    fun_prop

theorem upperReconstruction_mem {q : E2} (hq : q ∈ upperLevelSet) :
    upperReconstruction q ∈ sphere (0 : E3) 1 := by
  have hn : ‖upperReconstruction q‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, upperReconstruction,
      vector_zero, vector_one, vector_two]
    rw [← norm_sq_two]
    exact hq
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (upperReconstruction q)]

private def projectionBase : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩

def upperSphereMap (q : E2) : S2 :=
  Plane.unitRadialProjection projectionBase (upperReconstruction q)

theorem upperSphereMap_coe {q : E2} (hq : q ∈ upperLevelSet) :
    (upperSphereMap q : E3) = upperReconstruction q :=
  congrArg Subtype.val (Plane.unitRadialProjection_apply_coe projectionBase
    ⟨upperReconstruction q, upperReconstruction_mem hq⟩)

theorem upperSphereMap_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ upperSphereMap upperLevelSet := by
  apply (Plane.contMDiffOn_unitRadialProjection (n := 2) (m := ∞) projectionBase).comp
    upperReconstruction_contDiff.contMDiff.contMDiffOn
  intro q hq
  exact ne_zero_of_mem_unit_sphere ⟨upperReconstruction q, upperReconstruction_mem hq⟩

theorem upperSphereMap_image : upperSphereMap '' upperLevelSet = height ⁻¹' {13 / 10} := by
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    change height (upperSphereMap q) = 13 / 10
    rw [height_apply, upperSphereMap_coe hq]
    simp only [upperReconstruction, vector_zero, vector_one, vector_two]
    dsimp [upperSourceHeight]
    ring
  · intro p hp
    change height p = 13 / 10 at hp
    let q : E2 := WithLp.toLp 2 ![(p : E3) 0, (p : E3) 1]
    have hq₀ : q 0 = (p : E3) 0 := rfl
    have hq₁ : q 1 = (p : E3) 1 := rfl
    have hq₂ : upperSourceHeight q = (p : E3) 2 := by
      rw [height_apply] at hp
      dsimp [upperSourceHeight]
      rw [hq₀, hq₁]
      linarith
    have hq : q ∈ upperLevelSet := by
      change ‖q‖^2 + (upperSourceHeight q)^2 = 1
      rw [norm_sq_two, hq₀, hq₁, hq₂]
      have hn := EuclideanSpace.norm_sq_eq (p : E3)
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
      exact hn.symm
    refine ⟨q, hq, ?_⟩
    apply Subtype.ext
    rw [upperSphereMap_coe hq]
    ext i
    fin_cases i
    · exact hq₀
    · exact hq₁
    · exact hq₂

theorem isConnected_upper_height_level : IsConnected (height ⁻¹' {(13 / 10 : Real)}) := by
  rw [← upperSphereMap_image]
  exact isConnected_upperLevelSet.image _ upperSphereMap_smooth.continuousOn


theorem exists_smooth_circle_upper_height_level :
    ∃ γ : S1 → S2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ γ ∧ Function.Injective γ ∧
      (∀ p, Function.Injective (mfderiv (𝓡 1) (𝓡 2) γ p)) ∧
      range γ = height ⁻¹' {(13 / 10 : Real)} := by
  obtain ⟨p, hp⟩ := isConnected_upper_height_level.nonempty
  obtain ⟨γ, hγ, hinj, hder, hrange⟩ := exists_smooth_circle_regularLevelComponent
    height_contMDiff (13 / 10) (fun p hp => nested_cutting_heights_regular p (Or.inr hp)) p hp
  refine ⟨γ, hγ, hinj, hder, ?_⟩
  rw [hrange]
  exact Subset.antisymm (connectedComponentIn_subset _ _)
    (isConnected_upper_height_level.isPreconnected.subset_connectedComponentIn hp subset_rfl)

theorem card_connectedComponents_upper_height_level :
    Nat.card (ConnectedComponents ↥(height ⁻¹' {(13 / 10 : Real)})) = 1 := by
  let : ConnectedSpace ↥(height ⁻¹' {(13 / 10 : Real)}) :=
    isConnected_iff_connectedSpace.mp isConnected_upper_height_level
  exact Nat.card_unique

end Poincare.Manifold.Schoenflies.Saddle.Nested

end

end M38Schoenflies
