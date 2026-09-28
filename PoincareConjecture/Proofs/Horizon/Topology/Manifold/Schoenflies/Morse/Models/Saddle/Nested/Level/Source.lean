import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Components
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Regularity
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

def lowerReconstruction (q : E2) : E3 := vector (q 0) (q 1) (sourceHeight q)

theorem lowerReconstruction_continuous : Continuous lowerReconstruction := by
  unfold lowerReconstruction vector sourceHeight
  fun_prop

theorem lowerReconstruction_mem {q : E2} (hq : q ∈ levelSet) :
    lowerReconstruction q ∈ sphere (0 : E3) 1 := by
  have hn : ‖lowerReconstruction q‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, lowerReconstruction,
      vector_zero, vector_one, vector_two]
    rw [← norm_sq_two]
    exact (mem_levelSet_iff q).mp hq
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (lowerReconstruction q)]

private def lowerProjectionBase : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩

def lowerSphereMap (q : E2) : S2 :=
  Plane.unitRadialProjection lowerProjectionBase (lowerReconstruction q)

theorem lowerSphereMap_coe {q : E2} (hq : q ∈ levelSet) :
    (lowerSphereMap q : E3) = lowerReconstruction q :=
  congrArg Subtype.val (Plane.unitRadialProjection_apply_coe lowerProjectionBase
    ⟨lowerReconstruction q, lowerReconstruction_mem hq⟩)

theorem lowerSphereMap_continuousOn : ContinuousOn lowerSphereMap levelSet := by
  apply (Plane.contMDiffOn_unitRadialProjection (n := 2) (m := ∞)
    lowerProjectionBase).continuousOn.comp lowerReconstruction_continuous.continuousOn
  intro q hq
  exact ne_zero_of_mem_unit_sphere ⟨lowerReconstruction q, lowerReconstruction_mem hq⟩

theorem lowerSphereMap_image : lowerSphereMap '' levelSet = height ⁻¹' {(1 : Real)} := by
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    change height (lowerSphereMap q)=1
    rw [height_apply, lowerSphereMap_coe hq]
    simp only [lowerReconstruction, vector_zero, vector_one, vector_two]
    dsimp [sourceHeight]
    ring
  · intro p hp
    change height p=1 at hp
    let q : E2 := WithLp.toLp 2 ![(p : E3) 0, (p : E3) 1]
    have hq₀ : q 0=(p : E3) 0 := rfl
    have hq₁ : q 1=(p : E3) 1 := rfl
    have hq₂ : sourceHeight q=(p : E3) 2 := by
      rw [height_apply] at hp
      dsimp [sourceHeight]
      rw [hq₀, hq₁]
      linarith
    have hq : q ∈ levelSet := by
      rw [mem_levelSet_iff, norm_sq_two, hq₀, hq₁, hq₂]
      have hn := EuclideanSpace.norm_sq_eq (p : E3)
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
      exact hn.symm
    refine ⟨q, hq, ?_⟩
    apply Subtype.ext
    rw [lowerSphereMap_coe hq]
    ext i
    fin_cases i
    · exact hq₀
    · exact hq₁
    · exact hq₂

def outerSourceCircle : Set S2 := lowerSphereMap '' outerOval

def innerSourceCircle : Set S2 := lowerSphereMap '' innerOval

private theorem outer_subset_level : outerOval ⊆ levelSet := by
  rw [levelSet_eq_outerOval_union_innerOval]
  exact subset_union_left

private theorem inner_subset_level : innerOval ⊆ levelSet := by
  rw [levelSet_eq_outerOval_union_innerOval]
  exact subset_union_right

theorem isConnected_outerSourceCircle : IsConnected outerSourceCircle :=
  isConnected_outerOval.image _ (lowerSphereMap_continuousOn.mono outer_subset_level)

theorem isConnected_innerSourceCircle : IsConnected innerSourceCircle :=
  isConnected_innerOval.image _ (lowerSphereMap_continuousOn.mono inner_subset_level)

theorem isCompact_outerSourceCircle : IsCompact outerSourceCircle :=
  isCompact_outerOval.image_of_continuousOn (lowerSphereMap_continuousOn.mono outer_subset_level)

theorem isCompact_innerSourceCircle : IsCompact innerSourceCircle :=
  isCompact_innerOval.image_of_continuousOn (lowerSphereMap_continuousOn.mono inner_subset_level)

theorem lower_height_level_eq_sourceCircles : height ⁻¹' {(1 : Real)} =
    outerSourceCircle ∪ innerSourceCircle := by
  rw [← lowerSphereMap_image, levelSet_eq_outerOval_union_innerOval, image_union]
  rfl

theorem outerSourceCircle_latitude {p : S2} (hp : p ∈ outerSourceCircle) :
    (p : E3) 2 ∈ Icc lowerRoot (3 / 5) := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [lowerSphereMap_coe (outer_subset_level hq)]
  exact sourceHeight_mem_of_mem_outerOval hq

theorem innerSourceCircle_latitude {p : S2} (hp : p ∈ innerSourceCircle) :
    (p : E3) 2 ∈ Icc upperRoot 1 := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [lowerSphereMap_coe (inner_subset_level hq)]
  exact sourceHeight_mem_of_mem_innerOval hq

theorem disjoint_sourceCircles : Disjoint outerSourceCircle innerSourceCircle := by
  apply disjoint_left.mpr
  intro p hp hq
  have ho := outerSourceCircle_latitude hp
  have hi := innerSourceCircle_latitude hq
  linarith [upperRoot_bounds.1, ho.2, hi.1]

private def sourceCircle (i : Fin 2) : Set S2 := ![outerSourceCircle, innerSourceCircle] i

private theorem sourceCircle_closed (i : Fin 2) : IsClosed (sourceCircle i) := by
  fin_cases i
  · exact isCompact_outerSourceCircle.isClosed
  · exact isCompact_innerSourceCircle.isClosed

private theorem sourceCircle_connected (i : Fin 2) : IsConnected (sourceCircle i) := by
  fin_cases i
  · exact isConnected_outerSourceCircle
  · exact isConnected_innerSourceCircle

private theorem sourceCircle_disjoint : Pairwise (fun i j => Disjoint (sourceCircle i) (sourceCircle j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact disjoint_sourceCircles
  · exact disjoint_sourceCircles.symm
  · exact (hij rfl).elim

private theorem sourceCircle_cover : (⋃ i, sourceCircle i) = height ⁻¹' {(1 : Real)} := by
  rw [lower_height_level_eq_sourceCircles]
  ext q
  simp [sourceCircle, Fin.exists_fin_two]

theorem connectedComponentIn_lower_of_mem_outer {p : S2} (hp : p ∈ outerSourceCircle) :
    connectedComponentIn (height ⁻¹' {(1 : Real)}) p=outerSourceCircle :=
  Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover sourceCircle sourceCircle_closed
    (fun i => (sourceCircle_connected i).isPreconnected) sourceCircle_disjoint sourceCircle_cover (i := 0) hp

theorem connectedComponentIn_lower_of_mem_inner {p : S2} (hp : p ∈ innerSourceCircle) :
    connectedComponentIn (height ⁻¹' {(1 : Real)}) p=innerSourceCircle :=
  Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover sourceCircle sourceCircle_closed
    (fun i => (sourceCircle_connected i).isPreconnected) sourceCircle_disjoint sourceCircle_cover (i := 1) hp

end Poincare.Manifold.Schoenflies.Saddle.Nested
