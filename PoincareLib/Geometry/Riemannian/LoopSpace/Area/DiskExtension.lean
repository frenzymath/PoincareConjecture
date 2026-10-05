import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.FamilyContraction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Regular disk extensions of short loops

This is the qualitative disk construction for Morgan--Tian Corollary 18.28,
printed p. 434. A cutoff makes the contraction constant near the disk center,
so the map is C1 on the entire plane and has the original boundary values.
The metric Lipschitz and quantitative area estimates are separate obligations.
See the task's disk-extension derivation for the domain checks.
-/

set_option autoImplicit false

open Set Filter Real
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareMT.LoopSpace

/-- Time profile for a cutoff filling: terminal near the center and initial
on the unit circle. Source: MT Corollary 18.28, p. 434, disk-extension derivation. -/
noncomputable def diskTimeProfile (r : ℝ) : ℝ := smoothTransition (2 - 4 * r ^ 2)

/-- The disk profile is smooth, including at zero. Source:
MT Corollary 18.28, p. 434, disk-extension derivation. -/
theorem contDiff_diskTimeProfile : ContDiff ℝ ∞ diskTimeProfile :=
  smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2)))

/-- All disk times lie in the domain of the local contraction. Source:
MT Corollary 18.28, p. 434. -/
theorem diskTimeProfile_mem_Icc (r : ℝ) : diskTimeProfile r ∈ Icc (0 : ℝ) 1 :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

/-- The profile reaches the constant endpoint throughout the inner half
disk. Source: MT Corollary 18.28, p. 434, disk-extension derivation. -/
theorem diskTimeProfile_eq_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    diskTimeProfile r = 1 := by
  apply smoothTransition.one_of_one_le
  have hsq := (sq_le_sq₀ hr0 (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hr
  nlinarith

/-- The boundary time is the original-loop endpoint. Source:
MT Corollary 18.28, p. 434. -/
theorem diskTimeProfile_one : diskTimeProfile 1 = 0 := by
  apply smoothTransition.zero_of_nonpos
  norm_num

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The total cutoff disk map; radial normalization is only used away
from zero. Source: MT Corollary 18.28, p. 434, disk-extension derivation. -/
noncomputable def contractionDiskMap (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M)) (z : LoopPlane) : M := by
  classical
  exact if z = 0 then p else C (diskTimeProfile ‖z‖, p, γ.extension (radialNormalization z))

/-- The cutoff filling is exactly constant on a neighborhood of its
center. Source: MT Corollary 18.28, p. 434, disk-extension derivation. -/
theorem contractionDiskMap_eventually_constant (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M))
    (h1 : ∀ z : LoopCircle, C (1, p, γ z) = p) :
    contractionDiskMap C p γ =ᶠ[𝓝 0] (fun _ => p) := by
  classical
  filter_upwards [Metric.ball_mem_nhds (0 : LoopPlane)
    (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
  by_cases hw0 : w = 0
  · simp [contractionDiskMap, hw0]
  · have hw' : ‖w‖ ≤ 1 / 2 := (mem_ball_zero_iff.mp hw).le
    rw [contractionDiskMap, if_neg hw0, diskTimeProfile_eq_one (norm_nonneg w) hw']
    let z : LoopCircle := ⟨radialNormalization w, norm_radialNormalization hw0⟩
    change C (1, p, γ.extension z.val) = p
    rw [γ.boundary]
    exact h1 z

/-- The cutoff disk map is genuinely C1 everywhere, including the center.
Source: MT Corollary 18.28, p. 434, disk-extension derivation. -/
theorem contMDiff_contractionDiskMap (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M))
    (h1 : ∀ z : LoopCircle, C (1, p, γ z) = p)
    (hC : ∀ (t : I) (z : LoopCircle),
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z)) :
    ContMDiff (𝓡 2) (𝓡 3) 1 (contractionDiskMap C p γ) := by
  classical
  intro w
  by_cases hw0 : w = 0
  · subst w
    exact contMDiffAt_const.congr_of_eventuallyEq
      (contractionDiskMap_eventually_constant C p γ h1)
  · let z : LoopCircle := ⟨radialNormalization w, norm_radialNormalization hw0⟩
    let t : I := ⟨diskTimeProfile ‖w‖, diskTimeProfile_mem_Icc ‖w‖⟩
    have ht : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1
        (fun v : LoopPlane => diskTimeProfile ‖v‖) w :=
      ((contDiff_diskTimeProfile.contDiffAt.comp w (contDiffAt_norm ℝ hw0)).of_le
        (by simp)).contMDiffAt
    have hinput : ContMDiffAt (𝓡 2) (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) 1
        (fun v => (diskTimeProfile ‖v‖, p, γ.extension (radialNormalization v))) w :=
      ht.prodMk (contMDiffAt_const.prodMk (contMDiffAt_radial_extension γ hw0))
    have hmain := (hC t z).comp_of_eq hinput (by
      change (diskTimeProfile ‖w‖, p, γ.extension z.val) = ((t : ℝ), p, γ z)
      rw [γ.boundary])
    apply hmain.congr_of_eventuallyEq
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw0] with v hv
    exact if_neg hv

/-- The disk has the original circle parameterization. Source:
MT Definition 18.17, p. 430, and Corollary 18.28, p. 434. -/
theorem contractionDiskMap_boundary (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q) (p : M) (γ : C1FreeLoopSpace (M := M))
    (z : LoopCircle) : contractionDiskMap C p γ z.val = γ z := by
  have hz0 : z.val ≠ 0 := by
    intro h
    simpa [h] using z.property
  rw [contractionDiskMap, if_neg hz0, z.property, diskTimeProfile_one, h0,
    radialNormalization_of_norm_eq_one z.property, γ.boundary]

/-- A uniform length threshold gives actual C1 disk extensions. The
Lipschitz and area estimates are not part of this intermediate theorem.
Source: MT Corollary 18.28, printed p. 434. -/
theorem exists_c1_disk_extension_of_short [T2Space M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M)) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ γ : C1FreeLoopSpace (M := M), freeLoopLength g γ < ζ →
      ∃ F : LoopPlane → M, ContMDiff (𝓡 2) (𝓡 3) 1 F ∧ ∀ z : LoopCircle, F z.val = γ z := by
  obtain ⟨C, U, hU, hdiagU, h0, h1, -, hC⟩ := exists_local_contraction (𝓡 3) hcompact 1
  obtain ⟨ζ, hζ, hshort⟩ := exists_short_loop_diagonal_radius g hcompact hU
    (fun p => hdiagU (by rfl : (p, p) ∈ diagonal M))
  refine ⟨ζ, hζ, ?_⟩
  intro γ hγ
  refine ⟨contractionDiskMap C (γ loopCircleBasepoint) γ, ?_,
    contractionDiskMap_boundary C h0 (γ loopCircleBasepoint) γ⟩
  exact contMDiff_contractionDiskMap C (γ loopCircleBasepoint) γ
    (fun z => h1 _ (hshort γ hγ z))
    (fun t z => hC _ ⟨t.property, hshort γ hγ z⟩)

end PoincareMT.LoopSpace
