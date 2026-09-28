import PoincareConjecture.Proofs.M58.Lemma18_27_FamilyContraction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set Filter Real
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture.Proofs.M58

noncomputable def diskTimeProfile (r : ℝ) : ℝ := smoothTransition (2 - 4 * r ^ 2)

theorem contDiff_diskTimeProfile : ContDiff ℝ ∞ diskTimeProfile :=
  smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2)))

theorem diskTimeProfile_mem_Icc (r : ℝ) : diskTimeProfile r ∈ Icc (0 : ℝ) 1 :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

theorem diskTimeProfile_eq_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    diskTimeProfile r = 1 := by
  apply smoothTransition.one_of_one_le
  have hsq := (sq_le_sq₀ hr0 (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hr
  nlinarith

theorem diskTimeProfile_one : diskTimeProfile 1 = 0 := by
  apply smoothTransition.zero_of_nonpos
  norm_num

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

noncomputable def contractionDiskMap (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M)) (z : LoopPlane) : M := by
  classical
  exact if z = 0 then p else C (diskTimeProfile ‖z‖, p, γ.extension (radialNormalization z))

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

theorem contractionDiskMap_boundary (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q) (p : M) (γ : C1FreeLoopSpace (M := M))
    (z : LoopCircle) : contractionDiskMap C p γ z.val = γ z := by
  have hz0 : z.val ≠ 0 := by
    intro h
    simpa [h] using z.property
  rw [contractionDiskMap, if_neg hz0, z.property, diskTimeProfile_one, h0,
    radialNormalization_of_norm_eq_one z.property, γ.boundary]

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

end PoincareConjecture.Proofs.M58
