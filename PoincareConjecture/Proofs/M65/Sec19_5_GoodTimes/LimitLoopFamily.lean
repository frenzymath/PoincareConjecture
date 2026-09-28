import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.ChartLoopLimit
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.ImmersedAreaTransfer










set_option autoImplicit false

open Set Filter Bundle
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in


theorem m65TimeSlice_contMDiff {J : Set ℝ} (hJ : IsOpen J)
    (c : ℝ → ℝ → M)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ (fun z => c z.2 z.1) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun x => c x t) := by
  intro x
  have h := hc.contMDiffAt (x := (t, x))
    ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hs : ContDiff ℝ ∞ (fun y : ℝ => (t, y)) := contDiff_const.prodMk contDiff_id
  exact (h.comp x hs.contMDiff.contMDiffAt).of_le (by simp)




theorem m65PeriodicFamily_exists_loops {J : Set ℝ} (hJ : IsOpen J)
    (c : ℝ → ℝ → M)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ (fun z => c z.2 z.1) (J ×ˢ univ))
    (hp : ∀ t ∈ J, ∀ x, c (x + curvePeriod) t = c x t)
    (fallback : C1FreeLoopSpace (M := M)) :
    ∃ loops : ℝ → C1FreeLoopSpace (M := M),
      ∀ t ∈ J, ∀ x, periodicFreeLoop (loops t) x = c x t := by
  classical
  let loops (t : ℝ) : C1FreeLoopSpace (M := M) :=
    if ht : t ∈ J then
      m65LoopOfPeriodic (fun x => c x t) (m65TimeSlice_contMDiff hJ c hc ht) (hp t ht)
    else fallback
  refine ⟨loops, ?_⟩
  intro t ht x
  simp only [loops, dif_pos ht]
  exact m65PeriodicFreeLoop_loopOfPeriodic _ _ _ x

set_option maxHeartbeats 600000 in




theorem m65SmoothFilledLoopFamily_of_values
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    {J : Set ℝ} (hJ : IsOpen J) (c : ℝ → ℝ → M)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ (fun z => c z.2 z.1) (J ×ˢ univ))
    (hgeom : ∀ t ∈ J, ∀ x,
      curveVelocity (n := 3) (fun y => c y t) x ≠ 0 ∧
      curveVelocity (n := 3) (fun q => c x q) t = m62CurvatureVector F c t x)
    (loops : ℝ → C1FreeLoopSpace (M := M))
    (heq : ∀ t ∈ J, ∀ x, periodicFreeLoop (loops t) x = c x t)
    (hfill : ∀ t ∈ J, Nonempty (LipschitzSpanningDisk (F.metric t) (loops t))) :
    ∃ L : M65SmoothFilledLoopFamily F J, L.loops = loops ∧
      ∀ t ∈ J, ∀ x, curveVelocity (n := 3) (fun q => periodicFreeLoop (L.loops q) x) t =
        m62CurvatureVector F (fun y q => periodicFreeLoop (L.loops q) y) t x := by
  have hs (t : ℝ) (ht : t ∈ J) : periodicFreeLoop (loops t) = fun y => c y t :=
    funext (heq t ht)
  have hswap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.2, z.1)) :=
    contDiff_snd.prodMk contDiff_fst
  let L : M65SmoothFilledLoopFamily F J := {
    loops := loops
    joint_smooth := (hc.comp hswap.contMDiff.contMDiffOn
      (fun z hz => ⟨hz.2, mem_univ _⟩)).congr
        (fun z hz => heq z.2 hz.2 z.1)
    immersed := fun t ht x => by rw [hs t ht]; exact (hgeom t ht x).1
    filled := hfill }
  refine ⟨L, rfl, ?_⟩
  intro t ht x
  have htime : (fun q => periodicFreeLoop (loops q) x) =ᶠ[𝓝 t] (fun q => c x q) := by
    filter_upwards [hJ.mem_nhds ht] with q hq
    exact heq q hq x
  have hv : curveVelocity (n := 3) (fun q => periodicFreeLoop (loops q) x) t =
      curveVelocity (n := 3) (fun q => c x q) t := by
    exact congrArg (fun D : ℝ →L[ℝ] LoopAmbient => D 1)
      (htime.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  change curveVelocity (n := 3) (fun q => periodicFreeLoop (loops q) x) t = _
  rw [hv, (hgeom t ht x).2]
  let curvature (f : ℝ → M) : LoopAmbient :=
    ((F.metric t).tangentNorm (f x) (curveVelocity f x))⁻¹ •
      rampHorizontalCovariantDerivative (F.connection t) f
        (fun y => ((F.metric t).tangentNorm (f y) (curveVelocity f y))⁻¹ •
          curveVelocity f y) x
  exact congrArg curvature (hs t ht).symm

end PoincareConjecture
