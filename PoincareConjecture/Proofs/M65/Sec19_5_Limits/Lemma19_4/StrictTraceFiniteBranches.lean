import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceBoundaryAlternative
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceContinuation
import Mathlib.Topology.DiscreteSubset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65StrictTrace

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem not_within_local_zero_of_Jordan_trace (D : LeviCivitaData g)
    {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (hei : Function.Injective e)
    {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (ball (0 : LoopPlane) 1))
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hharm : ∀ z ∈ ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    {gamma : LoopCircle → M} (hgamma : Function.Injective gamma)
    {beta : LoopCircle → LoopCircle} (hbeta : Function.Surjective beta)
    (htrace : ∀ z : LoopCircle, f z = gamma (beta z))
    {x : LoopPlane} (hx : x ∈ loopDiskSet) :
    ¬∀ᶠ y in 𝓝[loopDiskSet] x,
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet y = 0 := by
  intro hzero
  obtain ⟨W, hW, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hzero
  obtain ⟨O, hOW, hO, hxO⟩ := _root_.mem_nhds_iff.mp hW
  have hxcl : x ∈ closure (ball (0 : LoopPlane) 1) := by
    rw [closure_ball (0 : LoopPlane) one_ne_zero]
    exact hx
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff_nhds.mp hxcl O (hO.mem_nhds hxO)
  apply not_local_zero_of_Jordan_trace D he hei hf hb hharm hgamma hbeta htrace hy
  filter_upwards [hO.mem_nhds hyO, isOpen_ball.mem_nhds hy] with z hzO hz
  have hzK : loopDiskSet ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have hd := hsub ⟨hOW hzO, ball_subset_closedBall hz⟩
  change mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0 at hd
  rwa [mfderivWithin_of_mem_nhds hzK] at hd

omit [T2Space M] in

theorem isCompact_disk_branches (f : LoopPlane → M)
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    IsCompact {z : LoopPlane | z ∈ loopDiskSet ∧
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0} := by
  let : CompactSpace LoopDisk :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : LoopPlane) 1)
  have hc : Continuous (fun z : LoopDisk => diskConformalFactor g f z) :=
    (diskConformalFactor_continuousOn g f hb).domRestrict
  have hclosed : IsClosed {z : LoopDisk | diskConformalFactor g f z = 0} :=
    isClosed_eq hc continuous_const
  have hcompact := hclosed.isCompact.image continuous_subtype_val
  convert hcompact using 1
  ext z
  constructor
  · rintro ⟨hz, hd⟩
    exact ⟨⟨z, hz⟩, (diskConformalFactor_eq_zero_iff g f hb hconf hz).mpr hd, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, (diskConformalFactor_eq_zero_iff g f hb hconf w.property).mp hw⟩

theorem finite_disk_branches (D : LeviCivitaData g)
    {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (hei : Function.Injective e)
    {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (ball (0 : LoopPlane) 1))
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hharm : ∀ z ∈ ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    {gamma : LoopCircle → M} (hgamma : Continuous gamma)
    (hinj : Function.Injective gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {beta : LoopCircle → LoopCircle} (hbeta : Function.Surjective beta)
    (htrace : ∀ z : LoopCircle, f z = gamma (beta z)) :
    {z : LoopPlane | z ∈ loopDiskSet ∧
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0}.Finite := by
  have hisolated (x : LoopPlane) (hx : x ∈ loopDiskSet) :
      ∀ᶠ y in 𝓝[loopDiskSet] x,
        mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet y = 0 → y = x := by
    by_cases hi : x ∈ ball (0 : LoopPlane) 1
    · have h := (interior_differential_zero_alternative D hf hb hharm hi).resolve_left
        (not_local_zero_of_Jordan_trace D he hei hf hb hharm hinj hbeta htrace hi)
      have hball : ∀ᶠ y : LoopPlane in 𝓝 x, y ∈ ball (0 : LoopPlane) 1 :=
        isOpen_ball.mem_nhds hi
      filter_upwards [h.filter_mono nhdsWithin_le_nhds,
        hball.filter_mono nhdsWithin_le_nhds] with y hy hyi hdy
      apply hy
      have hyK : loopDiskSet ∈ 𝓝 y :=
        mem_of_superset (isOpen_ball.mem_nhds hyi) ball_subset_closedBall
      rwa [mfderivWithin_of_mem_nhds hyK] at hdy
    · have hnorm : ‖x‖ = 1 := by
        have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
        have hge : ¬‖x‖ < 1 := by simpa only [mem_ball_zero_iff] using hi
        exact le_antisymm hle (le_of_not_gt hge)
      exact (boundary_differential_zero_alternative D hf hb hconf hharm hgamma hinj
        hsmooth hregular beta htrace hnorm).resolve_left
        (not_within_local_zero_of_Jordan_trace D he hei hf hb hharm hinj hbeta htrace hx)
  apply (isCompact_disk_branches f hb hconf).finite
  apply IsDiscrete.of_nhdsWithin
  intro x hx
  apply Filter.le_pure_iff.mpr
  filter_upwards [(hisolated x hx.1).filter_mono
    (nhdsWithin_mono x (fun _ hy => hy.1)), self_mem_nhdsWithin] with y hy hyB
  exact hy hyB.2

end PoincareConjecture.M65StrictTrace
