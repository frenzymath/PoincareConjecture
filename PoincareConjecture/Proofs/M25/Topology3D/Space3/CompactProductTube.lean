import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldOpenChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.UniformTube
import Mathlib.Tactic.Linarith













set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem exists_manifold_source_regular_neighborhood (f : M → F) {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (x : M) (hx : x ∈ U)
    (hb : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ InjOn f V ∧
      ∀ y ∈ V, Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y) := by
  obtain ⟨e, hxe, heU, hef, hei⟩ :=
    exists_manifold_source_local_inverse f hU hf x hx hb
  have hes : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e e.source :=
    (hf.mono heU).congr (fun y hy => hef hy)
  have hed : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨hes.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  refine ⟨e.source, e.open_source, hxe, heU, ?_, ?_⟩
  · intro y hy z hz hyz
    apply e.injOn hy hz
    rw [hef hy, hef hz]
    exact hyz
  · intro y hy
    have heq : (e : M → F) =ᶠ[𝓝 y] f := by
      filter_upwards [e.open_source.mem_nhds hy] with z hz
      exact hef hz
    have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e y =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y := heq.mfderiv_eq
    rw [← hd]
    exact hed.mfderiv_bijective hy

variable [CompactSpace M]




theorem exists_compact_product_regular_tube (C : M × ℝ → F) {U : Set (M × ℝ)}
    (hU : IsOpen U) (hzero : ∀ p : M, (p, (0 : ℝ)) ∈ U)
    (hC : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ C U)
    (hinj : Function.Injective (fun p : M => C (p, 0)))
    (hderiv : ∀ p : M, Function.Bijective
      (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) C (p, 0))) :
    ∃ d > (0 : ℝ), univ ×ˢ Ioo (-d) d ⊆ U ∧
      InjOn C (univ ×ˢ Ioo (-d) d) ∧
      ∀ z ∈ (univ ×ˢ Ioo (-d) d : Set (M × ℝ)), Function.Bijective
        (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) C z) := by
  classical
  let : ChartedSpace (E × ℝ) (M × ℝ) := prodChartedSpace E M ℝ ℝ
  let : IsManifold 𝓘(ℝ, E × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod M ℝ
  have hC' : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ∞ C U := by
    rwa [modelWithCornersSelf_prod]
  have hlocal (p : M) :
      ∃ V : Set (M × ℝ), IsOpen V ∧ (p, (0 : ℝ)) ∈ V ∧ V ⊆ U ∧
        InjOn C V ∧ ∀ z ∈ V, Function.Bijective
          (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) C z) := by
    have hp : Function.Bijective (mfderiv 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) C (p, 0)) := by
      rw [modelWithCornersSelf_prod]
      exact hderiv p
    have h := exists_manifold_source_regular_neighborhood C hU hC' (p, 0) (hzero p) hp
    rwa [modelWithCornersSelf_prod] at h
  choose V hVo hVp hVU hVi hVd using hlocal
  let W : Set (M × ℝ) := ⋃ p : M, V p
  have hWo : IsOpen W := isOpen_iUnion hVo
  have hWU : W ⊆ U := by
    intro z hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    exact hVU p hp
  have hWzero : univ ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨p, s⟩ ⟨_, rfl⟩
    exact mem_iUnion.mpr ⟨p, hVp p⟩
  obtain ⟨A, B, _, hB, hA, hzeroB, hAB⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hWo hWzero
  obtain ⟨dr, hdr, hball⟩ :=
    Metric.mem_nhds_iff.mp (hB.mem_nhds (hzeroB (mem_singleton 0)))
  have hregular : univ ×ˢ Ioo (-dr) dr ⊆ W := by
    intro z hz
    apply hAB
    refine ⟨hA hz.1, hball ?_⟩
    change dist z.2 0 < dr
    rw [Real.dist_eq, sub_zero]
    exact abs_lt.mpr hz.2
  obtain ⟨di, hdi, hi⟩ := exists_injective_uniform_tube C hinj
    (fun p => (hC.contMDiffAt (hU.mem_nhds (hzero p))).continuousAt)
    (fun p => ⟨V p, (hVo p).mem_nhds (hVp p), hVi p⟩)
  let d := min dr di / 2
  have hd : 0 < d := div_pos (lt_min hdr hdi) (by norm_num)
  have hdr' : d < dr := by
    dsimp [d]
    linarith [min_le_left dr di]
  have hdi' : d < di := by
    dsimp [d]
    linarith [min_le_right dr di]
  have hsubr : univ ×ˢ Ioo (-d) d ⊆ (univ ×ˢ Ioo (-dr) dr : Set (M × ℝ)) := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hsubi : univ ×ˢ Ioo (-d) d ⊆ (univ ×ˢ Ioo (-di) di : Set (M × ℝ)) := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  refine ⟨d, hd, hsubr.trans (hregular.trans hWU), hi.mono hsubi, ?_⟩
  intro z hz
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hregular (hsubr hz))
  exact hVd p z hp

end PoincareConjecture.M25.Topology3D
