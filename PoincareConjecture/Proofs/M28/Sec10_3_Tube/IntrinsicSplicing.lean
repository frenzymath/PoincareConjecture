import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicCompetitors

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_flat_intrinsic_path (g : RiemannianMetric 3 M)
    {U : Set M} {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1))
    (hγU : MapsTo γ (Icc (0 : ℝ) 1) U) (hab : a < b) :
    ∃ σ : ℝ → M, σ a = γ 0 ∧ σ b = γ 1 ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 σ ∧ MapsTo σ univ U ∧
      g.pathELength σ a b = g.pathELength γ 0 1 ∧
      σ =ᶠ[𝓝 a] (fun _ => γ 0) ∧ σ =ᶠ[𝓝 b] (fun _ => γ 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a', haa', ha'b⟩ := exists_between hab
  obtain ⟨b', ha'b', hb'b⟩ := exists_between ha'b
  let η (t : ℝ) : ℝ := Real.smoothTransition ((b' - a')⁻¹ * (t - a'))
  have hzero (t : ℝ) (ht : t < a') : η t = 0 := by
    simp only [η, Real.smoothTransition.zero_iff_nonpos]
    apply mul_nonpos_of_nonneg_of_nonpos
    · simpa using ha'b'.le
    · linarith
  have hone (t : ℝ) (ht : b' < t) : η t = 1 := by
    simp only [η, Real.smoothTransition.eq_one_iff_one_le, inv_mul_eq_div]
    rw [one_le_div₀] <;> linarith
  have hη : MapsTo η univ (Icc (0 : ℝ) 1) := by
    intro t _
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨γ ∘ η, by simp [hzero a haa'], by simp [hone b hb'b], ?_,
    hγU.comp hη, ?_, ?_, ?_⟩
  · rw [← contMDiffOn_univ]
    apply hγ.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · exact hη
  · rw [← hzero a haa', ← hone b hb'b]
    apply Manifold.pathELength_comp_of_monotoneOn hab.le
    · apply Monotone.monotoneOn
      apply Real.smoothTransition.monotone.comp
      intro t u htu
      dsimp only
      gcongr
    · simp only [η]
      apply (ContDiff.contDiffOn _).differentiableOn one_ne_zero
      fun_prop
    · rw [hzero a haa', hone b hb'b]
      exact hγ.mdifferentiableOn one_ne_zero
  · filter_upwards [Iio_mem_nhds haa'] with t ht
    simp [hzero t ht]
  · filter_upwards [Ioi_mem_nhds hb'b] with t ht
    simp [hone t ht]

theorem exists_intrinsic_splice (g : RiemannianMetric 3 M)
    {U : Set M} {α β : ℝ → M}
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 α (Icc (0 : ℝ) 1))
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 β (Icc (0 : ℝ) 1))
    (hαU : MapsTo α (Icc (0 : ℝ) 1) U)
    (hβU : MapsTo β (Icc (0 : ℝ) 1) U) (hjoin : α 1 = β 0) :
    ∃ σ : ℝ → M, σ 0 = α 0 ∧ σ 1 = β 1 ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 = g.pathELength α 0 1 + g.pathELength β 0 1 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨α', hα0, _, hα', hαU', hαlen, _, hαend⟩ :=
    exists_flat_intrinsic_path g hα hαU zero_lt_one
  obtain ⟨β', _, hβ2, hβ', hβU', hβlen, hβstart, _⟩ :=
    exists_flat_intrinsic_path g hβ hβU one_lt_two
  have hmatch : α' =ᶠ[𝓝 (1 : ℝ)] β' := by
    have hαend' : α' =ᶠ[𝓝 (1 : ℝ)] (fun _ => β 0) := by
      simpa only [hjoin] using hαend
    exact hαend'.trans hβstart.symm
  let τ := piecewise (Iic (1 : ℝ)) α' β'
  have hτ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 τ :=
    hα'.piecewise_Iic hβ' hmatch
  have hτU : MapsTo τ univ U := by
    intro t _
    by_cases ht : t ≤ 1
    · simp only [τ, piecewise, mem_Iic, if_pos ht]
      exact hαU' (mem_univ t)
    · simp only [τ, piecewise, mem_Iic, if_neg ht]
      exact hβU' (mem_univ t)
  have hτ0 : τ 0 = α 0 := by simp [τ, hα0]
  have hτ2 : τ 2 = β 1 := by simp [τ, hβ2]
  have hfirst : g.pathELength τ 0 1 = g.pathELength α' 0 1 := by
    apply Manifold.pathELength_congr
    intro t ht
    simp [τ, ht.2]
  have hsecond : g.pathELength τ 1 2 = g.pathELength β' 1 2 := by
    apply Manifold.pathELength_congr_Ioo
    intro t ht
    simp [τ, not_le.mpr ht.1]
  have hτlen : g.pathELength τ 0 2 =
      g.pathELength α 0 1 + g.pathELength β 0 1 := by
    calc
      g.pathELength τ 0 2 = g.pathELength τ 0 1 + g.pathELength τ 1 2 :=
        (Manifold.pathELength_add zero_le_one one_le_two).symm
      _ = g.pathELength α 0 1 + g.pathELength β 0 1 := by
        rw [hfirst, hsecond, hαlen, hβlen]
  obtain ⟨σ, h0, h1, hσ, hσU, hσlen⟩ :=
    exists_unit_interval_path g zero_le_two hτ.contMDiffOn
      (fun t _ => hτU (mem_univ t))
  exact ⟨σ, h0.trans hτ0, h1.trans hτ2, hσ, hσU, hσlen.trans hτlen⟩

theorem exists_intrinsic_subarc_replacement (g : RiemannianMetric 3 M)
    {U : Set M} {γ α : ℝ → M} {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 α (Icc (0 : ℝ) 1))
    (hαU : MapsTo α (Icc (0 : ℝ) 1) U)
    (hα0 : α 0 = γ c) (hα1 : α 1 = γ d) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 =
        g.pathELength γ a c + g.pathELength α 0 1 + g.pathELength γ d b := by
  have hleft : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl (hcd.trans hdb)
  have hright : Icc d b ⊆ Icc a b := Icc_subset_Icc (hac.trans hcd) le_rfl
  obtain ⟨β, hβ0, hβ1, hβ, hβU, hβlen⟩ :=
    exists_unit_interval_path g hac (hγ.mono hleft) (fun _ ht => hγU (hleft ht))
  obtain ⟨η, hη0, hη1, hη, hηU, hηlen⟩ :=
    exists_unit_interval_path g hdb (hγ.mono hright) (fun _ ht => hγU (hright ht))
  obtain ⟨τ, hτ0, hτ1, hτ, hτU, hτlen⟩ :=
    exists_intrinsic_splice g hβ hα hβU hαU (hβ1.trans hα0.symm)
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσlen⟩ :=
    exists_intrinsic_splice g hτ hη hτU hηU ((hτ1.trans hα1).trans hη0.symm)
  refine ⟨σ, (hσ0.trans hτ0).trans hβ0, hσ1.trans hη1, hσ, hσU, ?_⟩
  rw [hσlen, hτlen, hβlen, hηlen]

end PoincareConjecture.M28
