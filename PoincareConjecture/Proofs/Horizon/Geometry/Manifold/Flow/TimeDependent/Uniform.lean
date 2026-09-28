import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Local
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.JointInverse








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem exists_locally_uniform_smooth_timeDependentFlows
    {J : Set ℝ} (hJ : IsOpen J)
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    {s : ℝ} (hs : s ∈ J) (p : M) :
    ∃ (N : Set (ℝ × M)) (δ : ℝ), IsOpen N ∧ (s, p) ∈ N ∧ 0 < δ ∧
      ∀ z ∈ N, ∃ (V : Set M) (Φ : ℝ × M → M),
        IsOpen V ∧ z.2 ∈ V ∧ Ioo (z.1 - δ) (z.1 + δ) ⊆ J ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
          (Ioo (z.1 - δ) (z.1 + δ) ×ˢ V) ∧
        (∀ y ∈ V, Φ (z.1, y) = y) ∧
        (∀ y ∈ V, ∀ t ∈ Ioo (z.1 - δ) (z.1 + δ),
          HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => Φ (r, y)) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ (t, y))))) := by
  obtain ⟨V, ε, Φ, hV, hpV, hε, hεJ, hΦ, hi, hsol⟩ :=
    exists_smooth_local_timeDependentFlow hJ hX hs p
  have hsε : s ∈ Ioo (s - ε) (s + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨W, ψ, hW, hspW, hψ, hright⟩ :=
    exists_smooth_spatial_rightInverse_near_initial isOpen_Ioo hV hΦ hsε hi hpV
  have hWn := hW.mem_nhds hspW
  rw [nhds_prod_eq] at hWn
  obtain ⟨T₀, hT₀, U₀, hU₀, hTU⟩ := Filter.mem_prod_iff.mp hWn
  obtain ⟨T, hTT₀, hT, hsT⟩ := mem_nhds_iff.mp hT₀
  obtain ⟨U, hUU₀, hU, hpU⟩ := mem_nhds_iff.mp hU₀
  let N := (T ∩ Ioo (s - ε / 2) (s + ε / 2)) ×ˢ U
  have hNW : N ⊆ W := fun z hz => hTU ⟨hTT₀ hz.1.1, hUU₀ hz.2⟩
  refine ⟨N, ε / 2, (hT.inter isOpen_Ioo).prod hU,
    ⟨⟨hsT, by constructor <;> linarith⟩, hpU⟩, by positivity, ?_⟩
  rintro ⟨r, x⟩ ⟨hr, hx⟩
  have hUright (y : M) (hy : y ∈ U) := hright (r, y) (hNW ⟨hr, hy⟩)
  have hpsir : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (fun y => ψ (r, y)) U :=
    hψ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun y hy => hNW ⟨hr, hy⟩)
  have hsub : Ioo (r - ε / 2) (r + ε / 2) ⊆ Ioo (s - ε) (s + ε) := by
    intro t ht
    constructor <;> linarith [hr.2.1, hr.2.2, ht.1, ht.2]
  refine ⟨U, fun z => Φ (z.1, ψ (r, z.2)), hU, hx, hsub.trans hεJ, ?_, ?_, ?_⟩
  · exact hΦ.comp
      (contMDiff_fst.contMDiffOn.prodMk
        (hpsir.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2)))
      (fun z hz => ⟨hsub hz.1, (hUright z.2 hz.2).2.1⟩)
  · exact fun y hy => (hUright y hy).2.2
  · exact fun y hy t ht => hsol (ψ (r, y)) (hUright y hy).2.1 t (hsub ht)



theorem exists_uniform_smooth_local_timeDependentFlows
    {J : Set ℝ} (hJ : IsOpen J)
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    {K : Set (ℝ × M)} (hK : IsCompact K) (hKJ : K ⊆ J ×ˢ univ) :
    ∃ δ > 0, ∀ z ∈ K, ∃ (V : Set M) (Φ : ℝ × M → M),
      IsOpen V ∧ z.2 ∈ V ∧ Ioo (z.1 - δ) (z.1 + δ) ⊆ J ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (z.1 - δ) (z.1 + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (z.1, y) = y) ∧
      (∀ y ∈ V, ∀ t ∈ Ioo (z.1 - δ) (z.1 + δ),
        HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => Φ (r, y)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ (t, y))))) := by
  let P : (ℝ × M) → ℝ → Prop := fun z δ =>
    ∃ (V : Set M) (Φ : ℝ × M → M),
      IsOpen V ∧ z.2 ∈ V ∧ Ioo (z.1 - δ) (z.1 + δ) ⊆ J ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (z.1 - δ) (z.1 + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (z.1, y) = y) ∧
      (∀ y ∈ V, ∀ t ∈ Ioo (z.1 - δ) (z.1 + δ),
        HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => Φ (r, y)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ (t, y)))))
  have hmono {z : ℝ × M} {δ ε : ℝ} (hδε : δ ≤ ε) : P z ε → P z δ := by
    rintro ⟨V, Φ, hV, hzV, hJ', hΦ, hi, hsol⟩
    have hsub : Ioo (z.1 - δ) (z.1 + δ) ⊆ Ioo (z.1 - ε) (z.1 + ε) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    exact ⟨V, Φ, hV, hzV, hsub.trans hJ', hΦ.mono (prod_mono hsub subset_rfl),
      hi, fun y hy t ht => hsol y hy t (hsub ht)⟩
  change ∃ δ > 0, ∀ z ∈ K, P z δ
  refine hK.induction_on (p := fun S => ∃ δ > 0, ∀ z ∈ S, P z δ) ?_ ?_ ?_ ?_
  · exact ⟨1, zero_lt_one, fun z hz => False.elim hz⟩
  · rintro S T hST ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun z hz => h z (hST hz)⟩
  · rintro S T ⟨δ, hδ, hS⟩ ⟨ε, hε, hT⟩
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · exact hmono (min_le_left _ _) (hS z hz)
    · exact hmono (min_le_right _ _) (hT z hz)
  · rintro ⟨s, x⟩ hx
    obtain ⟨N, δ, hN, hsxN, hδ, hlocal⟩ :=
      exists_locally_uniform_smooth_timeDependentFlows hJ hX (hKJ hx).1 x
    exact ⟨N, mem_nhdsWithin_of_mem_nhds (hN.mem_nhds hsxN), δ, hδ, hlocal⟩

end Poincare.Manifold
