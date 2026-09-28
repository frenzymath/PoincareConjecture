import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.CompactSupport









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_finite_nested_contMDiff_cutoffs {K : Set M} (hK : IsCompact K)
    {α : Type v} (U : α → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∃ c : Fin N → α, ∃ ψ θ : Fin N → M → ℝ,
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ψ i)) ∧
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (θ i)) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧ (∀ i, HasCompactSupport (θ i)) ∧
      (∀ i x, 0 ≤ ψ i x ∧ ψ i x ≤ 1) ∧
      (∀ i x, 0 ≤ θ i x ∧ θ i x ≤ 1) ∧
      (∀ i, tsupport (θ i) ⊆ U (c i)) ∧
      (∀ i x, x ∈ tsupport (ψ i) → θ i =ᶠ[𝓝 x] 1) ∧
      ∀ x ∈ K, ∃ i, ψ i =ᶠ[𝓝 x] 1 := by
  classical
  have hex (x : K) : ∃ i, (x : M) ∈ U i := mem_iUnion.mp (hcover x.property)
  choose c hc using hex
  have hb (x : K) : ∃ b : SmoothBumpFunction (𝓡 n) (x : M),
      tsupport b ⊆ U (c x) := by
    obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n)
      (x : M)).mem_iff.mp ((hU (c x)).mem_nhds (hc x))
    exact ⟨b, hb⟩
  choose b hb using hb
  have hθ (x : K) := exists_contMDiff_cutoff_of_isCompact (n := n)
    (b x).hasCompactSupport (hU (c x)) (hb x)
  choose θ hθsmooth hθcompact hθsupport hθbounds hθone using hθ
  let W : K → Set M := fun x => interior {y | b x y = 1}
  have hW (x : K) : (x : M) ∈ W x :=
    mem_interior_iff_mem_nhds.mpr (b x).eventuallyEq_one
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover W (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hW ⟨x, hx⟩⟩)
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun i => c (e i).val,
    fun i => b (e i).val, fun i => θ (e i).val,
    fun i => (b (e i).val).contMDiff, fun i => hθsmooth (e i).val,
    fun i => (b (e i).val).hasCompactSupport, fun i => hθcompact (e i).val,
    fun i x => ⟨(b (e i).val).nonneg, (b (e i).val).le_one⟩,
    fun i => hθbounds (e i).val, fun i => hθsupport (e i).val,
    fun i => hθone (e i).val, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  refine ⟨e.symm ⟨i, hi⟩, ?_⟩
  change ∀ᶠ y in 𝓝 x, b (e (e.symm ⟨i, hi⟩)).val y = 1
  have hei : (e (e.symm ⟨i, hi⟩)).val = i :=
    congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)
  rw [hei]
  exact mem_interior_iff_mem_nhds.mp hxi

omit [T3Space M] [IsManifold (𝓡 n) ∞ M] in


theorem contMDiff_cutoff_mul {U : Set M} (hU : IsOpen U)
    {θ f : M → ℝ} (hθ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ θ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) (hθU : tsupport θ ⊆ U) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => θ x * f x) := by
  intro x
  by_cases hx : x ∈ tsupport θ
  · exact hθ.contMDiffAt.mul (hf.contMDiffAt (hU.mem_nhds (hθU hx)))
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_mul]

omit [T3Space M] [IsManifold (𝓡 n) ∞ M] in


theorem contMDiff_cutoff_extension {U : Set M} (hU : IsOpen U)
    {θ f : M → ℝ} (hθ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ θ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) (hθU : tsupport θ ⊆ U)
    (Q : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => θ x * f x + (1 - θ x) * Q) :=
  (contMDiff_cutoff_mul hU hθ hf hθU).add
    ((contMDiff_const.sub hθ).mul contMDiff_const)

end PoincareConjecture
