import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_finite_bump_partition {K : Set M} (hK : IsCompact K)
    {α : Type v} (U : α → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (s : Finset K) (c : s → α) (V : Set M), IsOpen V ∧ K ⊆ V ∧
      ∃ ρ : SmoothPartitionOfUnity s (𝓡 n) M V,
        (∀ i, HasCompactSupport (ρ i : M → ℝ)) ∧
        (∀ i, tsupport (ρ i : M → ℝ) ⊆ U (c i)) := by
  classical
  have hex (x : K) : ∃ i, (x : M) ∈ U i := mem_iUnion.mp (hcover x.property)
  choose c hc using hex
  have hb (x : K) : ∃ b : SmoothBumpFunction (𝓡 n) (x : M),
      tsupport b ⊆ U (c x) := by
    obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n)
      (x : M)).mem_iff.mp ((hU (c x)).mem_nhds (hc x))
    exact ⟨b, hb⟩
  choose b hb using hb
  let W : K → Set M := fun x => interior {y | b x y = 1}
  have hW (x : K) : (x : M) ∈ W x :=
    mem_interior_iff_mem_nhds.mpr (b x).eventuallyEq_one
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover W (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hW ⟨x, hx⟩⟩)
  let V := ⋃ i : s, W i.val
  have hKV : K ⊆ V := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  let B : BumpCovering s M V :=
    { toFun := fun i => ⟨b i.val, (b i.val).continuous⟩
      locallyFinite' := locallyFinite_of_finite _
      nonneg' := fun i x => (b i.val).nonneg
      le_one' := fun i x => (b i.val).le_one
      eventuallyEq_one' := by
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact ⟨i, mem_interior_iff_mem_nhds.mp hi⟩ }
  let ρ := B.toSmoothPartitionOfUnity (fun i => (b i.val).contMDiff)
  have hsub (i : s) : tsupport (ρ i : M → ℝ) ⊆ tsupport (b i.val) := by
    exact closure_mono (B.support_toPartitionOfUnity_subset i)
  refine ⟨s, fun i => c i.val, V, isOpen_iUnion (fun _ => isOpen_interior), hKV,
    ρ, fun i => ?_, fun i => (hsub i).trans (hb i.val)⟩
  exact (b i.val).hasCompactSupport.mono' ((subset_tsupport (ρ i)).trans (hsub i))

theorem exists_contMDiff_cutoff_of_isCompact {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] 1 := by
  classical
  obtain ⟨s, c, V, hVo, hKV, ρ, hρc, hρU⟩ :=
    exists_finite_bump_partition (n := n) hK (fun _ : Unit => U)
      (fun _ => hU) (fun x hx => mem_iUnion.mpr ⟨(), hKU hx⟩)
  refine ⟨fun x => ∑ i, ρ i x, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [finsum_eq_sum_of_fintype] using ρ.contMDiff_sum
  · convert HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => hρc i) using 1
    · rfl
    · ext x
      simp
  · have hsub : tsupport (fun x => ∑ i, ρ i x) ⊆ ⋃ i, tsupport (ρ i : M → ℝ) := by
      apply closure_minimal
      · intro x hx
        by_contra h
        have hzero (i : s) : ρ i x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hi => h (mem_iUnion.mpr ⟨i, hi⟩))
        exact hx (by simp [hzero])
      · exact isClosed_iUnion_of_finite fun i => isClosed_tsupport _
    exact hsub.trans (iUnion_subset fun i => hρU i)
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using
      And.intro (ρ.sum_nonneg x) (ρ.sum_le_one x)
  · intro x hx
    filter_upwards [hVo.mem_nhds (hKV hx)] with y hy
    simpa only [finsum_eq_sum_of_fintype, Pi.one_apply] using ρ.sum_eq_one hy

end PoincareConjecture
