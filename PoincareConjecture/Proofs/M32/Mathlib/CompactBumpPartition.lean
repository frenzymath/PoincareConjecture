import Mathlib.Geometry.Manifold.PartitionOfUnity












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe uE uH uM uA

namespace PoincareConjecture.M32

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M]
  [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]





theorem exists_finite_bump_partition_of_isCompact {K : Set M} (hK : IsCompact K)
    {α : Type uA} (U : α → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (s : Finset K) (c : s → α) (V : Set M), IsOpen V ∧ K ⊆ V ∧
      ∃ ρ : SmoothPartitionOfUnity s I M V,
        (∀ i, HasCompactSupport (ρ i : M → ℝ)) ∧
        (∀ i, tsupport (ρ i : M → ℝ) ⊆ U (c i)) := by
  classical
  have hex (x : K) : ∃ i, (x : M) ∈ U i := mem_iUnion.mp (hcover x.property)
  choose c hc using hex
  have hb (x : K) : ∃ b : SmoothBumpFunction I (x : M),
      tsupport b ⊆ U (c x) := by
    obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I)
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
  have hsub (i : s) : tsupport (ρ i : M → ℝ) ⊆ tsupport (b i.val) :=
    closure_mono (B.support_toPartitionOfUnity_subset i)
  refine ⟨s, fun i => c i.val, V, isOpen_iUnion (fun _ => isOpen_interior), hKV,
    ρ, fun i => ?_, fun i => (hsub i).trans (hb i.val)⟩
  exact (b i.val).hasCompactSupport.mono' ((subset_tsupport (ρ i)).trans (hsub i))

end PoincareConjecture.M32
