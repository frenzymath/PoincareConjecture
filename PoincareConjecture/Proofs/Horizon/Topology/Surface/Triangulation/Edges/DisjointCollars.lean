import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.CollarCoordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

private theorem exists_disjoint_open_neighborhoods
    {X I : Type*} [TopologicalSpace X] [T2Space X] [Finite I]
    (K O : I → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hO : ∀ i, IsOpen (O i)) (hKO : ∀ i, K i ⊆ O i) :
    ∃ U : I → Set X, (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧ U i ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  have hfilters : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) := fun i j hij =>
    (SeparatedNhds.of_isCompact_isCompact (hK i) (hK j) (hdisj hij)).disjoint_nhdsSet
  obtain ⟨V, hV, hVdisj⟩ := hfilters.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (K i))
  refine ⟨fun i => V i ∩ O i, ?_, ?_⟩
  · intro i
    exact ⟨(hV i).1.inter (hO i), subset_inter (hV i).2 (hKO i), inter_subset_right⟩
  · intro i j hij
    exact (hVdisj hij).mono inter_subset_left inter_subset_left

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

def chartArcCarrier (p : M) (f : ℝ → EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : Set M :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' (f '' Icc a b)

theorem exists_surface_normal_collar_coordinates_within (p : M)
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hinj : InjOn f (Icc a b))
    (hregular : ∀ t ∈ Icc a b, deriv f t ≠ 0)
    (htarget : f '' Icc a b ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target)
    {O : Set M} (hO : IsOpen O) (hcore : chartArcCarrier p f a b ⊆ O) :
    ∃ ε > 0, ∃ C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M,
      collarParameterEquiv ⁻¹' (Icc a b ×ˢ Ioo (-ε) ε) ⊆ C.source ∧
      (∀ z, C z = (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
        (Poincare.Topology.Plane.Curves.normalStrip f (collarParameterEquiv z))) ∧
      (∀ t ∈ Icc a b,
        C (collarParameterEquiv.symm (t, 0)) =
          (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm (f t)) ∧
      C.target ⊆ O ∧ C.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target := by
  obtain ⟨δ, hδ, C, hstrip, hformula, haxis, hchart, hC, hCinv⟩ :=
    exists_surface_normal_collar_coordinates p hf hinj hregular htarget
  let D := C.trans (OpenPartialHomeomorph.ofSet O hO)
  let W := collarParameterEquiv.symm ⁻¹' D.source
  have hWopen : IsOpen W := D.open_source.preimage collarParameterEquiv.symm.continuous
  have hWaxis : Icc a b ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    change collarParameterEquiv.symm (t, 0) ∈ C.source ∧
      C (collarParameterEquiv.symm (t, 0)) ∈ O
    constructor
    · apply hstrip
      simpa only [mem_preimage, collarParameterEquiv.apply_symm_apply, mem_prod, mem_Ioo] using
        And.intro ht (And.intro (neg_neg_of_pos hδ) hδ)
    · rw [haxis t ht]
      exact hcore ⟨f t, ⟨t, ht, rfl⟩, rfl⟩
  have hWnhds := hWopen.mem_nhdsSet.mpr hWaxis
  rw [isCompact_Icc.nhdsSet_prod_eq isCompact_singleton, nhdsSet_singleton] at hWnhds
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hWnhds
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  have hnewstrip : Icc a b ×ˢ Ioo (-ε) ε ⊆ W := by
    apply (prod_mono (subset_of_mem_nhdsSet hU) ?_).trans hUV
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hεV
  refine ⟨ε, hε, D, ?_, hformula, haxis, fun _ hz => hz.1,
    fun _ hz => hchart hz.2, hC.mono (fun _ hz => hz.1),
    hCinv.mono (fun _ hz => hz.2)⟩
  intro z hz
  have h := hnewstrip hz
  change collarParameterEquiv.symm (collarParameterEquiv z) ∈ D.source at h
  simpa only [collarParameterEquiv.symm_apply_apply] using h

theorem exists_disjoint_surface_normal_collars [T2Space M]
    {I : Type v} [Finite I] (p : I → M) (f : I → ℝ → EuclideanSpace ℝ (Fin 2))
    (a b : I → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hinj : ∀ i, InjOn (f i) (Icc (a i) (b i)))
    (hregular : ∀ i, ∀ t ∈ Icc (a i) (b i), deriv (f i) t ≠ 0)
    (htarget : ∀ i, f i '' Icc (a i) (b i) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).target)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (chartArcCarrier (p i) (f i) (a i) (b i))
      (chartArcCarrier (p j) (f j) (a j) (b j))))
    (O : I → Set M) (hO : ∀ i, IsOpen (O i))
    (hcore : ∀ i, chartArcCarrier (p i) (f i) (a i) (b i) ⊆ O i) :
    ∃ (ε : I → ℝ) (C : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M),
      (∀ i, 0 < ε i) ∧
      (∀ i, collarParameterEquiv ⁻¹' (Icc (a i) (b i) ×ˢ Ioo (-ε i) (ε i)) ⊆
        (C i).source) ∧
      (∀ i z, C i z = (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm
        (Poincare.Topology.Plane.Curves.normalStrip (f i) (collarParameterEquiv z))) ∧
      (∀ i, ∀ t ∈ Icc (a i) (b i),
        C i (collarParameterEquiv.symm (t, 0)) =
          (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm (f i t)) ∧
      (∀ i, (C i).target ⊆ O i) ∧
      (∀ i, (C i).target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C i) (C i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C i).symm (C i).target) ∧
      Pairwise (fun i j => Disjoint (C i).target (C j).target) := by
  let K : I → Set M := fun i => chartArcCarrier (p i) (f i) (a i) (b i)
  have hK (i : I) : IsCompact (K i) :=
    (isCompact_Icc.image (hf i).continuous).image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).continuousOn_symm.mono (htarget i))
  obtain ⟨U, hU, hUdisj⟩ := exists_disjoint_open_neighborhoods K O hK hdisjoint hO hcore
  choose ε hε C hstrip hformula haxis htargetU hchart hC hCinv using fun i =>
    exists_surface_normal_collar_coordinates_within (p i) (hf i) (hinj i) (hregular i)
      (htarget i) (hU i).1 (hU i).2.1
  refine ⟨ε, C, hε, hstrip, hformula, haxis,
    fun i => (htargetU i).trans (hU i).2.2, hchart, hC, hCinv, ?_⟩
  intro i j hij
  exact (hUdisj hij).mono (htargetU i) (htargetU j)

end PoincareConjecture.Topology.Surface
