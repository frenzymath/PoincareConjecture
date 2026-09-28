


import PoincareConjecture.Proofs.Horizon.Topology.Paths.Trimming
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.DisjointCollars








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem exists_trimmed_disjoint_chart_arc_collars
    {I : Type v} [Finite I] (p : I → M) (f : I → ℝ → EuclideanSpace ℝ (Fin 2))
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hinj : ∀ i, InjOn (f i) (Icc (0 : ℝ) 1))
    (hregular : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f i) t ≠ 0)
    (htarget : ∀ i, f i '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).target)
    (hmeet : ∀ i j, i ≠ j →
      chartArcCarrier (p i) (f i) 0 1 ∩ chartArcCarrier (p j) (f j) 0 1 ⊆
        {(chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm (f i 0),
          (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm (f i 1)})
    (U V : I → Set M)
    (hU : ∀ i, U i ∈ 𝓝 ((chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm (f i 0)))
    (hV : ∀ i, V i ∈ 𝓝 ((chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm (f i 1))) :
    ∃ (a b ε : I → ℝ) (C : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M),
      (∀ i, 0 < a i ∧ a i < b i ∧ b i < 1 ∧ 0 < ε i) ∧
      (∀ i, chartArcCarrier (p i) (f i) 0 (a i) ⊆ U i ∧
        chartArcCarrier (p i) (f i) (b i) 1 ⊆ V i) ∧
      (∀ i, collarParameterEquiv ⁻¹' (Icc (a i) (b i) ×ˢ Ioo (-ε i) (ε i)) ⊆
        (C i).source) ∧
      (∀ i z, C i z = (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm
        (Poincare.Topology.Plane.Curves.normalStrip (f i) (collarParameterEquiv z))) ∧
      (∀ i, (C i).target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C i) (C i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C i).symm (C i).target) ∧
      Pairwise (fun i j => Disjoint (C i).target (C j).target) ∧
      (∀ i j, i ≠ j → Disjoint (C i).target (chartArcCarrier (p j) (f j) 0 1)) := by
  let γ (i : I) : ℝ → M := (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm ∘ f i
  have hcarrier (i : I) (a b : ℝ) : chartArcCarrier (p i) (f i) a b = γ i '' Icc a b := by
    exact image_image _ _ _
  have hγ (i : I) : ContinuousOn (γ i) (Icc (0 : ℝ) 1) :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).continuousOn_symm.comp
      (hf i).continuous.continuousOn (fun t ht => htarget i ⟨t, ht, rfl⟩)
  have hγinj (i : I) : InjOn (γ i) (Icc (0 : ℝ) 1) :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).symm.injOn.comp (hinj i)
      (fun t ht => htarget i ⟨t, ht, rfl⟩)
  obtain ⟨a, b, hab, hends, _, hdisj, _⟩ :=
    Poincare.Topology.exists_disjoint_compact_arc_cores γ hγ hγinj
      (fun i j hij => by simpa only [hcarrier, γ, Function.comp_apply] using hmeet i j hij)
      U V hU hV
  let K (i : I) := chartArcCarrier (p i) (f i) 0 1
  let O (i : I) := (⋃ j : {j : I // i ≠ j}, K j)ᶜ
  have hKcompact (i : I) : IsCompact (K i) := by
    change IsCompact (chartArcCarrier (p i) (f i) 0 1)
    rw [hcarrier]
    exact isCompact_Icc.image_of_continuousOn (hγ i)
  have hO (i : I) : IsOpen (O i) :=
    (isClosed_iUnion_of_finite (fun j : {j : I // i ≠ j} => (hKcompact j).isClosed)).isOpen_compl
  have hcore (i : I) : chartArcCarrier (p i) (f i) (a i) (b i) ⊆ O i := by
    rw [hcarrier]
    intro z hz hzo
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzo
    exact disjoint_left.mp (hdisj i j j.property) hz ((hcarrier j 0 1) ▸ hj)
  have hsub (i : I) : Icc (a i) (b i) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hab i).1.le (hab i).2.2.le
  have hcores : Pairwise (fun i j => Disjoint
      (chartArcCarrier (p i) (f i) (a i) (b i))
      (chartArcCarrier (p j) (f j) (a j) (b j))) := by
    intro i j hij
    rw [hcarrier, hcarrier]
    exact (hdisj i j hij).mono_right (image_mono (hsub j))
  obtain ⟨ε, C, hε, hstrip, hformula, _, hCO, hchart, hC, hCinv, hCC⟩ :=
    exists_disjoint_surface_normal_collars p f a b hf
      (fun i => (hinj i).mono (hsub i)) (fun i t ht => hregular i t (hsub i ht))
      (fun i => (image_mono (hsub i)).trans (htarget i)) hcores O hO hcore
  refine ⟨a, b, ε, C, fun i => ⟨(hab i).1, (hab i).2.1, (hab i).2.2, hε i⟩,
    ?_, hstrip, hformula, hchart, hC, hCinv, hCC, ?_⟩
  · intro i
    simpa only [hcarrier] using hends i
  · intro i j hij
    exact disjoint_left.mpr fun z hz hj => hCO i hz (mem_iUnion.mpr ⟨⟨j, hij⟩, hj⟩)

end PoincareConjecture.Topology.Surface
