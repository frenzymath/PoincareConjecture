import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

universe u v w

namespace PoincareConjecture.Proofs.M03

theorem contDiffOn_family_bundle_coordinates
    {n d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : M → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    [ContMDiffVectorBundle ∞ F E (𝓡 n)]
    (q : F ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    {J : Set ℝ} (v : (t : ℝ) → (x : M) → E x)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' F p.2 (v p.1 p.2)) (J ×ˢ Set.univ))
    (a : M)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin n)) a).source ⊆
      (trivializationAt F E a).baseSet) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        q ((trivializationAt F E a) (TotalSpace.mk' F
          ((chartAt (EuclideanSpace ℝ (Fin n)) a).symm p.2)
          (v p.1 ((chartAt (EuclideanSpace ℝ (Fin n)) a).symm p.2)))).2)
      (J ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) a).target) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) a
  let e := trivializationAt F E a
  have hmaps :
      MapsTo (fun p : ℝ × M => TotalSpace.mk' F p.2 (v p.1 p.2))
        (J ×ˢ c.source) e.source := by
    intro p hp
    rw [e.mem_source]
    exact hbase (show p.2 ∈ c.source from hp.2)
  have hcoords := (e.contMDiffOn_iff hmaps).mp
    (hv.mono (Set.prod_mono subset_rfl (subset_univ _)))
  let G : ℝ × EuclideanSpace ℝ (Fin n) → ℝ × M :=
    fun p => (p.1, c.symm p.2)
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ G
      (J ×ˢ c.target) := by
    apply contMDiffOn_fst.prodMk
    exact (contMDiffOn_chart_symm (H := EuclideanSpace ℝ (Fin n))
      (x := a)).comp contMDiffOn_snd (fun p hp => hp.2)
  have hGmaps : MapsTo G (J ×ˢ c.target) (J ×ˢ c.source) := by
    intro p hp
    exact ⟨hp.1, c.map_target hp.2⟩
  have hcomp := hcoords.2.comp hG hGmaps
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
  have hcomp' : ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        (e (TotalSpace.mk' F (c.symm p.2)
          (v p.1 (c.symm p.2)))).2)
      (J ×ˢ c.target) := hcomp.contDiffOn
  exact q.contDiff.comp_contDiffOn hcomp'

end PoincareConjecture.Proofs.M03
