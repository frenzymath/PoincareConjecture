import PoincareConjecture.Proofs.M34.Standard.FlowLocality

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set Filter

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_forwardFlowUnion {ι : Type*} (T : ι → ℝ)
    (F : (i : ι) → RicciFlow n M (Ico 0 (T i))) (i0 : ι)
    (hcompat : ∀ i j : ι, EqOn (F i).metric (F j).metric
      (Ico 0 (T i) ∩ Ico 0 (T j)))
    {S : ℝ} (hS : 0 < S) (hcover : ∀ t ∈ Ico 0 S, ∃ i : ι, t ∈ Ico 0 (T i)) :
    ∃ G : RicciFlow n M (Ico 0 S), ∀ i : ι,
      EqOn G.metric (F i).metric (Ico 0 S ∩ Ico 0 (T i)) := by
  classical
  let index : ℝ → ι := fun t => if h : ∃ i : ι, t ∈ Ico 0 (T i) then h.choose else i0
  have hindex {t : ℝ} (ht : t ∈ Ico 0 S) : t ∈ Ico 0 (T (index t)) := by
    dsimp [index]
    rw [dif_pos (hcover t ht)]
    exact (hcover t ht).choose_spec
  let g : ℝ → RiemannianMetric n M := fun t => (F (index t)).metric t
  let D : (t : ℝ) → LeviCivitaData (g t) := fun t => (F (index t)).connection t
  have hmatch (i : ι) : EqOn g (F i).metric (Ico 0 S ∩ Ico 0 (T i)) := by
    intro t ht
    exact hcompat (index t) i ⟨hindex ht.1, ht.2⟩
  have hne : (Ico 0 S).Nontrivial := by
    refine ⟨0, ⟨le_rfl, hS⟩, S / 2, ⟨by linarith, by linarith⟩, ?_⟩
    linarith
  have hloc : ∀ t ∈ Ico 0 S, ∃ K : Set ℝ, ∃ G : RicciFlow n M K,
      t ∈ K ∧ K ∈ 𝓝[Ico 0 S] t ∧ g =ᶠ[𝓝[Ico 0 S] t] G.metric := by
    intro t ht
    obtain ⟨i, hi⟩ := hcover t ht
    have hK : Ico 0 (T i) ∈ 𝓝[Ico 0 S] t := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi.2)] with s hs hs'
      exact ⟨hs.1, hs'⟩
    refine ⟨Ico 0 (T i), F i, hi, hK, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hK] with s hs hsK
    exact hmatch i ⟨hs, hsK⟩
  exact ⟨flowOfLocalRepresentatives (Ico 0 S) g D ordConnected_Ico hne hloc, hmatch⟩

end PoincareConjecture.M34
