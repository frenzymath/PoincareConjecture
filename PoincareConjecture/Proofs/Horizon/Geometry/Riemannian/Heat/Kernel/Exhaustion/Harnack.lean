import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Bounded
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum







set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData



theorem exists_dirichletExhaustionKernel_harnack_on_intrinsic_ball
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ Ω : ℕ → Set M,
      (∀ j, IsOpen (Ω j)) → Monotone Ω → (⋃ j, Ω j) = univ →
      ∀ K : ℕ → ℝ → M → M → ℝ,
        (∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j)) →
        (∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y)) →
        ∀ a b : ℝ, 0 < a → a < b → ∀ x z : M,
          (g.edist O x).toReal ≤ R → (g.edist O z).toReal ≤ R → ∀ y,
          dirichletExhaustionKernel K a x y ≤ dirichletExhaustionKernel K b z y *
            Real.exp (2 * (n : ℝ) * Real.log (b / a) + C * (b - a) +
              (g.edist x z).toReal ^ 2 / (2 * (b - a))) := by
  obtain ⟨C, hC, hH⟩ :=
    D.exists_heat_harnack_on_domains_containing_ball hn hc hk hRic O hR
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ hΩmono hcover K hK hmono a b ha hab x z hx hz y
  have hbdd : ∀ t, 0 < t → ∀ p q, BddAbove (range (fun j => K j t p q)) :=
    fun t ht p q => D.bddAbove_dirichletHeatKernel_exhaustion
      hn hc hk hRic hΩ hΩmono hcover hK hmono ht p q
  have hcball := g.isCompact_closedBall_of_metricComplete hc O (15 * R)
  obtain ⟨N, hN⟩ := hcball.elim_directed_cover Ω hΩ (by rw [hcover]; exact subset_univ _)
    (fun i j => ⟨max i j, hΩmono (le_max_left _ _), hΩmono (le_max_right _ _)⟩)
  have hcontains : {p | (g.edist O p).toReal ≤ 15 * R} ⊆ Ω N := by
    intro p hp
    apply hN
    change g.edist O p ≤ ENNReal.ofReal (15 * R)
    calc
      g.edist O p = ENNReal.ofReal (g.edist O p).toReal :=
        (ENNReal.ofReal_toReal (g.edist_ne_top O p)).symm
      _ ≤ ENNReal.ofReal (15 * R) := ENNReal.ofReal_le_ofReal hp
  obtain ⟨J, hJ⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ y)
  let E := Real.exp (2 * (n : ℝ) * Real.log (b / a) + C * (b - a) +
    (g.edist x z).toReal ^ 2 / (2 * (b - a)))
  have htail : ∀ᶠ j in atTop, K j a x y ≤ K j b z y * E := by
    refine eventually_atTop.2 ⟨max N J, ?_⟩
    intro j hj
    have hΩj : {p | (g.edist O p).toReal ≤ 15 * R} ⊆ Ω j :=
      hcontains.trans (hΩmono ((le_max_left N J).trans hj))
    have hyj : y ∈ Ω j := hΩmono ((le_max_right N J).trans hj) hJ
    have hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => K j p.1 p.2 y) (Ioi 0 ×ˢ Ω j) := by
      intro p hp
      have hs := (hK j).smooth.contMDiffAt (x := ((p.2, y), p.1))
        ((((hΩ j).prod (hΩ j)).prod isOpen_Ioi).mem_nhds ⟨⟨hp.2, hyj⟩, hp.1⟩)
      have hc := hs.comp p
        ((contMDiffAt_snd.prodMk contMDiffAt_const).prodMk contMDiffAt_fst)
      exact hc.contMDiffWithinAt
    exact hH (Ω j) (hΩ j) hΩj (fun p : ℝ × M => K j p.1 p.2 y) hu
      (fun s hs p hp => (hK j).positive s hs p hp y hyj)
      (fun s hs p hp => (hK j).heat_equation s hs p hp y)
      a b ha hab x z hx hz
  exact le_of_tendsto_of_tendsto (DirichletExhaustion.tendsto_supremum hmono hbdd ha x y)
    ((DirichletExhaustion.tendsto_supremum hmono hbdd (ha.trans hab) z y).mul_const E)
    htail

end PoincareConjecture.LeviCivitaData
