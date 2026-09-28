import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.KernelJets

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_evaluationRow_coordinate_jet_bound
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V K : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVs : closure V ⊆ e.source) (hK : IsCompact K) (hKV : K ⊆ V)
    (k m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω),
      e '' V ⊆ Ω → ∀ {t : ℝ} (hat : a ≤ t), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m
        (fun z => evaluationRow (heatPowerContinuous D S k t (ha.trans_le hat)) (e z)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_heatPowerContinuous_coordinate_jet_bound
    D e he hei hV hVc hVs hK hKV k m ha
  refine ⟨C, hC, ?_⟩
  intro Ω S hVΩ t hat x hx
  exact norm_iteratedFDeriv_evaluationRow_coordinate_le D S e he k m t (ha.trans_le hat)
    (hVs (subset_closure (hKV hx))) (hVΩ (mem_image_of_mem e (hKV hx))) hC.le
    (fun f => hbound S hVΩ hat f x hx)

theorem exists_evaluationRow_coordinate_jets_bound
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V K : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVs : closure V ⊆ e.source) (hK : IsCompact K) (hKV : K ⊆ V)
    (k m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω),
      e '' V ⊆ Ω → ∀ {t : ℝ} (hat : a ≤ t), ∀ j ≤ m, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j
        (fun z => evaluationRow (heatPowerContinuous D S k t (ha.trans_le hat)) (e z)) x‖ ≤ C := by
  choose C hC hbound using fun j : ℕ =>
    exists_evaluationRow_coordinate_jet_bound D e he hei hV hVc hVs hK hKV k j ha
  refine ⟨1 + ∑ j ∈ Finset.range (m + 1), C j, ?_, ?_⟩
  · have hs : 0 ≤ ∑ j ∈ Finset.range (m + 1), C j :=
      Finset.sum_nonneg (fun j _ => (hC j).le)
    positivity
  · intro Ω S hVΩ t hat j hj x hx
    apply (hbound j S hVΩ hat x hx).trans
    exact (Finset.single_le_sum (fun i _ => (hC i).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans
        (le_add_of_nonneg_left zero_le_one)

end PoincareConjecture.LeviCivitaData.Dirichlet
