import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Order
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Singleton
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cover
import Mathlib.Order.Zorn

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

namespace BalancedNeckChain

def IsSelectedFrom (C : BalancedNeckChain g ε) (H : NeckOnlyCover g) : Prop :=
  C.source_necks ⊆ H.necks ∧ ∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X

def HasQuarterCapture (C : BalancedNeckChain g ε) : Prop :=
  ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
    (C.neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆ (C.neck (i + 1)).coordinate_map ''
      (univ ×ˢ Icc (-(3 / 4 : ℝ) * (C.neck (i + 1)).epsilon⁻¹)
        ((3 / 4 : ℝ) * (C.neck (i + 1)).epsilon⁻¹)) ∨
    (C.neck (i + 1)).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ (C.neck i).coordinate_map ''
      (univ ×ˢ Icc (-(3 / 4 : ℝ) * (C.neck i).epsilon⁻¹)
        ((3 / 4 : ℝ) * (C.neck i).epsilon⁻¹))

theorem exists_directed_limit_selected {ι : Type*} [Nonempty ι]
    (H : NeckOnlyCover g) (C : ι → BalancedNeckChain g ε)
    (hdir : Directed IsExtension C) (hselected : ∀ n, (C n).IsSelectedFrom H)
    (hcapture : ∀ n, (C n).HasQuarterCapture) :
    ∃ L : BalancedNeckChain g ε,
      L.IsSelectedFrom H ∧ L.HasQuarterCapture ∧ ∀ n, (C n).IsExtension L := by
  obtain ⟨L, hactive, hsource, hext, _⟩ := exists_directed_limit C hdir
  have hstage (i : ℤ) (hi : i ∈ L.shape.active) : ∃ n, i ∈ (C n).shape.active := by
    rw [hactive] at hi
    exact mem_iUnion.mp hi
  refine ⟨L, ⟨?_, ?_⟩, ?_, hext⟩
  · intro N hN
    rw [hsource] at hN
    obtain ⟨n, hn⟩ := mem_iUnion.mp hN
    exact (hselected n).1 hn
  · intro i hi
    obtain ⟨n, hn⟩ := hstage i hi
    rw [← (hext n).2.2 i hn]
    exact (hselected n).2 i hn
  · intro i hi hj
    obtain ⟨n, hn⟩ := hstage i hi
    obtain ⟨m, hm⟩ := hstage (i + 1) hj
    obtain ⟨p, hnp, hmp⟩ := hdir n m
    have hpi := hnp.1 hn
    have hpj := hmp.1 hm
    rw [← (hext p).2.2 i hpi, ← (hext p).2.2 (i + 1) hpj]
    exact hcapture p i hpi hpj

end BalancedNeckChain

namespace NeckOnlyCover

open BalancedNeckChain

theorem exists_maximal_selected_chain (H : NeckOnlyCover g) :
    ∃ C : BalancedNeckChain g H.epsilon,
      C.IsSelectedFrom H ∧ C.HasQuarterCapture ∧
      ∀ D : BalancedNeckChain g H.epsilon,
        D.IsSelectedFrom H → D.HasQuarterCapture → C.IsExtension D → D.IsExtension C := by
  classical
  obtain ⟨x, hx⟩ := H.connected_X.nonempty
  obtain ⟨N, hN, hNx⟩ := H.pointwise_center_cover x hx
  have initial (ε : ℝ) (he : N.epsilon = ε) :
      ∃ C : BalancedNeckChain g ε, C.IsSelectedFrom H ∧ C.HasQuarterCapture := by
    subst ε
    refine ⟨BalancedNeckChain.singleton N, ⟨?_, ?_⟩, ?_⟩
    · intro S hS
      change S ∈ ({N} : Set (EpsilonNeck g)) at hS
      simpa only [mem_singleton_iff.mp hS] using hN
    · intro i _
      change N.center ∈ H.X
      rwa [hNx]
    · intro i hi hj
      change i ∈ Icc (0 : ℤ) 0 at hi
      change i + 1 ∈ Icc (0 : ℤ) 0 at hj
      obtain ⟨hil, hiu⟩ := hi
      obtain ⟨hjl, hju⟩ := hj
      omega
  let A := {C : BalancedNeckChain g H.epsilon // C.IsSelectedFrom H ∧ C.HasQuarterCapture}
  have : Nonempty A := by
    obtain ⟨C, hC⟩ := initial H.epsilon (H.neck_epsilon N hN)
    exact ⟨⟨C, hC⟩⟩
  let r : A → A → Prop := fun C D => C.1.IsExtension D.1
  have hbound (s : Set A) (hs : IsChain r s) (hne : s.Nonempty) :
      ∃ L : A, ∀ C ∈ s, r C L := by
    let : Nonempty s := hne.to_subtype
    have hdir : Directed IsExtension (fun C : s => C.1.1) := by
      intro C D
      by_cases he : C.1 = D.1
      · refine ⟨D, ?_, IsExtension.refl _⟩
        simpa only [he] using IsExtension.refl D.1.1
      · rcases hs C.2 D.2 he with hCD | hDC
        · exact ⟨D, hCD, IsExtension.refl _⟩
        · exact ⟨C, IsExtension.refl _, hDC⟩
    obtain ⟨L, hLs, hLc, hL⟩ := exists_directed_limit_selected H
      (fun C : s => C.1.1) hdir (fun C => C.1.2.1) (fun C => C.1.2.2)
    exact ⟨⟨L, hLs, hLc⟩, fun C hC => hL ⟨C, hC⟩⟩
  obtain ⟨C, hC⟩ := exists_maximal_of_nonempty_chains_bounded hbound
    (fun hCD hDE => IsExtension.trans hCD hDE)
  exact ⟨C.1, C.2.1, C.2.2, fun D hDs hDc hCD => hC ⟨D, hDs, hDc⟩ hCD⟩

end NeckOnlyCover

end PoincareConjecture
