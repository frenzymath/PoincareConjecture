import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalSignedCollar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactNormalInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

set_option maxHeartbeats 800000 in

theorem m64Intrinsic_exists_annular_prefix_neighborhood
    {e : AnnulusCoordinates → AnnulusCoordinates} (he : ContDiff ℝ ∞ e)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    {a T : ℝ} (hT : 0 < T)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a)
      (deriv (fun t => e !₂[a, t]) 0))
    (hinside : ∀ t ∈ Ioc 0 T, 1 < ‖e !₂[a, t]‖ ∧ ‖e !₂[a, t]‖ < 2) :
    ∃ W : Set ℝ, IsOpen W ∧ a ∈ W ∧
      ∀ p ∈ W, ∀ t ∈ Ioc 0 T, 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ < 2 := by
  obtain ⟨epsilon, hepsilon, W0, hW0, haW0, hcollar⟩ :=
    m64Intrinsic_exists_signed_normal_collar he hbase hinward isOpen_univ (mem_univ _)
  let d := min epsilon T / 2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hde : d ≤ epsilon := by
    have h := min_le_left epsilon T
    dsimp only [d]
    linarith only [h, hepsilon]
  have hpair : Continuous (fun p : ℝ × ℝ => (!₂[p.1, p.2] : AnnulusCoordinates)) := by fun_prop
  let V : Set (ℝ × ℝ) := {p | 1 < ‖e !₂[p.1, p.2]‖ ∧ ‖e !₂[p.1, p.2]‖ < 2}
  have hn : Continuous (fun p : ℝ × ℝ => ‖e !₂[p.1, p.2]‖) :=
    (he.continuous.comp hpair).norm
  have hV : IsOpen V := (isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const)
  have hsub : ({a} : Set ℝ) ×ˢ Icc d T ⊆ V := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    have hpa : p = a := hp
    subst p
    exact hinside t ⟨hd.trans_le ht.1, ht.2⟩
  obtain ⟨W1, J, hW1, _, haW1, hTJ, hWJ⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hV hsub
  refine ⟨W0 ∩ W1, hW0.inter hW1, ⟨haW0, haW1 (mem_singleton a)⟩, ?_⟩
  intro p hp t ht
  by_cases hte : t ≤ epsilon
  · have hc := hcollar p hp.1 t ⟨by linarith only [hepsilon, ht.1], hte⟩
    exact ⟨hc.2.2.2 ht.1, hc.2.1⟩
  · have hpJ : (p, t) ∈ W1 ×ˢ J :=
      ⟨hp.2, hTJ ⟨hde.trans (le_of_not_ge hte), ht.2⟩⟩
    change (p, t) ∈ V
    exact hWJ hpJ

theorem m64Intrinsic_exists_stable_annular_prefix
    {e : AnnulusCoordinates → AnnulusCoordinates} (he : ContDiff ℝ ∞ e)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    {a T : ℝ} (hT : 0 < T)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a)
      (deriv (fun t => e !₂[a, t]) 0))
    (hinside : ∀ t ∈ Ioc 0 T, 1 < ‖e !₂[a, t]‖ ∧ ‖e !₂[a, t]‖ < 2)
    (hinj : InjOn (fun t => e !₂[a, t]) (Icc 0 T))
    (hreg : ∀ t ∈ Icc 0 T, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t])) :
    ∃ W : Set ℝ, IsOpen W ∧ a ∈ W ∧ ∀ p ∈ W,
      InjOn (fun t => e !₂[p, t]) (Icc 0 T) ∧
      ∀ t ∈ Ioc 0 T, 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ < 2 := by
  obtain ⟨W0, hW0, haW0, hconf⟩ :=
    m64Intrinsic_exists_annular_prefix_neighborhood he hbase hT hinward hinside
  obtain ⟨W1, hW1, haW1, hmap⟩ := m64Intrinsic_exists_embedded_prefix_tube he hinj hreg
  refine ⟨W0 ∩ W1, hW0.inter hW1, ⟨haW0, haW1⟩, ?_⟩
  intro p hp
  refine ⟨?_, fun t ht => hconf p hp.1 t ht⟩
  intro s hs t ht heq
  have hcoord := hmap (show (!₂[p, s] : AnnulusCoordinates) ∈ _ from ⟨hp.2, hs⟩)
    (show (!₂[p, t] : AnnulusCoordinates) ∈ _ from ⟨hp.2, ht⟩) heq
  exact congrArg (fun z : AnnulusCoordinates => z 1) hcoord

end PoincareConjecture
