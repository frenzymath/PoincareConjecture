import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinGeometry
import PoincareConjecture.Proofs.M64.Mathlib.PiecewiseFirstJet










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture





theorem m64Intrinsic_exists_straight_join_graph
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A B c eta : ℝ} (heta : 0 < eta) (hc : 0 < c)
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A) :
    ∃ epsilon > 0, epsilon < eta ∧
      ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (X : Set ℝ) (h : ℝ → ℝ),
        (∀ z, L z = (inner ℝ (deriv alpha A) z,
          inner ℝ (quarterTurn (deriv alpha A)) z)) ∧
        IsOpen X ∧ ContinuousOn h X ∧ (L (alpha A)).1 ∈ X ∧
        HasDerivAt h 0 (L (alpha A)).1 ∧
        ∀ z : AnnulusCoordinates, (L z).1 ∈ X →
          (z ∈ alpha '' Icc (A - epsilon) A ∪ beta '' Icc B (B + epsilon) ↔
            (L z).2 = h (L z).1) := by
  classical
  obtain ⟨epsilon, hepsilon, heeta, hleft, hright, _, _, _⟩ :=
    m64Intrinsic_straight_join_local_geometry ha hb heta hc hend hreg htan
  have hAE : A - epsilon < A := sub_lt_self _ hepsilon
  have hBE : B < B + epsilon := lt_add_of_pos_right _ hepsilon
  obtain ⟨la, ua, G, L, f, hla, hua, hsource, hGval, hL, hm, hGs,
      _, _, hf, hgraph, himage, htarget, _⟩ :=
    exists_graph_coordinates_of_positive_projection ha hAE.le
      (fun t ht => (hleft t ht).1)
  obtain ⟨lb, ub, H, R, g, hlb, hub, hsource', hHval, hR, hm', hHs,
      _, _, hg, hgraph', himage', htarget', _⟩ :=
    exists_graph_coordinates_of_positive_projection hb hBE.le
      (fun t ht => (hright t ht).1)
  have hLR : L = R := by
    apply ContinuousLinearEquiv.ext
    funext z
    exact (hL z).trans (hR z).symm
  subst R
  have hI : Icc (A - epsilon) A ⊆ G.source := by
    rw [hsource]
    exact fun t ht => ⟨hla.trans_le ht.1, ht.2.trans_lt hua⟩
  have hJ : Icc B (B + epsilon) ⊆ H.source := by
    rw [hsource']
    exact fun t ht => ⟨hlb.trans_le ht.1, ht.2.trans_lt hub⟩
  have hG : StrictMonoOn G G.source := by
    intro x hx y hy hxy
    simpa only [hGval] using hm hx hy hxy
  have hH : StrictMonoOn H H.source := by
    intro x hx y hy hxy
    simpa only [hHval] using hm' hx hy hxy
  have hA := hI (right_mem_Icc.mpr hAE.le)
  have hB := hJ (left_mem_Icc.mpr hBE.le)
  have hbase : G A = H B := by rw [hGval, hHval, hend]
  have hLpoint : (L (alpha A)).1 = G A := congrArg Prod.fst (hgraph A hA)
  have hfg : f (G A) = g (G A) := by
    have heq := congrArg L hend
    rw [hgraph A hA, hgraph' B hB, ← hbase] at heq
    exact congrArg Prod.snd heq
  have hta := m64Intrinsic_graph_tangent ha L G hGs hf hgraph hA
  have htb := m64Intrinsic_graph_tangent hb L H hHs hg hgraph' hB
  have hGa : 0 < deriv G A := by
    have hfirst := congrArg Prod.fst hta
    simp only [Prod.smul_fst, smul_eq_mul, mul_one] at hfirst
    rw [← hfirst, hL]
    exact real_inner_self_pos.mpr hreg
  have hHb : 0 < deriv H B := by
    have hfirst := congrArg Prod.fst htb
    simp only [Prod.smul_fst, smul_eq_mul, mul_one] at hfirst
    rw [← hfirst, hL]
    exact (hright B (left_mem_Icc.mpr hBE.le)).1
  have hz : (L (deriv alpha A)).2 = 0 := by
    rw [hL]
    exact (real_inner_comm _ _).trans (inner_quarterTurn_self _)
  have hz' : (L (deriv beta B)).2 = 0 := by
    rw [htan, map_smul, Prod.smul_snd, smul_eq_mul, hz, mul_zero]
  have hfzero : deriv f (G A) = 0 := by
    have hs := congrArg Prod.snd hta
    simp only [Prod.smul_snd, smul_eq_mul, hz] at hs
    exact (mul_eq_zero.mp hs.symm).resolve_left hGa.ne'
  have hgzero : deriv g (G A) = 0 := by
    have hs := congrArg Prod.snd htb
    simp only [Prod.smul_snd, smul_eq_mul, hz'] at hs
    rw [hbase]
    exact (mul_eq_zero.mp hs.symm).resolve_left hHb.ne'
  have hdf : HasDerivAt f 0 (G A) := by
    rw [← hfzero]
    exact ((hf.contDiffAt (G.open_target.mem_nhds (G.map_source hA))).differentiableAt
      (by simp)).hasDerivAt
  have hdg : HasDerivAt g 0 (G A) := by
    rw [← hgzero]
    exact ((hg.contDiffAt (H.open_target.mem_nhds (hbase ▸ H.map_source hB))).differentiableAt
      (by simp)).hasDerivAt
  let X := (G.target ∩ H.target) ∩ Ioo (G (A - epsilon)) (H (B + epsilon))
  let h : ℝ → ℝ := (Iic (G A)).piecewise f g
  have hX : IsOpen X := (G.open_target.inter H.open_target).inter isOpen_Ioo
  have hx : G A ∈ X := ⟨⟨G.map_source hA, hbase ▸ H.map_source hB⟩,
    hG (hI (left_mem_Icc.mpr hAE.le)) hA hAE,
    hbase ▸ hH hB (hJ (right_mem_Icc.mpr hBE.le)) hBE⟩
  have hfc : ContinuousOn f X := hf.continuousOn.mono (fun _ ht => ht.1.1)
  have hgc : ContinuousOn g X := hg.continuousOn.mono (fun _ ht => ht.1.2)
  have hh : ContinuousOn h X := by
    apply ContinuousOn.if
    · intro t ht
      have ht0 : t = G A := by
        have ht' := ht.2
        change t ∈ frontier (Iic (G A)) at ht'
        simpa only [frontier_Iic, mem_singleton_iff] using ht'
      simpa only [ht0] using hfg
    · exact hfc.mono inter_subset_left
    · exact hgc.mono inter_subset_left
  have hd : HasDerivAt h 0 (G A) :=
    m64HasDerivAt_piecewise_of_same_jet hdf hdg hfg (Iic (G A))
  refine ⟨epsilon, hepsilon, heeta, L, X, h, hL, hX, hh,
    hLpoint ▸ hx, hLpoint ▸ hd, ?_⟩
  intro z hzX
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · have hle : G s ≤ G A := hG.monotoneOn (hI hs) hA hs.2
      rw [hgraph s (hI hs)]
      exact (piecewise_eq_of_mem (Iic (G A)) f g hle).symm
    · have hge : G A ≤ H t := hbase ▸ hH.monotoneOn hB (hJ ht) ht.1
      rw [hgraph' t (hJ ht)]
      change g (H t) = (Iic (G A)).piecewise f g (H t)
      by_cases hle : H t ≤ G A
      · have ht0 := le_antisymm hle hge
        rw [piecewise_eq_of_mem (Iic (G A)) f g hle, ht0, hfg]
      · exact (piecewise_eq_of_notMem (Iic (G A)) f g hle).symm
  · intro hz
    by_cases hle : (L z).1 ≤ G A
    · have hxI : (L z).1 ∈ Icc (G (A - epsilon)) (G A) := ⟨hzX.2.1.le, hle⟩
      obtain ⟨s, hs, hGsx⟩ := (himage ▸ hxI : (L z).1 ∈ G '' Icc (A - epsilon) A)
      refine Or.inl ⟨s, hs, L.injective ?_⟩
      rw [hgraph s (hI hs), hGsx]
      refine Prod.ext rfl ?_
      rw [hz]
      exact (piecewise_eq_of_mem (Iic (G A)) f g hle).symm
    · have hxI : (L z).1 ∈ Icc (H B) (H (B + epsilon)) :=
        ⟨hbase ▸ (le_of_not_ge hle), hzX.2.2.le⟩
      obtain ⟨t, ht, hHtx⟩ := (himage' ▸ hxI : (L z).1 ∈ H '' Icc B (B + epsilon))
      refine Or.inr ⟨t, ht, L.injective ?_⟩
      rw [hgraph' t (hJ ht), hHtx]
      refine Prod.ext rfl ?_
      rw [hz]
      exact (piecewise_eq_of_notMem (Iic (G A)) f g hle).symm

end PoincareConjecture
