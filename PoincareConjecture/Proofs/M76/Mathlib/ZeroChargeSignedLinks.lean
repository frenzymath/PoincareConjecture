import PoincareConjecture.Proofs.M76.Mathlib.PolygonStrictSigns
import PoincareConjecture.Proofs.M76.Mathlib.SurfaceLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicIsolatedStarSign
import PoincareConjecture.Proofs.M76.Mathlib.CentralLinkSigns

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem zero_charge_link_sign_data
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hzero : (0 : E) ∈ K.vertices)
    (hconn : (K.link 0).vertexAbstractComplex.edgeGraph.Connected)
    (L : E →ₗ[ℝ] ℝ)
    (hpres : HasAlexanderCurvePresentation (K.space ∩ {x | L x = 0}) 0)
    (hsigns : (0 : E) ∈ closure ((K.space ∩ {x | L x = 0}) \ {0}) →
      (0 : E) ∈ closure (K.space ∩ {x | L x < 0}) ∧
        (0 : E) ∈ closure (K.space ∩ {x | 0 < L x})) :
    IsPreconnected ((K.link 0).space ∩ {x | L x < 0}) ∧
      IsPreconnected ((K.link 0).space ∩ {x | 0 < L x}) ∧
      ∀ x ∈ (K.link 0).space, L x = 0 →
        x ∈ closure ((K.link 0).space ∩ {y | L y < 0}) ∧
          x ∈ closure ((K.link 0).space ∩ {y | 0 < L y}) := by
  by_cases hacc : (0 : E) ∈ closure ((K.space ∩ {x | L x = 0}) \ {0})
  · obtain ⟨hneg, hpos⟩ := hsigns hacc
    obtain ⟨n, P, hPi, hPe, hPlink⟩ := K.exists_surface_link_polygon hK hpure hcofaces 0 hconn
    have hcard := K.ncard_link_zero_eq_two_of_zero_charge_nonisolated hK hzero L hpres hacc
    obtain ⟨hlinkpos, hlinkneg⟩ :=
      K.exists_both_link_signs_of_surface_accumulation hK hzero L hpos hneg
    rw [← hPlink] at hcard hlinkpos hlinkneg
    obtain ⟨hn, hp, hz⟩ := P.strict_sign_data hPe hPi L
      L.continuous_of_finiteDimensional.continuousOn hcard hlinkneg hlinkpos
    rw [hPlink] at hn hp hz
    exact ⟨hn.isPreconnected, hp.isPreconnected, hz⟩
  · have hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ∩ {y | L y = 0} → x = 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hacc] with x hx hxlevel
      by_contra hxzero
      exact hx (subset_closure ⟨hxlevel, hxzero⟩)
    have hlinkconn := ((K.link 0).isPathConnected_space_of_connected_edgeGraph hconn).isConnected
    obtain ⟨η, hη, ⟨hpos, _⟩ | ⟨hneg, _⟩⟩ :=
      K.exists_signed_link_gap_of_isolated_section hK L hconn hlocal
    · have hn : (K.link 0).space ∩ {x | L x < 0} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (hη.trans_le (hpos x hx.1)).not_ge (show L x < 0 from hx.2).le
      have hp : (K.link 0).space ∩ {x | 0 < L x} = (K.link 0).space := by
        apply Subset.antisymm inter_subset_left
        exact fun x hx => ⟨hx, hη.trans_le (hpos x hx)⟩
      refine ⟨hn.symm ▸ isPreconnected_empty, hp.symm ▸ hlinkconn.isPreconnected, ?_⟩
      intro x hx hxL
      exact ((hη.trans_le (hpos x hx)).ne' hxL).elim
    · have hn : (K.link 0).space ∩ {x | L x < 0} = (K.link 0).space := by
        apply Subset.antisymm inter_subset_left
        exact fun x hx => ⟨hx, (hneg x hx).trans_lt (neg_neg_of_pos hη)⟩
      have hp : (K.link 0).space ∩ {x | 0 < L x} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (show 0 < L x from hx.2).not_ge ((hneg x hx.1).trans (neg_nonpos.mpr hη.le))
      refine ⟨hn.symm ▸ hlinkconn.isPreconnected, hp.symm ▸ isPreconnected_empty, ?_⟩
      intro x hx hxL
      exact (((hneg x hx).trans_lt (neg_neg_of_pos hη)).ne hxL).elim

end Geometry.SimplicialComplex
