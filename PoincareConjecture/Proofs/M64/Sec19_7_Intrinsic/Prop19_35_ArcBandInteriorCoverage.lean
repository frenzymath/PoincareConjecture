import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcRelativeBoundaryCover
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCutContacts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_arc_band_covers_lower_interior
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B p : ℝ}
    (hinj : InjOn gamma (Icc A B))
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0) (hp : p ∈ Ioo A B)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma '' Icc A B ∪ K) (hfV : frontier V = frontier U)
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (D : ObliqueBandFaces F f a b ua wa ub wb ra rb)
    (hlower : D.lowerArc ⊆ gamma '' Icc A B) (hpoint : gamma p ∈ D.lowerArc)
    (hendpoint : ∀ e : Bool, gamma p ≠ (D.endpointEdge e).map 0)
    (hsub : D.carrier ⊆ closure U) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧
      W ∩ closure U ⊆ D.carrier := by
  let cuts (e : Bool) := (D.endpointEdge e).map '' Icc (0 : ℝ) 1
  have hcuts (e : Bool) : IsCompact (cuts e) :=
    isCompact_Icc.image_of_continuousOn (D.endpointEdge e).smooth.continuousOn
  have hpCuts (e : Bool) : gamma p ∉ cuts e := by
    rintro ⟨t, ht, htp⟩
    have ht0 := (m64Intrinsic_band_endpoint_mem_lower_iff D e ht).mp (htp.symm ▸ hpoint)
    exact hendpoint e (htp.symm.trans (congrArg (D.endpointEdge e).map ht0))
  let E := D.polygonalTop ∪ cuts false ∪ cuts true
  have hE : IsClosed E :=
    ((D.isCompact_polygonalTop.union (hcuts false)).union (hcuts true)).isClosed
  have hpE : gamma p ∉ E := by
    rintro ((htop | hleft) | hright)
    · exact disjoint_left.mp (m64Intrinsic_band_top_disjoint_lower D) htop hpoint
    · exact hpCuts false hleft
    · exact hpCuts true hright
  have hpD : gamma p ∈ D.carrier := D.isClosed_carrier.frontier_subset
    (D.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inl hpoint))))
  apply m64Intrinsic_exists_arc_relative_cover_of_local_frontier hg hinj hregular hp
    hK hpK hU hV hUV hfront (hfV.trans hfront) D.isClosed_carrier
    D.closure_interior_carrier hsub hpD (hE.isOpen_compl.mem_nhds hpE)
  intro z hz
  rw [D.frontier_carrier] at hz
  rcases hz.2 with ((hlow | htop) | hleft) | hright
  · exact Or.inl (hlower hlow)
  · exact (hz.1 (Or.inl (Or.inl htop))).elim
  · apply False.elim (hz.1 (Or.inl (Or.inr ?_)))
    change z ∈ (D.endpointEdge false).map '' Icc (0 : ℝ) 1
    simpa only [D.endpointEdge_image, Bool.false_eq_true, if_false] using hleft
  · apply False.elim (hz.1 (Or.inr ?_))
    change z ∈ (D.endpointEdge true).map '' Icc (0 : ℝ) 1
    simpa only [D.endpointEdge_image, if_true] using hright

end PoincareConjecture
