import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.BoundaryInterior
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_thin_collar_interior_pair_charts
    {E X ι : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {K rim : Set E} (hK : IsCompact K)
    {S R : Set X} (hS : IsClosed S)
    {g : E → X} (hg : ContinuousOn g K)
    (hproper : ∀ x ∈ K, g x ∈ frontier R ↔ x ∈ rim)
    (hboundary : ∀ x ∈ K ∩ rim, g x ∈ S →
      ∃ C : OriginalSurfacePairChart e S (g '' K) (g x) true,
        ∀ z ∈ C.coordinates.source,
          C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0)
    {height : E → ℝ} (hheight : ContinuousOn height K)
    (hnonneg : ∀ x ∈ K, 0 ≤ height x)
    (hzero : ∀ x ∈ K, height x = 0 ↔ x ∈ rim)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ c < δ ∧
      ∀ x ∈ K, height x ≤ c → x ∉ rim → g x ∈ S →
        Nonempty (OriginalSurfacePairChart e S (g '' K) (g x) false) := by
  classical
  let Points := {x : E // x ∈ K ∩ rim ∧ g x ∈ S}
  choose C hfront using fun x : Points => hboundary x x.property.1 x.property.2
  let U (x : Points) : Set X :=
    (C x).chart.source ∩ (C x).chart ⁻¹' (C x).coordinates.source
  have hU (x : Points) : IsOpen (U x) :=
    (C x).chart.isOpen_inter_preimage (C x).coordinates.open_source
  let W : Set X := (⋃ x : Points, U x) ∪ Sᶜ
  have hW : IsOpen W := (isOpen_iUnion hU).union hS.isOpen_compl
  have hrimW (x : E) (hxK : x ∈ K) (hxrim : x ∈ rim) : g x ∈ W := by
    by_cases hxS : g x ∈ S
    · let p : Points := ⟨x, ⟨hxK, hxrim⟩, hxS⟩
      exact Or.inl (mem_iUnion.mpr ⟨p, (C p).center_source, (C p).center_coordinates⟩)
    · exact Or.inr hxS
  have hbad : IsCompact (K ∩ g ⁻¹' Wᶜ) :=
    hK.of_isClosed_subset (hg.preimage_isClosed_of_isClosed hK.isClosed hW.isClosed_compl)
      inter_subset_left
  obtain ⟨b, hb, hbound⟩ := hbad.exists_forall_le'
    (hheight.mono inter_subset_left) (by
      intro x hx
      exact lt_of_le_of_ne (hnonneg x hx.1)
        (fun h => hx.2 (hrimW x hx.1 ((hzero x hx.1).mp h.symm))))
  let c := min b δ / 2
  have hc : 0 < c := half_pos (lt_min hb hδ)
  have hcb : c < b := (half_lt_self (lt_min hb hδ)).trans_le (min_le_left b δ)
  have hcδ : c < δ := (half_lt_self (lt_min hb hδ)).trans_le (min_le_right b δ)
  refine ⟨c, hc, hcδ, ?_⟩
  intro x hxK hxc hxrim hxS
  have hxW : g x ∈ W := by
    by_contra hn
    exact (hcb.trans_le (hbound x ⟨hxK, hn⟩)).not_ge hxc
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hxW.resolve_right (fun hn => hn hxS))
  have hxT : g x ∈ g '' K := mem_image_of_mem g hxK
  have hnonnegative : 0 ≤ ((C p).coordinates ((C p).chart (g x))).1.2 := by
    have hh := ((C p).first_surface _ hp.2).mp
      (by simpa only [(C p).chart.left_inv hp.1] using hxS)
    exact hh.2 rfl
  have hpositive : 0 < ((C p).coordinates ((C p).chart (g x))).1.2 := by
    apply lt_of_le_of_ne hnonnegative
    intro h
    apply hxrim ((hproper x hxK).mp ?_)
    have hh := (hfront p _ hp.2).mpr h.symm
    simpa only [(C p).chart.left_inv hp.1] using hh
  exact ⟨(C p).interior_at hp.1 hp.2 hxS hxT hpositive⟩

end PoincareConjecture.M76
