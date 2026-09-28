import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskConnectedLink
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAnnulusRimCircles
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Perfect

set_option autoImplicit false
open Set Filter Geometry
open scoped Topology

namespace PoincareConjecture.M76

theorem isConnected_product_sdiff_point
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : IsPreconnected s) (ht : IsPreconnected t)
    (p : X × Y) {a : X} {b : Y}
    (ha : a ∈ s) (hap : a ≠ p.1) (hb : b ∈ t) (hbp : b ≠ p.2) :
    IsConnected ((s ×ˢ t) \ {p}) := by
  refine ⟨⟨(a, b), ⟨ha, hb⟩, fun h => hap (congrArg Prod.fst h)⟩,
    isPreconnected_of_forall (a, b) ?_⟩
  intro z hz
  by_cases hzp : z.1 = p.1
  · have hzq : z.2 ≠ p.2 := by
      intro h
      exact hz.2 (Prod.ext hzp h)
    refine ⟨(s ×ˢ {z.2}) ∪ ({a} ×ˢ t), ?_, Or.inr ⟨rfl, hb⟩,
      Or.inl ⟨hz.1.1, rfl⟩, ?_⟩
    · rintro w (hw | hw)
      · refine ⟨⟨hw.1, mem_singleton_iff.mp hw.2 ▸ hz.1.2⟩, ?_⟩
        intro h
        exact hzq ((mem_singleton_iff.mp hw.2).symm.trans (congrArg Prod.snd h))
      · refine ⟨⟨mem_singleton_iff.mp hw.1 ▸ ha, hw.2⟩, ?_⟩
        intro h
        exact hap ((mem_singleton_iff.mp hw.1).symm.trans (congrArg Prod.fst h))
    · exact (hs.prod isPreconnected_singleton).union (a, z.2) ⟨ha, rfl⟩
        ⟨rfl, hz.1.2⟩ (isPreconnected_singleton.prod ht)
  · refine ⟨({z.1} ×ˢ t) ∪ (s ×ˢ {b}), ?_, Or.inr ⟨ha, rfl⟩,
      Or.inl ⟨rfl, hz.1.2⟩, ?_⟩
    · rintro w (hw | hw)
      · refine ⟨⟨mem_singleton_iff.mp hw.1 ▸ hz.1.1, hw.2⟩, ?_⟩
        intro h
        exact hzp ((mem_singleton_iff.mp hw.1).symm.trans (congrArg Prod.fst h))
      · refine ⟨⟨hw.1, mem_singleton_iff.mp hw.2 ▸ hb⟩, ?_⟩
        intro h
        exact hbp ((mem_singleton_iff.mp hw.2).symm.trans (congrArg Prod.snd h))
    · exact (isPreconnected_singleton.prod ht).union (z.1, b) ⟨rfl, hb⟩
        ⟨hz.1.1, rfl⟩ (hs.prod isPreconnected_singleton)

theorem exists_connected_punctured_product_neighborhood
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] [LocallyConnectedSpace Y]
    [PerfectSpace X] [PerfectSpace Y]
    (p : X × Y) {W : Set (X × Y)} (hW : W ∈ 𝓝 p) :
    ∃ U : Set (X × Y), IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧ IsConnected (U \ {p}) := by
  obtain ⟨s, hs, t, ht, hst⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨s', hs's, hs'o, hps', hs'⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance p.1 s hs
  obtain ⟨t', ht't, ht'o, hpt', ht'⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance p.2 t ht
  have hsa : s' ∈ 𝓝[≠] p.1 := mem_nhdsWithin_of_mem_nhds (hs'o.mem_nhds hps')
  have htb : t' ∈ 𝓝[≠] p.2 := mem_nhdsWithin_of_mem_nhds (ht'o.mem_nhds hpt')
  obtain ⟨a, ha, hap⟩ := Filter.Eventually.exists (Filter.Eventually.and hsa
    (self_mem_nhdsWithin : {p.1}ᶜ ∈ 𝓝[≠] p.1))
  obtain ⟨b, hb, hbp⟩ := Filter.Eventually.exists (Filter.Eventually.and htb
    (self_mem_nhdsWithin : {p.2}ᶜ ∈ 𝓝[≠] p.2))
  exact ⟨s' ×ˢ t', hs'o.prod ht'o, ⟨hps', hpt'⟩,
    (prod_mono hs's ht't).trans hst,
    isConnected_product_sdiff_point hs'.isPreconnected ht'.isPreconnected p ha hap hb hbp⟩

end PoincareConjecture.M76

namespace Geometry.SimplicialComplex

open Classical in

theorem isConnected_link_of_homeomorph_product
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] [LocallyConnectedSpace Y]
    [PerfectSpace X] [PerfectSpace Y]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (H : (X × Y) ≃ₜ K.space)
    {p : E} (hp : p ∈ K.vertices) : IsConnected (K.link p).space := by
  classical
  have hpK := K.vertices_subset_space hp
  let z := H.symm ⟨p, hpK⟩
  have hHz : H z = ⟨p, hpK⟩ := H.apply_symm_apply _
  have hstar : (Subtype.val : K.space → E) ⁻¹' (K.closedFaceStar {p}).space ∈
      𝓝 (⟨p, hpK⟩ : K.space) := by
    apply K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hp
    simp
  have hW : H ⁻¹' ((Subtype.val : K.space → E) ⁻¹' (K.closedFaceStar {p}).space) ∈
      𝓝 z := H.continuous.continuousAt.preimage_mem_nhds (hHz.symm ▸ hstar)
  obtain ⟨U, hU, hzU, hUW, hpunct⟩ :=
    PoincareConjecture.M76.exists_connected_punctured_product_neighborhood z hW
  let B := (fun x => (H x : E)) '' (U \ {z})
  have hB : IsConnected B := hpunct.image (fun x => (H x : E))
    (continuous_subtype_val.comp H.continuous).continuousOn
  have hBstar : B ⊆ (K.closedFaceStar {p}).space \ {p} := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨hUW hy.1, ?_⟩
    intro h
    have hHy : H y = H z := Subtype.ext (by
      rw [hHz]
      exact h)
    exact hy.2 (H.injective hHy)
  have hnear : insert p B ∈ 𝓝[K.space] p := by
    rw [← map_nhds_subtype_val (⟨p, hpK⟩ : K.space)]
    have hUimage : H '' U ∈ 𝓝 (⟨p, hpK⟩ : K.space) :=
      (H.isOpenMap _ hU).mem_nhds ⟨z, hzU, hHz⟩
    apply mem_of_superset hUimage
    rintro x ⟨y, hy, rfl⟩
    by_cases hyz : y = z
    · left
      rw [hyz, hHz]
    · exact Or.inr ⟨y, ⟨hy, hyz⟩, rfl⟩
  exact K.isConnected_link_of_punctured_neighborhood hK hB hBstar hnear

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Metric
open Classical in

theorem connected_links_of_marked_annulus_product
    {ι κ E : Type*} [Fintype ι] [Fintype κ] [Unique κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hi : Fintype.card ι = 2)
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ K.space) :
    ∀ p ∈ K.vertices, IsConnected (K.link p).space := by
  classical
  have : LocallyConnectedSpace Circle :=
    (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).isCoinducing.locallyConnectedSpace
  have : Nontrivial Circle := ⟨1, -1, by
    intro h
    have := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at this⟩
  have : LocallyPathConnectedSpace (Icc (0 : ℝ) 1) := (convex_Icc _ _).locallyPathConnectedSpace
  have : ConnectedSpace (Icc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num))
  have : Nontrivial (Icc (0 : ℝ) 1) :=
    ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  obtain ⟨g⟩ := exists_unit_sphere_circle_homeomorph hi
  let H : (Circle × Icc (0 : ℝ) 1) ≃ₜ K.space :=
    (g.symm.prodCongr (Homeomorph.refl _)).trans (markedProductCylinder P)
  exact fun _ hp => K.isConnected_link_of_homeomorph_product hK H hp

theorem exists_closed_ball_two_product_homeomorph
    {κ : Type*} [Fintype κ] (hk : Fintype.card κ = 2)
    {r : ℝ} (hr : 0 < r) :
    Nonempty (closedBall (0 : κ → ℝ) r ≃ₜ (Icc (-r) r × Icc (-r) r)) := by
  classical
  let tau : κ ≃ Fin 2 := Fintype.equivFinOfCardEq hk
  let E : (κ → ℝ) ≃ᵢ (Fin 2 → ℝ) := IsometryEquiv.piCongrLeft' tau
  have hnorm (x : κ → ℝ) : ‖E x‖ = ‖x‖ := by
    simpa only [show E 0 = 0 from rfl, dist_zero_right] using E.isometry.dist_eq x 0
  let A : closedBall (0 : κ → ℝ) r ≃ₜ closedBall (0 : Fin 2 → ℝ) r :=
    E.toHomeomorph.subtype (fun x => by
      change x ∈ closedBall 0 r ↔ E x ∈ closedBall 0 r
      simp only [mem_closedBall_zero_iff, hnorm])
  let B := Homeomorph.piFinTwo (fun _ : Fin 2 => ℝ)
  have hB (x : Fin 2 → ℝ) : x ∈ closedBall 0 r ↔ B x ∈ Icc (-r) r ×ˢ Icc (-r) r := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr.le]
    change (∀ i, ‖x i‖ ≤ r) ↔ x 0 ∈ Icc (-r) r ∧ x 1 ∈ Icc (-r) r
    constructor
    · intro h
      exact ⟨abs_le.mp (h 0), abs_le.mp (h 1)⟩
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · exact abs_le.mpr h0
      · exact abs_le.mpr h1
  exact ⟨(A.trans (B.subtype hB)).trans (Homeomorph.Set.prod _ _)⟩

open Classical in

theorem connected_links_of_closed_ball_two
    {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hk : Fintype.card κ = 2) {r : ℝ} (hr : 0 < r)
    (P : closedBall (0 : κ → ℝ) r ≃ₜ K.space) :
    ∀ p ∈ K.vertices, IsConnected (K.link p).space := by
  classical
  have hrr : -r < r := by linarith
  have : LocallyPathConnectedSpace (Icc (-r) r) := (convex_Icc _ _).locallyPathConnectedSpace
  have : ConnectedSpace (Icc (-r) r) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc hrr.le)
  have : Nontrivial (Icc (-r) r) :=
    ⟨⟨-r, le_rfl, hrr.le⟩, ⟨r, hrr.le, le_rfl⟩,
      fun h => hrr.ne (congrArg Subtype.val h)⟩
  obtain ⟨g⟩ := exists_closed_ball_two_product_homeomorph hk hr
  exact fun _ hp => K.isConnected_link_of_homeomorph_product hK (g.symm.trans P) hp

end PoincareConjecture.M76
