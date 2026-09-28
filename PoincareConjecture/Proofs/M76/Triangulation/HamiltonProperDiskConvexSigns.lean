import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskPairedFacetSigns
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.AffineOnFaces
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem full_face_label_constant {β : Type*}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (label : {s : Finset E // s ∈ K.faces ∧ s.card = Module.finrank ℝ E + 1} → β)
    (hadj : ∀ s t, ∀ r : Finset E, r.card = Module.finrank ℝ E →
      r ⊆ s.val → r ⊆ t.val → label s = label t) :
    ∀ s t, label s = label t := by
  classical
  let Small : Set (Finset E) := {s | s ∈ K.faces ∧ s.card < Module.finrank ℝ E}
  have hSmall : Small.Finite := hK.subset (fun _ hs => hs.1)
  let : Finite Small := hSmall.to_subtype
  let A : Small → AffineSubspace ℝ E := fun s => affineSpan ℝ (s.val : Set E)
  have hcodim : ∀ s, Module.finrank ℝ (A s).direction + 1 < Module.finrank ℝ E := by
    intro s
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces s.property.1)
    have hc : s.val.card = (s.val.card - 1) + 1 := by omega
    change Module.finrank ℝ (affineSpan ℝ (s.val : Set E)).direction + 1 < _
    rw [K.finrank_faceDirection_of_card s.property.1 hc]
    have hslt := s.property.2
    omega
  have hproper : ∀ s, A s ≠ ⊤ := by
    intro s hs
    have h := hcodim s
    rw [hs, AffineSubspace.direction_top, finrank_top] at h
    omega
  let U : Set E := interior K.space \ ⋃ s, (A s : Set E)
  have hU : IsPathConnected U := AffineSubspace.isPathConnected_sdiff_iUnion
    A hcodim isOpen_interior hcv.interior hne
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU.isConnected.isPreconnected
  let Full := {s : Finset E // s ∈ K.faces ∧ s.card = Module.finrank ℝ E + 1}
  have hpick (x : U) : ∃ s : Full, (x : E) ∈ convexHull ℝ (s.val : Set E) := by
    obtain ⟨s, hs, hcard, hxs⟩ := K.exists_full_face_of_mem_interior hK x.property.1
    exact ⟨⟨s, hs, hcard⟩, hxs⟩
  choose piece hpiece using hpick
  let value : U → β := fun x => label (piece x)
  have hlocal : IsLocallyConstant value := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK
      (interior_subset x.property.1)
    have hcard : Module.finrank ℝ E ≤ s.card := by
      by_contra hn
      apply x.property.2
      exact mem_iUnion.mpr ⟨⟨s, hs, not_le.mp hn⟩,
        convexHull_subset_affineSpan _ (intrinsicInterior_subset hxs)⟩
    have hbase : s ⊆ (piece x).val := K.subset_of_mem_intrinsicInterior_face
      hs (piece x).property.1 hxs (hpiece x)
    have hpoint (t : Full) (hxt : (x : E) ∈ convexHull ℝ (t.val : Set E)) :
        label t = label (piece x) := by
      have hst : s ⊆ t.val := K.subset_of_mem_intrinsicInterior_face hs t.property.1 hxs hxt
      have htcard := t.property.2
      have hbcard := (piece x).property.2
      by_cases hc : s.card = Module.finrank ℝ E + 1
      · have ht : s = t.val := Finset.eq_of_subset_of_card_le hst (by omega)
        have hb : s = (piece x).val := Finset.eq_of_subset_of_card_le hbase (by omega)
        exact congrArg label (Subtype.ext (ht.symm.trans hb))
      · have hle := Finset.card_le_card hbase
        have hb := (piece x).property.2
        exact hadj t (piece x) s (by omega) hst hbase
    let Bad : Set (Finset E) := {t | t ∈ K.faces ∧ (x : E) ∉ convexHull ℝ (t : Set E)}
    let Z : Set E := ⋃ t ∈ Bad, convexHull ℝ (t : Set E)
    have hBad : Bad.Finite := hK.subset (fun _ ht => ht.1)
    have hZ : IsClosed Z :=
      (hBad.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
    have hxZ : (x : E) ∉ Z := by
      intro hx
      obtain ⟨t, htBad, hxt⟩ := mem_iUnion₂.mp hx
      exact htBad.2 hxt
    have hnear : ∀ᶠ y : U in 𝓝 x, (y : E) ∉ Z :=
      continuous_subtype_val.continuousAt.eventually (hZ.isOpen_compl.mem_nhds hxZ)
    filter_upwards [hnear] with y hy
    apply hpoint (piece y)
    by_contra hxy
    exact hy (mem_iUnion₂.mpr ⟨(piece y).val, ⟨(piece y).property.1, hxy⟩, hpiece y⟩)
  have hhit (s : Full) : ∃ x : U, piece x = s := by
    have hint : (interior (convexHull ℝ (s.val : Set E))).Nonempty := by
      apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
      simpa using ((K.indep s.property.1).affineBasisOfCard s.property.2).tot
    obtain ⟨x, hxs, hxA⟩ := (AffineSubspace.dense_compl_iUnion A hproper).inter_open_nonempty
      (interior (convexHull ℝ (s.val : Set E))) isOpen_interior hint
    have hxU : x ∈ U :=
      ⟨interior_mono (K.convexHull_subset_space s.property.1) hxs, hxA⟩
    let y : U := ⟨x, hxU⟩
    have hsub : s.val ⊆ (piece y).val := K.subset_of_mem_intrinsicInterior_face
      s.property.1 (piece y).property.1 (interior_subset_intrinsicInterior hxs) (hpiece y)
    have he : s.val = (piece y).val := Finset.eq_of_subset_of_card_le hsub (by
      rw [s.property.2, (piece y).property.2])
    exact ⟨y, Subtype.ext he.symm⟩
  intro s t
  obtain ⟨x, hx⟩ := hhit s
  obtain ⟨y, hy⟩ := hhit t
  have h := hlocal.apply_eq_of_preconnectedSpace x y
  change label (piece x) = label (piece y) at h
  rwa [hx, hy] at h

theorem det_mul_pos_of_injective_convex_pieces
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : 0 < Module.finrank ℝ E)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    {f : E → E} (hf : InjOn f K.space)
    (A : {s : Finset E // s ∈ K.faces ∧ s.card = Module.finrank ℝ E + 1} → E ≃ᵃ[ℝ] E)
    (hA : ∀ s, EqOn (A s) f (convexHull ℝ (s.val : Set E))) :
    ∀ s t, 0 < LinearMap.det ((A s).linear : E →ₗ[ℝ] E) *
      LinearMap.det ((A t).linear : E →ₗ[ℝ] E) := by
  classical
  let label := fun s => 0 < LinearMap.det ((A s).linear : E →ₗ[ℝ] E)
  have hadj : ∀ s t, ∀ r : Finset E, r.card = Module.finrank ℝ E →
      r ⊆ s.val → r ⊆ t.val → label s = label t := by
    intro s t r hr hrs hrt
    by_cases hst : s = t
    · rw [hst]
    have hneFaces : s.val ≠ t.val := fun h => hst (Subtype.ext h)
    have hpos := det_mul_pos_of_actual_paired_facet K hdim
      s.property.1 t.property.1 hr s.property.2 t.property.2 hrs hrt hneFaces hf
      (A s) (A t) (hA s) (hA t)
    apply propext
    constructor
    · intro hs
      by_contra ht
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hs.le (le_of_not_gt ht))) hpos
    · intro ht
      by_contra hs
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hs) ht.le)) hpos
  have hconst := full_face_label_constant K hK hcv hne label hadj
  intro s t
  have hiff : label s ↔ label t := iff_of_eq (hconst s t)
  rcases lt_or_gt_of_ne (A s).linear.isUnit_det'.ne_zero with hs | hs
  · rcases lt_or_gt_of_ne (A t).linear.isUnit_det'.ne_zero with ht | ht
    · exact mul_pos_of_neg_of_neg hs ht
    · exact (not_lt_of_ge hs.le (hiff.mpr ht)).elim
  · exact mul_pos hs (hiff.mp hs)

theorem exists_actual_convex_affine_pieces_with_same_sign
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : 0 < Module.finrank ℝ E)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    {f : E → E} (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) :
    ∃ A : {s : Finset E // s ∈ K.faces ∧ s.card = Module.finrank ℝ E + 1} → E ≃ᵃ[ℝ] E,
      (∀ s, EqOn (A s) f (convexHull ℝ (s.val : Set E))) ∧
      ∀ s t, 0 < LinearMap.det ((A s).linear : E →ₗ[ℝ] E) *
        LinearMap.det ((A t).linear : E →ₗ[ℝ] E) := by
  classical
  have hpieces (s : {s : Finset E // s ∈ K.faces ∧ s.card = Module.finrank ℝ E + 1}) :
      ∃ A : E ≃ᵃ[ℝ] E, EqOn A f (convexHull ℝ (s.val : Set E)) := by
    obtain ⟨a, ha⟩ := hf s.val s.property.1
    have hia : InjOn a.toAffineMap (convexHull ℝ (s.val : Set E)) := by
      intro x hx y hy hxy
      exact hinj (K.convexHull_subset_space s.property.1 hx)
        (K.convexHull_subset_space s.property.1 hy) ((ha hx).trans (hxy.trans (ha hy).symm))
    obtain ⟨A, hAa⟩ := exists_affineEquiv_of_injective_full_simplex
      K s.property.1 s.property.2 a.toAffineMap hia
    refine ⟨A, fun x hx => ?_⟩
    change A.toAffineMap x = f x
    rw [hAa]
    exact (ha hx).symm
  choose A hA using hpieces
  exact ⟨A, hA, det_mul_pos_of_injective_convex_pieces K hK hdim hcv hne hinj A hA⟩

end PoincareConjecture.M76.HamiltonIndexOne
