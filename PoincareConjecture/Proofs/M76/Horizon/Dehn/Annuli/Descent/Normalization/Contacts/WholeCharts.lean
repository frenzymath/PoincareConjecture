import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Contacts.SourceIsolation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ProjectedCrossingCoordinates

set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ V} {j : V → t.Carrier} {R : Set M} {boundary : Set V}

namespace OriginalRelativeNormalization

variable (D : OriginalRelativeNormalization step K j R boundary)

omit [FiniteDimensional ℝ V] in
theorem double_point_interior {x y : V} (hx : x ∈ K.space) (hy : y ∈ K.space)
    (hne : x ≠ y) (hxy : D.projected x = D.projected y) :
    D.projected x ∈ interior (s.projection ⁻¹' R) := by
  by_contra hn
  have hfront : D.projected x ∈ frontier (s.projection ⁻¹' R) :=
    ⟨subset_closure (D.projected_region hx), hn⟩
  have hxb := (D.projected_proper x hx).mp hfront
  have hyb := (D.projected_proper y hy).mp (hxy ▸ hfront)
  apply hne (D.protected_fiber x (D.boundary_protected hxb) y hy ?_)
  have h := hxy
  rw [D.projected_boundary hxb, D.projected_boundary hyb] at h
  exact h

theorem exists_whole_projected_crossing
    (hcard : ∀ a ∈ K.faces, a.card ≤ 3)
    {x y : V} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : D.projected x = D.projected y) (hex : D.projected x ∉ D.exceptionalValues)
    (W : Set s.Carrier) (hW : IsOpen W) (hxW : D.projected x ∈ W) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (T : OpenPartialHomeomorph s.Carrier V3),
      ((D.endpoint x ∈ w.left.source ∧ D.endpoint y ∈ w.right.source) ∨
        (D.endpoint x ∈ w.right.source ∧ D.endpoint y ∈ w.left.source)) ∧
      D.projected x ∈ T.source ∧
      T.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) ∧
      T (D.projected x) = 0 ∧
      (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans T) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans T) ∈ piecewiseAffineGroupoid V3) ∧
      (step.projection ∘ step.inclusion) ⁻¹' T.source =
        (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
          (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
      (∀ z ∈ T.source, z ∈ (step.projection ∘ step.inclusion) ''
        (D.endpoint '' K.space ∩ w.left.source) ↔ T z 0 = 0) ∧
      ∀ z ∈ T.source, z ∈ (step.projection ∘ step.inclusion) ''
        (D.endpoint '' K.space ∩ w.right.source) ↔ T z 1 = 0 := by
  classical
  obtain ⟨i, x', y', old, H, hswap, hxface, hyface, hi3, hk3, hxQ, hyB,
    hcommon, hpH, hHBtarget, hH0, hHPL, _hHiPL, hleftface, hrightface⟩ :=
    D.exists_projected_face_crossing hcard hx hy hne hxy hex
  let p := step.projection ∘ step.inclusion
  let B := (D.activeBox i).lower
  let a : D.source.faces := ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩
  let b : D.source.faces := ⟨old.val, D.prefix_le i.val old.property⟩
  have hxsource := D.source.convexHull_subset_space a.property (intrinsicInterior_subset hxface)
  have hysource := D.source.convexHull_subset_space b.property (intrinsicInterior_subset hyface)
  have hxbase : D.projected x' = D.projected x := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hxy.symm
  have hybase : D.projected y' = D.projected x := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy.symm
    · rfl
  have hneq : x' ≠ y' := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact hne.symm
  have hinj : InjOn D.endpoint D.source.space := by
    intro z hz v hv hzv
    exact congrArg Subtype.val ((D.states D.length).embedding.injective
      (a₁ := ⟨z, hz⟩) (a₂ := ⟨v, hv⟩) hzv)
  obtain ⟨w, hxw, hyw⟩ := step.projectionInclusion_local.exists_twoBranchWindow
    (fun z ↦ (step.projectionInclusion_fiber z).1)
    (fun z ↦ (step.projectionInclusion_fiber z).2)
    (hxbase.trans hybase.symm) (fun h ↦ hneq (hinj hxsource hysource h))
  have hmax {c : Finset V} (hc3 : c.card = 3) :
      ∀ d ∈ D.source.faces, c ⊆ d → d = c := by
    intro d hd hcd
    exact (Finset.eq_of_subset_of_card_le hcd (by
      have h := D.source_card_le hcard hd
      omega)).symm
  obtain ⟨V₀, hV₀, hxV₀, hV₀target, hVL⟩ :=
    D.source.exists_projected_branch_face_neighborhood D.source_finite
      (D.states D.length).embedding w.left w.left_eq a.property (hmax hi3) hxface hxw
  obtain ⟨V₁, hV₁, hyV₁, hV₁target, hVR⟩ :=
    D.source.exists_projected_branch_face_neighborhood D.source_finite
      (D.states D.length).embedding w.right w.right_eq b.property (hmax hk3) hyface hyw
  have hxV : D.projected x ∈ V₀ := hxbase ▸ hxV₀
  have hyV : D.projected x ∈ V₁ := hybase ▸ hyV₁
  let N := W ∩ (interior (s.projection ⁻¹' R) ∩ (V₀ ∩ V₁))
  have hN : IsOpen N := hW.inter (isOpen_interior.inter (hV₀.inter hV₁))
  have hxN : D.projected x ∈ N := ⟨hxW, D.double_point_interior hx hy hne hxy, hxV, hyV⟩
  let coord := H.trans crossingCoordinatesLeftLast.toHomeomorph.toOpenPartialHomeomorph
  let T := (B.trans coord).restrOpen N hN
  have hxB : D.projected x ∈ B.source := hybase ▸ hyB
  have hxcoord : B (D.projected x) = (D.activeBox i).upper (D.endpoint x') :=
    (congrArg B hybase).symm.trans hcommon.symm
  have hxT : D.projected x ∈ T.source :=
    ⟨⟨hxB, hxcoord.symm ▸ hpH, mem_univ _⟩, hxN⟩
  have hTw : T.source ⊆ w.target := by
    intro z hz
    exact w.left_target.subset (hV₀target hz.2.2.2.1)
  have hTPL (k : s.Index) : (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    have hcoord := (locallyPiecewiseAffineOn_affine
      crossingCoordinatesLeftLast.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp hHPL
    have hcomp := hcoord.comp ((D.activeBox i).lower_compatible k).1
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact hcomp.mono ((s.charts k).symm.trans T).open_source
      (fun z hz ↦ ⟨⟨hz.1, hz.2.1.1⟩, hz.2.1.2⟩)
  have hdistinct : a.val ≠ b.val := by
    intro hab
    have hyactive : y' ∈ convexHull ℝ (a.val : Set V) :=
      hab.symm ▸ intrinsicInterior_subset hyface
    have hretx := (D.states D.length).retained a (intrinsicInterior_subset hxface)
    have hrety := (D.states D.length).retained a hyactive
    have hmapsame := (D.box a).neighborhood_injective hretx hrety (hxbase.trans hybase.symm)
    exact hneq (hinj hxsource hysource hmapsame)
  have hno (c d : D.source.faces) (hc3 : c.val.card = 3) (hd3 : d.val.card = 3)
      (hcd : c.val ≠ d.val) {q : V}
      (hqc : q ∈ convexHull ℝ (c.val : Set V))
      (hqd : q ∈ intrinsicInterior ℝ (convexHull ℝ (d.val : Set V))) : False := by
    have hsub := D.source.subset_of_mem_intrinsicInterior_face d.property c.property hqd hqc
    exact hcd ((Finset.eq_of_subset_of_card_le hsub (by omega)).symm)
  have hleft (z : s.Carrier) (hz : z ∈ T.source) :
      z ∈ p '' (D.endpoint '' K.space ∩ w.left.source) ↔
        z ∈ D.projected '' convexHull ℝ (a.val : Set V) := by
    constructor
    · rintro ⟨_, ⟨⟨q, hq, rfl⟩, hqL⟩, hqz⟩
      exact ⟨q, intrinsicInterior_subset (hVL z hz.2.2.2.1 q
        (D.subdivision.space_eq.symm.subset hq) hqL hqz), hqz⟩
    · rintro ⟨q, hqface, hqz⟩
      have hqsource := D.source.convexHull_subset_space a.property hqface
      have hqK := D.subdivision.space_eq.subset hqsource
      have hqwindow : D.endpoint q ∈ w.left.source ∪ w.right.source := by
        apply w.whole_preimage.subset
        change D.projected q ∈ w.target
        exact hqz.symm ▸ hTw hz
      rcases hqwindow with hqL | hqR
      · exact ⟨D.endpoint q, ⟨mem_image_of_mem _ hqK, hqL⟩, hqz⟩
      · exact (hno a b hi3 hk3 hdistinct hqface
          (hVR z hz.2.2.2.2 q hqsource hqR hqz)).elim
  have hright (z : s.Carrier) (hz : z ∈ T.source) :
      z ∈ p '' (D.endpoint '' K.space ∩ w.right.source) ↔
        z ∈ D.projected '' convexHull ℝ (b.val : Set V) := by
    constructor
    · rintro ⟨_, ⟨⟨q, hq, rfl⟩, hqR⟩, hqz⟩
      exact ⟨q, intrinsicInterior_subset (hVR z hz.2.2.2.2 q
        (D.subdivision.space_eq.symm.subset hq) hqR hqz), hqz⟩
    · rintro ⟨q, hqface, hqz⟩
      have hqsource := D.source.convexHull_subset_space b.property hqface
      have hqK := D.subdivision.space_eq.subset hqsource
      have hqwindow : D.endpoint q ∈ w.left.source ∪ w.right.source := by
        apply w.whole_preimage.subset
        change D.projected q ∈ w.target
        exact hqz.symm ▸ hTw hz
      rcases hqwindow with hqL | hqR
      · exact (hno b a hk3 hi3 hdistinct.symm hqface
          (hVL z hz.2.2.2.1 q hqsource hqL hqz)).elim
      · exact ⟨D.endpoint q, ⟨mem_image_of_mem _ hqK, hqR⟩, hqz⟩
  have hcoordinate (c : Finset V) (z : s.Carrier) (hz : z ∈ B.source) :
      z ∈ D.projected '' convexHull ℝ (c : Set V) ↔
        B z ∈ B '' (D.projected '' convexHull ℝ (c : Set V) ∩ B.source) := by
    constructor
    · intro hzc
      exact mem_image_of_mem B ⟨hzc, hz⟩
    · rintro ⟨v, ⟨hvc, hvB⟩, hvz⟩
      exact B.injOn hvB hz hvz ▸ hvc
  refine ⟨w, T, ?_, hxT, fun z hz ↦ ⟨hz.2.1, hz.2.2.1, hTw hz⟩,
    ?_, hTPL, ?_, ?_, ?_, ?_⟩
  · rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hxw, hyw⟩
    · exact Or.inr ⟨hyw, hxw⟩
  · change crossingCoordinatesLeftLast (H (B (D.projected x))) = 0
    rw [hxcoord, hH0]
    exact map_zero _
  · intro k
    exact ⟨step.compatible_branch_chart w.left (fun z _ ↦ congrFun w.left_eq z) T hTPL k,
      step.compatible_branch_chart w.right (fun z _ ↦ congrFun w.right_eq z) T hTPL k⟩
  · ext z
    constructor
    · intro hz
      rcases w.whole_preimage.subset (hTw hz) with hl | hr
      · exact Or.inl ⟨hl, hz⟩
      · exact Or.inr ⟨hr, hz⟩
    · exact fun hz ↦ hz.elim And.right And.right
  · intro z hz
    exact (hleft z hz).trans ((hcoordinate a.val z hz.1.1).trans
      (hleftface (B z) hz.1.2.1))
  · intro z hz
    exact (hright z hz).trans ((hcoordinate b.val z hz.1.1).trans
      (hrightface (B z) hz.1.2.1))

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
