import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeJointMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedHalfFaceMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPrismRim

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

def signedTubePrismAxis (α β : ℝ) : Set (P2 × ℝ) := {(0, 0)} ×ˢ Icc α β

def signedTubePrismOuter (i : Fin 2) (sign : Bool) (α β : ℝ) : Set (P2 × ℝ) :=
  ({signedTubeCorner i sign} ×ˢ Icc α β) ∪ (signedTubeRadius i sign ×ˢ {α, β})

theorem signedTubePrism_axis_ball (α β : ℝ) (hαβ : α < β) :
    IsFinitePLBallPair ℝ (signedTubePrismAxis α β) {((0, 0), α), ((0, 0), β)} := by
  let f : ℝ →ᴬ[ℝ] P2 × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ (0, 0)).prod (ContinuousAffineMap.id ℝ ℝ)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.snd h
  have h := (isFinitePLBallPair_Icc hαβ).affine_image f hf.injOn
  change IsFinitePLBallPair ℝ ((fun t : ℝ => ((0, 0), t)) '' Icc α β)
    ((fun t : ℝ => ((0, 0), t)) '' {α, β}) at h
  simpa only [signedTubePrismAxis, singleton_prod, image_pair] using h

theorem signedTubePrism_end_ball (i : Fin 2) (sign : Bool) (t : ℝ) :
    IsFinitePLBallPair ℝ (signedTubeRadius i sign ×ˢ {t})
      {((0, 0), t), (signedTubeCorner i sign, t)} := by
  have h := (signedTube_radius_ball i sign).prod_singleton t
  have heq : ({(0, 0), signedTubeCorner i sign} : Set P2) ×ˢ {t} =
      {((0, 0), t), (signedTubeCorner i sign, t)} := by
    ext x
    simp only [mem_prod, mem_insert_iff, mem_singleton_iff, Prod.ext_iff]
    tauto
  rwa [heq] at h

theorem signedTubePrism_boundary (i : Fin 2) (sign : Bool) (α β : ℝ) (hαβ : α < β) :
    IsFinitePLBallPair P2 (signedTubeRadius i sign ×ˢ Icc α β)
      (signedTubePrismAxis α β ∪ signedTubePrismOuter i sign α β) ∧
    IsFinitePLBallPair ℝ (signedTubePrismOuter i sign α β)
      {((0, 0), α), ((0, 0), β)} ∧
    signedTubePrismAxis α β ∩ signedTubePrismOuter i sign α β =
      {((0, 0), α), ((0, 0), β)} := by
  let r := signedTubeRadius i sign
  let c := signedTubeCorner i sign
  let axis := signedTubePrismAxis α β
  let outer := signedTubePrismOuter i sign α β
  have hz : (0, 0) ∈ r := left_mem_segment ℝ _ _
  have hc : c ≠ (0, 0) := signedTube_corner_ne_center i sign
  have hcover : axis ∪ outer =
      (({(0, 0), c} : Set P2) ×ˢ Icc α β) ∪ (r ×ˢ {α, β}) := by
    ext x
    simp only [axis, outer, signedTubePrismAxis, signedTubePrismOuter,
      mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have hball : IsFinitePLBallPair P2 (r ×ˢ Icc α β) (axis ∪ outer) := by
    rw [hcover]
    exact (signedTube_radius_ball i sign).prod (isFinitePLBallPair_Icc hαβ)
  have hinter : axis ∩ outer = {((0, 0), α), ((0, 0), β)} := by
    ext x
    constructor
    · rintro ⟨hxA, hxO | hxO⟩
      · exact False.elim (hc (hxO.1.symm.trans hxA.1))
      · rcases hxO.2 with hα | hβ
        · exact Or.inl (Prod.ext hxA.1 hα)
        · exact Or.inr (Prod.ext hxA.1 hβ)
    · rintro (rfl | rfl)
      · exact ⟨⟨rfl, le_rfl, hαβ.le⟩, Or.inr ⟨hz, Or.inl rfl⟩⟩
      · exact ⟨⟨rfl, hαβ.le, le_rfl⟩, Or.inr ⟨hz, Or.inr rfl⟩⟩
  have hne : (((0, 0) : P2), α) ≠ ((0, 0), β) := fun h => hαβ.ne (congrArg Prod.snd h)
  obtain ⟨W, hW, hAW, hIW⟩ := hball.exists_boundary_arc_complement
    (signedTubePrism_axis_ball α β hαβ) subset_union_left hne
  have hWO : W = outer := by
    ext x
    have hu := Set.ext_iff.mp hAW x
    have hi := Set.ext_iff.mp hIW x
    have hj := Set.ext_iff.mp hinter x
    change (x ∈ axis ∨ x ∈ W) ↔ (x ∈ axis ∨ x ∈ outer) at hu
    change (x ∈ axis ∧ x ∈ W) ↔ x ∈ ({((0, 0), α), ((0, 0), β)} : Set (P2 × ℝ)) at hi
    change (x ∈ axis ∧ x ∈ outer) ↔ x ∈ ({((0, 0), α), ((0, 0), β)} : Set (P2 × ℝ)) at hj
    by_cases hx : x ∈ axis
    · exact ⟨fun h => (hj.mpr (hi.mp ⟨hx, h⟩)).2,
        fun h => (hi.mpr (hj.mp ⟨hx, h⟩)).2⟩
    · exact ⟨fun h => (hu.mp (Or.inr h)).resolve_left hx,
        fun h => (hu.mpr (Or.inr h)).resolve_left hx⟩
  refine ⟨hball, ?_, hinter⟩
  simpa only [hWO] using hW

noncomputable def signedTubePrismEndProjection (i : Fin 2) (sign : Bool) (t : ℝ) :
    ↥(signedTubeRadius i sign ×ˢ {t}) ≃ₜ signedTubeRadius i sign :=
  (Homeomorph.Set.prod _ _).trans (Homeomorph.prodUnique _ _)

noncomputable def signedTubePrismAxisProjection (α β : ℝ) :
    signedTubePrismAxis α β ≃ₜ Icc α β :=
  (Homeomorph.Set.prod _ _).trans (Homeomorph.uniqueProd _ _)

theorem signedTubePrismEndProjection_isFinitePL (i : Fin 2) (sign : Bool) (t : ℝ) :
    (signedTubePrismEndProjection i sign t).IsFinitePL := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := signedTubePrism_end_ball i sign t
  exact ⟨Prod.fst, ⟨K, hK, hKs,
    K.affineOnFaces_affine (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap⟩, fun _ => rfl⟩

theorem signedTubePrismAxisProjection_isFinitePL (α β : ℝ) (hαβ : α < β) :
    (signedTubePrismAxisProjection α β).IsFinitePL := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := signedTubePrism_axis_ball α β hαβ
  exact ⟨Prod.snd, ⟨K, hK, hKs,
    K.affineOnFaces_affine (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap⟩, fun _ => rfl⟩

end PoincareConjecture.M76.Dehn
