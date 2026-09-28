import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexLabels
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBlocks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}




structure HamiltonProperDiskNormalLabels
    (T : HamiltonProperDiskTriangulation R D b) (c : E ≃ᴬ[ℝ] V) where

  weight : T.disk.vertices → ℝ

  nonzero : ∀ p, weight p ≠ 0


  alignment : ∀ (p : T.disk.vertices) (s u : Finset E), s ∈ T.disk.faces →
    s.card = 3 → (p : E) ∈ s → u ∈ T.ambient.faces → u.card = 4 → s ⊆ u →
    ∀ (P : V2 →ᴬ[ℝ] E), Function.Injective P →
      (∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x) →
      ∀ w ∈ convexHull ℝ (u : Set E), ((T.pairChart p).chart w).2 ≠ 0 →
        0 < affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P.toAffineMap) (c w) *
          (weight p * ((T.pairChart p).chart w).2)




theorem HamiltonProperDiskTriangulation.exists_normal_labels
    [FiniteDimensional ℝ E] (T : HamiltonProperDiskTriangulation R D b)
    (hb : b.IsFinitePL) (c : E ≃ᴬ[ℝ] V) :
    Nonempty (HamiltonProperDiskNormalLabels T c) := by
  classical
  choose δ hδ halign using fun p => T.exists_vertex_normal_label hb p c
  exact ⟨⟨δ, hδ, halign⟩⟩

variable {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}



noncomputable def HamiltonProperDiskNormalLabels.height
    (O : HamiltonProperDiskNormalLabels T c) (p : T.disk.vertices) (x : E) : ℝ :=
  O.weight p * ((T.pairChart p).chart x).2



theorem HamiltonProperDiskNormalLabels.height_eq_zero_iff
    (O : HamiltonProperDiskNormalLabels T c) (p : T.disk.vertices)
    {x : E} (hx : x ∈ (T.pairChart p).chart.source) (hxR : x ∈ R) :
    O.height p x = 0 ↔ x ∈ D := by
  rw [HamiltonProperDiskNormalLabels.height, mul_eq_zero, or_iff_right (O.nonzero p)]
  rcases (T.pairChart p).model with ⟨_, hplane⟩ | ⟨hregion, hplane⟩
  · exact (hplane x hx).symm
  · have hR := (hregion x hx).mp hxR
    exact ⟨fun h => (hplane x hx).mpr ⟨hR, h⟩,
      fun h => ((hplane x hx).mp h).2⟩



theorem HamiltonProperDiskNormalLabels.continuousOn_height
    (O : HamiltonProperDiskNormalLabels T c) (p : T.disk.vertices) :
    ContinuousOn (O.height p) (T.pairChart p).chart.source :=
  continuousOn_const.mul ((T.pairChart p).chart.continuousOn_toFun.snd)




theorem HamiltonProperDiskNormalLabels.mul_pos_on_common_triangle
    [FiniteDimensional ℝ E] (O : HamiltonProperDiskNormalLabels T c)
    (p q : T.disk.vertices) {s u : Finset E} (hs : s ∈ T.disk.faces)
    (hsc : s.card = 3) (hps : (p : E) ∈ s) (hqs : (q : E) ∈ s)
    (hu : u ∈ T.ambient.faces) (huc : u.card = 4) (hsu : s ⊆ u)
    {w : E} (hw : w ∈ convexHull ℝ (u : Set E))
    (hp : ((T.pairChart p).chart w).2 ≠ 0) (hq : ((T.pairChart q).chart w).2 ≠ 0) :
    0 < O.height p w * O.height q w := by
  obtain ⟨P, hPi, hP, _, _⟩ := T.exists_original_triangle_parameter hs hsc
  have h1 := O.alignment p s u hs hsc hps hu huc hsu P hPi hP w hw hp
  have h2 := O.alignment q s u hs hsc hqs hu huc hsu P hPi hP w hw hq
  let n := affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P.toAffineMap) (c w)
  have hn : n ≠ 0 := by
    intro hn
    change 0 < n * O.height p w at h1
    rw [hn, zero_mul] at h1
    exact lt_irrefl _ h1
  have hpos : 0 < (n * n) * (O.height p w * O.height q w) := by
    have h := mul_pos h1 h2
    change 0 < (n * O.height p w) * (n * O.height q w) at h
    convert h using 1; ring
  exact (mul_pos_iff_of_pos_left (mul_self_pos.mpr hn)).mp hpos






theorem HamiltonProperDiskNormalLabels.nonneg_on_half_of_incident_witness
    [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O : HamiltonProperDiskNormalLabels T c) (p q : T.disk.vertices)
    {B Q : Set E} (hB : IsFinitePLBallPair F B Q)
    (hBR : B ⊆ R) (hBS : B ⊆ (T.pairChart q).chart.source)
    (hBD : B ∩ D ⊆ Q)
    {s u : Finset E} (hs : s ∈ T.disk.faces) (hsc : s.card = 3)
    (hps : (p : E) ∈ s) (hqs : (q : E) ∈ s)
    (hu : u ∈ T.ambient.faces) (huc : u.card = 4) (hsu : s ⊆ u)
    {w : E} (hwB : w ∈ B) (hw : w ∈ convexHull ℝ (u : Set E))
    (hp : 0 < O.height p w) (hwD : w ∉ D) :
    MapsTo (O.height q) B (Ici 0) := by
  have hp0 : ((T.pairChart p).chart w).2 ≠ 0 := by
    intro h
    change 0 < O.weight p * ((T.pairChart p).chart w).2 at hp
    rw [h, mul_zero] at hp
    exact lt_irrefl _ hp
  have hq0 : ((T.pairChart q).chart w).2 ≠ 0 := by
    intro h
    apply hwD
    apply (O.height_eq_zero_iff q (hBS hwB) (hBR hwB)).mp
    exact mul_eq_zero_of_right _ h
  have hpos := O.mul_pos_on_common_triangle p q hs hsc hps hqs hu huc hsu hw hp0 hq0
  have hqpos : 0 < O.height q w := (mul_pos_iff_of_pos_left hp).mp hpos
  apply hB.mapsTo_nonneg_of_zeros_in_boundary (O.height q)
    ((O.continuousOn_height q).mono hBS)
  · intro x hx
    exact hBD ⟨hx.1, (O.height_eq_zero_iff q (hBS hx.1) (hBR hx.1)).mp hx.2⟩
  · exact ⟨w, hwB, hqpos⟩



theorem HamiltonProperDiskNormalLabels.nonpos_on_half_of_incident_witness
    [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O : HamiltonProperDiskNormalLabels T c) (p q : T.disk.vertices)
    {B Q : Set E} (hB : IsFinitePLBallPair F B Q)
    (hBR : B ⊆ R) (hBS : B ⊆ (T.pairChart q).chart.source)
    (hBD : B ∩ D ⊆ Q)
    {s u : Finset E} (hs : s ∈ T.disk.faces) (hsc : s.card = 3)
    (hps : (p : E) ∈ s) (hqs : (q : E) ∈ s)
    (hu : u ∈ T.ambient.faces) (huc : u.card = 4) (hsu : s ⊆ u)
    {w : E} (hwB : w ∈ B) (hw : w ∈ convexHull ℝ (u : Set E))
    (hp : O.height p w < 0) (hwD : w ∉ D) :
    MapsTo (O.height q) B (Iic 0) := by
  have hp0 : ((T.pairChart p).chart w).2 ≠ 0 := by
    intro h
    change O.weight p * ((T.pairChart p).chart w).2 < 0 at hp
    rw [h, mul_zero] at hp
    exact lt_irrefl _ hp
  have hq0 : ((T.pairChart q).chart w).2 ≠ 0 := by
    intro h
    apply hwD
    apply (O.height_eq_zero_iff q (hBS hwB) (hBR hwB)).mp
    exact mul_eq_zero_of_right _ h
  have hpos := O.mul_pos_on_common_triangle p q hs hsc hps hqs hu huc hsu hw hp0 hq0
  have hqneg : O.height q w < 0 := by
    by_contra hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hp.le (le_of_not_gt hn))) hpos
  apply hB.mapsTo_nonpos_of_zeros_in_boundary (O.height q)
    ((O.continuousOn_height q).mono hBS)
  · intro x hx
    exact hBD ⟨hx.1, (O.height_eq_zero_iff q (hBS hx.1) (hBR hx.1)).mp hx.2⟩
  · exact ⟨w, hwB, hqneg⟩





theorem HamiltonProperDiskNormalLabels.half_eq_of_whole_signs
    (O : HamiltonProperDiskNormalLabels T c) (p q : T.disk.vertices)
    {S : Set E} (hSR : S ⊆ R)
    (hSp : S ⊆ (T.pairChart p).chart.source) (hSq : S ⊆ (T.pairChart q).chart.source)
    (hpos : MapsTo (O.height q) (S ∩ {x | 0 ≤ O.height p x}) (Ici 0))
    (hneg : MapsTo (O.height q) (S ∩ {x | O.height p x ≤ 0}) (Iic 0)) :
    S ∩ {x | 0 ≤ O.height p x} = S ∩ {x | 0 ≤ O.height q x} := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨hx.1, hpos hx⟩
  · rintro x ⟨hxS, hxq⟩
    refine ⟨hxS, ?_⟩
    by_contra hn
    have hxp : O.height p x < 0 := lt_of_not_ge hn
    have hzq : O.height q x = 0 := le_antisymm (hneg ⟨hxS, hxp.le⟩) hxq
    have hxD := (O.height_eq_zero_iff q (hSq hxS) (hSR hxS)).mp hzq
    have hzp := (O.height_eq_zero_iff p (hSp hxS) (hSR hxS)).mpr hxD
    rw [hzp] at hxp
    exact lt_irrefl _ hxp

end PoincareConjecture.M76.HamiltonIndexOne
