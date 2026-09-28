import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem saddle_selected_circle_images
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (label : Fin 2 ≃ Fin 2)
    (src : Fin 2 → ℝ → UnitTwoSphere)
    (gamma : Fin 2 → unitInterval → UnitTwoSphere)
    (La Dc Vs : Set UnitTwoSphere)
    (hVs : Vs ⊆ Dc)
    (hq : (⋃ i : Fin 2, range (q i)) = La)
    (hqd : ∀ i k : Fin 2, i ≠ k →
      Disjoint (range (q i)) (range (q k)))
    (hSrcParent : ∀ i : Fin 2, range (src i) ⊆ range (q (label i)))
    (hGammaParent : ∀ i : Fin 2, range (gamma i) ⊆ range (q (label i)))
    (hSourceCover : La \ Vs = ⋃ i : Fin 2, src i '' Icc (0 : ℝ) 1)
    (hConnectorCover : La ∩ Dc = ⋃ i : Fin 2, range (gamma i))
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (kp : OpenPartialHomeomorph E2 E2)
    (hksSource : closedBall (0 : E2) 1 ⊆ ks.source)
    (hDisc : ks '' closedBall (0 : E2) 1 = Dc)
    (Z : Fin 2 → Set E2)
    (hZ : ∀ i : Fin 2, Z i ⊆ closedBall (0 : E2) 1)
    (hConnector : ∀ i : Fin 2, ks '' Z i = range (gamma i))
    (F : E2 → E2) (A : UnitTwoSphere → E2)
    (C : Fin 2 → UnitCircle → E2)
    (hC : ∀ (i : Fin 2) (theta : UnitCircle), C i theta = A (q i theta))
    (hRegions : ∀ p ∈ La,
      (A p ∈ kp '' ball (0 : E2) 1 ↔ p ∈ Vs) ∧
      (A p ∈ kp '' closedBall (0 : E2) 1 ↔ p ∈ Dc))
    (hInside : ∀ p ∈ La, p ∈ Dc → A p = kp (F (ks.symm p))) :
    ∀ i : Fin 2,
      range (q (label i)) ∩ Dc = range (gamma i) ∧
      range (q (label i)) \ Vs = src i '' Icc (0 : ℝ) 1 ∧
      range (C (label i)) =
        (A '' (src i '' Icc (0 : ℝ) 1)) ∪ (kp '' (F '' Z i)) ∧
      range (C (label i)) ∩ (kp '' closedBall (0 : E2) 1) =
        kp '' (F '' Z i) ∧
      range (C (label i)) \ (kp '' ball (0 : E2) 1) =
        A '' (src i '' Icc (0 : ℝ) 1) := by
  classical
  have hqLa (i : Fin 2) {p : UnitTwoSphere} (hp : p ∈ range (q i)) : p ∈ La := by
    rw [← hq]
    exact mem_iUnion.mpr ⟨i, hp⟩
  have hlabel (i k : Fin 2) {p : UnitTwoSphere}
      (hi : p ∈ range (q (label i))) (hk : p ∈ range (q (label k))) : i = k := by
    apply label.injective
    by_contra hne
    exact Set.disjoint_left.mp (hqd (label i) (label k) hne) hi hk
  have hGamma (i : Fin 2) {p : UnitTwoSphere} (hp : p ∈ range (gamma i)) :
      p ∈ La ∩ Dc := by
    rw [hConnectorCover]
    exact mem_iUnion.mpr ⟨i, hp⟩
  have hSrc (i : Fin 2) {p : UnitTwoSphere} (hp : p ∈ src i '' Icc (0 : ℝ) 1) :
      p ∈ La \ Vs := by
    rw [hSourceCover]
    exact mem_iUnion.mpr ⟨i, hp⟩
  have hSrcRange (i : Fin 2) {p : UnitTwoSphere}
      (hp : p ∈ src i '' Icc (0 : ℝ) 1) : p ∈ range (q (label i)) := by
    rcases hp with ⟨t, -, rfl⟩
    exact hSrcParent i (mem_range_self t)
  have hSource (i : Fin 2) :
      range (q (label i)) ∩ Dc = range (gamma i) ∧
      range (q (label i)) \ Vs = src i '' Icc (0 : ℝ) 1 := by
    constructor
    · ext p
      constructor
      · rintro ⟨hp, hd⟩
        have hm : p ∈ ⋃ k : Fin 2, range (gamma k) := by
          rw [← hConnectorCover]
          exact ⟨hqLa _ hp, hd⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp hm
        have hik := hlabel i k hp (hGammaParent k hk)
        subst k
        exact hk
      · intro hp
        exact ⟨hGammaParent i hp, (hGamma i hp).2⟩
    · ext p
      constructor
      · rintro ⟨hp, hv⟩
        have hm : p ∈ ⋃ k : Fin 2, src k '' Icc (0 : ℝ) 1 := by
          rw [← hSourceCover]
          exact ⟨hqLa _ hp, hv⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp hm
        have hik := hlabel i k hp (hSrcRange k hk)
        subst k
        exact hk
      · intro hp
        exact ⟨hSrcRange i hp, (hSrc i hp).2⟩
  have hRange (i : Fin 2) : range (C (label i)) = A '' range (q (label i)) := by
    ext y
    constructor
    · rintro ⟨theta, rfl⟩
      exact ⟨q (label i) theta, mem_range_self theta, (hC (label i) theta).symm⟩
    · rintro ⟨p, ⟨theta, rfl⟩, rfl⟩
      exact ⟨theta, hC (label i) theta⟩
  have hPoint (i : Fin 2) (x : E2) (hx : x ∈ Z i) : A (ks x) = kp (F x) := by
    have hg : ks x ∈ range (gamma i) := by
      rw [← hConnector i]
      exact ⟨x, hx, rfl⟩
    have hd : ks x ∈ Dc := by
      rw [← hDisc]
      exact ⟨x, hZ i hx, rfl⟩
    simpa only [ks.left_inv (hksSource (hZ i hx))] using
      hInside (ks x) (hGamma i hg).1 hd
  have hInnerImage (i : Fin 2) : A '' range (gamma i) = kp '' (F '' Z i) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hConnector i] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      exact ⟨F x, ⟨x, hx, rfl⟩, (hPoint i x hx).symm⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨ks x, ?_, hPoint i x hx⟩
      rw [← hConnector i]
      exact ⟨x, hx, rfl⟩
  intro i
  refine ⟨(hSource i).1, (hSource i).2, ?_, ?_, ?_⟩
  · rw [← hInnerImage i, hRange i]
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      by_cases hv : p ∈ Vs
      · right
        refine ⟨p, ?_, rfl⟩
        rw [← (hSource i).1]
        exact ⟨hp, hVs hv⟩
      · left
        refine ⟨p, ?_, rfl⟩
        rw [← (hSource i).2]
        exact ⟨hp, hv⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact ⟨p, hSrcRange i hp, rfl⟩
      · exact ⟨p, hGammaParent i hp, rfl⟩
  · rw [← hInnerImage i, hRange i]
    ext y
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hy⟩
      refine ⟨p, ?_, rfl⟩
      rw [← (hSource i).1]
      exact ⟨hp, (hRegions p (hqLa _ hp)).2.mp hy⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hGammaParent i hp, rfl⟩,
        (hRegions p (hGamma i hp).1).2.mpr (hGamma i hp).2⟩
  · rw [hRange i]
    ext y
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hy⟩
      refine ⟨p, ?_, rfl⟩
      rw [← (hSource i).2]
      exact ⟨hp, fun hv => hy ((hRegions p (hqLa _ hp)).1.mpr hv)⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hSrcRange i hp, rfl⟩,
        fun hy => (hSrc i hp).2 ((hRegions p (hSrc i hp).1).1.mp hy)⟩

end PoincareConjecture.M25.Topology3D
