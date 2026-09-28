import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.SphereTwoFiberCellularity
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.RegionCellularCancellation










set_option autoImplicit false

open Set Metric

namespace ContinuousMap

variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]




theorem exists_region_marked_sphere_quotient_cancellation (q : C(X, Y))
    (hq : Function.Surjective q) (a b : Y) (hab : a ≠ b)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b))
    (eX : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (eY : Y ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (p : X) (hpa : q p ≠ a) (hpb : q p ≠ b)
    {U V D P : Set X} {C B : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hAU : q ⁻¹' {a} ⊆ U) (hBV : q ⁻¹' {b} ⊆ V)
    (hUD : U ⊆ D) (hVD : V ⊆ Dᶜ) (hP : P ⊆ (U ∪ V)ᶜ)
    (hmark : ∀ x, q x ∈ B ↔ x ∈ P) (hregion : ∀ x, q x ∈ C ↔ x ∈ D) :
    ∃ H : X ≃ₜ Y, EqOn H q P ∧ (∀ x, H x ∈ B ↔ x ∈ P) ∧
      ∀ x, H x ∈ C ↔ x ∈ D := by
  obtain ⟨K, L, hK, hL, hnestK, hnestL, hpairK, hpairL, hdis, hK0, hL0, hKA, hLB⟩ :=
    q.exists_sphere_two_fiber_cellular_sequences hq a b hab hfib eX eY p hpa hpb
      hU hV hUV hAU hBV
  have hPc : P ⊆ (interior (K 0) ∪ interior (L 0))ᶜ := by
    intro x hx
    rintro (hxK | hxL)
    · exact hP hx (Or.inl (hK0 (interior_subset hxK)))
    · exact hP hx (Or.inr (hL0 (interior_subset hxL)))
  have hfib' (x y : X) : q x = q y ↔ x = y ∨
      (x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n) ∨
      (x ∈ ⋂ n, L n) ∧ (y ∈ ⋂ n, L n) := by
    simpa only [hKA, hLB, mem_preimage, mem_singleton_iff] using hfib x y
  exact Homeomorph.exists_region_marked_of_disjoint_cellular_fibers K L hK hL hnestK hnestL
    hpairK hpairL hdis q hq hfib' (hK0.trans hUD) (hL0.trans hVD) hPc hmark hregion

end ContinuousMap
