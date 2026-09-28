import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Maximal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Endpoints
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Reversal




set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {ε : ℝ} {C D : BalancedNeckChain g ε}

local notation "slab(" N ")" => EpsilonNeck.coordinate_map N ''
  (Set.prod univ (Icc (-(3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)
    ((3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)))

theorem IsSelectedFrom.isSeparating {H : NeckOnlyCover g} (hC : C.IsSelectedFrom H)
    (hsep : ∀ N ∈ H.necks, N.IsSeparating) {i : ℤ} (hi : i ∈ C.shape.active) :
    (C.neck i).IsSeparating := by
  obtain ⟨N, hN, hsame⟩ := C.selected i hi
  exact hsame.isSeparating_iff.mpr (hsep N (hC.1 hN))

theorem IsSelectedFrom.of_insert {H : NeckOnlyCover g} (hC : C.IsSelectedFrom H)
    (hext : C.IsExtension D) {j : ℤ} {S : EpsilonNeck g}
    (hactive : D.shape.active = insert j C.shape.active)
    (hsource : D.source_necks = insert S C.source_necks)
    (hS : S ∈ H.necks) (hcenter : (D.neck j).center ∈ H.X) :
    D.IsSelectedFrom H := by
  constructor
  · rw [hsource]
    exact insert_subset hS hC.1
  · intro i hi
    rw [hactive, mem_insert_iff] at hi
    rcases hi with rfl | hi
    · exact hcenter
    · rw [← hext.2.2 i hi]
      exact hC.2 i hi

theorem HasQuarterCapture.of_append (hC : C.HasQuarterCapture)
    (hext : C.IsExtension D) {b : ℤ} (hb : b ∈ C.shape.active)
    (hnext : b + 1 ∉ C.shape.active) (hshape : D.shape = C.shape.extendRight)
    (hnew : (C.neck b).region (ε⁻¹ / 2) ε⁻¹ ⊆ slab(D.neck (b + 1))) :
    D.HasQuarterCapture := by
  have hactive : D.shape.active = insert (b + 1) C.shape.active := by
    rw [hshape, ChainShape.extendRight_active hb hnext]
  intro i hi hj
  rw [hactive, mem_insert_iff] at hi hj
  have hmax {k : ℤ} (hk : k ∈ C.shape.active) : k ≤ b :=
    ChainShape.le_of_right_endpoint hb hnext hk
  have hiold : i ∈ C.shape.active := by
    rcases hi with rfl | hi
    · rcases hj with hj | hj
      · omega
      · have := hmax hj
        omega
    · exact hi
  rcases hj with hj | hj
  · have hib : i = b := by omega
    subst i
    rw [← hext.2.2 b hb]
    exact Or.inl hnew
  · rw [← hext.2.2 i hiold, ← hext.2.2 (i + 1) hj]
    exact hC i hiold hj

theorem HasQuarterCapture.of_prepend (hC : C.HasQuarterCapture)
    (hext : C.IsExtension D) {a : ℤ} (ha : a ∈ C.shape.active)
    (hprev : a - 1 ∉ C.shape.active) (hshape : D.shape = C.shape.extendLeft)
    (hnew : (C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ slab(D.neck (a - 1))) :
    D.HasQuarterCapture := by
  have hactive : D.shape.active = insert (a - 1) C.shape.active := by
    rw [hshape, ChainShape.extendLeft_active ha hprev]
  intro i hi hj
  rw [hactive, mem_insert_iff] at hi hj
  rcases hi with rfl | hi
  · rw [show a - 1 + 1 = a by omega, ← hext.2.2 a ha]
    exact Or.inr hnew
  · have hjold : i + 1 ∈ C.shape.active := by
      rcases hj with hj | hj
      · have := ChainShape.le_of_left_endpoint ha hprev hi
        omega
      · exact hj
    rw [← hext.2.2 i hi, ← hext.2.2 (i + 1) hjold]
    exact hC i hi hjold

end PoincareConjecture.BalancedNeckChain
