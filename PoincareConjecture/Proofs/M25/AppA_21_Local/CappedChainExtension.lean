import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainClosedQuarters
import PoincareConjecture.Proofs.M25.AppA_1_Necks.PositiveFrontierSeparation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem CapCertificate.exists_finite_outward_extension :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C : CapCertificate g) (D : BalancedNeckChain g C.epsilon) {a b : ℤ},
      D.shape = ChainShape.finite a b →
      C.epsilon ≤ epsilon0 →
      D.neck a = C.end_neck →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      (∀ i ∈ D.shape.active, a < i → (D.neck i).center ∉ C.carrier) →
      (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
        closure ((D.neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
            (D.neck (i + 1)).carrier ∧
          closure ((D.neck (i + 1)).region
              (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) →
      ∀ (N : EpsilonNeck g),
      N ∈ D.source_necks →
      N.epsilon = C.epsilon →
      N.center ∈ closure ((D.neck b).region 0 C.epsilon⁻¹) →
      N.center ∉ C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) →
      ∃ (R : EpsilonNeck g) (E : BalancedNeckChain g C.epsilon),
        (R = N ∨ R = N.reverse) ∧
        R.SameUpToReversal N ∧
        E.shape = ChainShape.finite a (b + 1) ∧
        E.source_necks = D.source_necks ∧
        E.neck = Function.update D.neck (b + 1) R ∧
        E.neck a = C.end_neck ∧
        (∀ i ∈ E.shape.active, (E.neck i).IsSeparating) ∧
        (∀ i ∈ E.shape.active, a < i → (E.neck i).center ∉ C.carrier) ∧
        (∀ i ∈ E.shape.active, i + 1 ∈ E.shape.active →
          closure ((E.neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
              (E.neck (i + 1)).carrier ∧
            closure ((E.neck (i + 1)).region
                (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ (E.neck i).carrier) := by
  classical
  obtain ⟨epsilonF, hF, hFcap, hforward⟩ :=
    BalancedNeckChain.exists_finite_forward_extension_closed_quarters.{u}
  obtain ⟨epsilonS, hS, _, hseparation⟩ :=
    EpsilonNeck.exists_positive_frontier_separation.{u}
  refine ⟨min epsilonF epsilonS, lt_min hF hS,
    (min_le_left _ _).trans hFcap, ?_⟩
  intro M _ _ _ _ _ _ g C D a b hshape he hstart hsep hout hquarters
    N hsource hepsilon hy hyout
  have hactive (i : ℤ) : i ∈ D.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  obtain ⟨i0, hi0⟩ := D.active_nonempty
  have hab : a ≤ b := ((hactive i0).mp hi0).1.trans ((hactive i0).mp hi0).2
  have ha : a ∈ D.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ D.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have hyUnion : N.center ∉ (⋃ i ∈ D.shape.active, (D.neck i).carrier) :=
    fun hx => hyout (Or.inr hx)
  have hyCap : N.center ∉ C.carrier := fun hx => hyout (Or.inl hx)
  have hyLast : N.center ∉ (D.neck b).carrier :=
    fun hx => hyUnion (mem_iUnion₂.mpr ⟨b, hb, hx⟩)
  have hlast : (D.neck b).epsilon = C.epsilon := D.epsilon_eq b hb
  have hNsep : N.IsSeparating :=
    hseparation (D.neck b) N
      (by rw [hlast]; exact he.trans (min_le_right _ _))
      (hepsilon.trans hlast.symm) (hsep b hb)
      (by simpa only [hlast] using hy) hyLast
  obtain ⟨R, E, hchoice, hselected, hEshape, hEsource, hEneck, hEquarters⟩ :=
    hforward D hshape (he.trans (min_le_left _ _)) hsep hquarters
      N hsource hepsilon hy hyUnion
  have hRc : R.center = N.center := hselected.2.2.1
  have hRs : R.central_sphere = N.central_sphere := hselected.2.2.2.2.1
  have hRsep : R.IsSeparating := by
    simpa only [EpsilonNeck.IsSeparating, hRc, hRs] using hNsep
  have hEnew : E.neck (b + 1) = R := by
    rw [hEneck, Function.update_self]
  have hEold {i : ℤ} (hi : i ∈ D.shape.active) : E.neck i = D.neck i := by
    have hib : i ≤ b := ((hactive i).mp hi).2
    have hine : i ≠ b + 1 := by omega
    rw [hEneck, Function.update_of_ne hine]
  have hEactive (i : ℤ) : i ∈ E.shape.active ↔ i ∈ Icc a (b + 1) := by
    rw [hEshape]
    rfl
  refine ⟨R, E, hchoice, hselected, hEshape, hEsource, hEneck,
    (hEold ha).trans hstart, ?_, ?_, hEquarters⟩
  · intro i hi
    by_cases hinew : i = b + 1
    · rw [hinew, hEnew]
      exact hRsep
    · rcases (hEactive i).mp hi with ⟨hia, hib⟩
      have hio : i ∈ D.shape.active := (hactive i).mpr ⟨hia, by omega⟩
      rw [hEold hio]
      exact hsep i hio
  · intro i hi hai
    by_cases hinew : i = b + 1
    · rw [hinew, hEnew, hRc]
      exact hyCap
    · rcases (hEactive i).mp hi with ⟨hia, hib⟩
      have hio : i ∈ D.shape.active := (hactive i).mpr ⟨hia, by omega⟩
      rw [hEold hio]
      exact hout i hio hai

end PoincareConjecture
