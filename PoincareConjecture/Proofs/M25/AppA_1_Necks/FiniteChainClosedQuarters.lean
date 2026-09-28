import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainExtension
import PoincareConjecture.Proofs.M25.AppA_1_Necks.ClosedFrontierQuarters

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_finite_forward_extension_closed_quarters :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b →
      epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        closure ((C.neck i).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
            (C.neck (i + 1)).carrier ∧
          closure ((C.neck (i + 1)).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆
            (C.neck i).carrier) →
      ∀ (N' : EpsilonNeck g),
      N' ∈ C.source_necks →
      N'.epsilon = epsilon →
      N'.center ∈ closure ((C.neck b).region 0 epsilon⁻¹) →
      N'.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) →
      ∃ (R : EpsilonNeck g) (D : BalancedNeckChain g epsilon),
        (R = N' ∨ R = N'.reverse) ∧
        R.SameUpToReversal N' ∧
        D.shape = ChainShape.finite a (b + 1) ∧
        D.source_necks = C.source_necks ∧
        D.neck = Function.update C.neck (b + 1) R ∧
        (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          closure ((D.neck i).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
              (D.neck (i + 1)).carrier ∧
            closure ((D.neck (i + 1)).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆
              (D.neck i).carrier) := by
  classical
  obtain ⟨epsilonF, hF, hFcap, hforward⟩ := exists_finite_forward_extension.{u}
  obtain ⟨epsilonP, hP, _, hpositive⟩ :=
    EpsilonNeck.exists_positive_frontier_closed_quarter_control.{u}
  obtain ⟨epsilonN, hN, _, hnegative⟩ :=
    EpsilonNeck.exists_positive_frontier_closed_negative_quarter_control.{u}
  refine ⟨min epsilonF (min epsilonP epsilonN), lt_min hF (lt_min hP hN),
    (min_le_left _ _).trans hFcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape he hsep hquarters
    N' hsource hepsilon hy hyout
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  obtain ⟨i0, hi0⟩ := C.active_nonempty
  have hab : a ≤ b := ((hactive i0).mp hi0).1.trans ((hactive i0).mp hi0).2
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have hlast : (C.neck b).epsilon = epsilon := C.epsilon_eq b hb
  have heP : epsilon ≤ epsilonP :=
    he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heN : epsilon ≤ epsilonN :=
    he.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨R, D, hchoice, hselected, hDshape, hDsource, hDneck⟩ :=
    hforward C hshape (he.trans (min_le_left _ _)) hsep N' hsource hepsilon hy hyout
  have hRc : R.center = N'.center := hselected.2.2.1
  have hRe : R.epsilon = (C.neck b).epsilon :=
    (hselected.1.trans hepsilon).trans hlast.symm
  have hDnew : D.neck (b + 1) = R := by rw [hDneck, Function.update_self]
  have hDold {i : ℤ} (hi : i ∈ C.shape.active) : D.neck i = C.neck i := by
    have hile : i ≤ b := ((hactive i).mp hi).2
    have hine : i ≠ b + 1 := by omega
    rw [hDneck, Function.update_of_ne hine]
  have hDb : b ∈ D.shape.active := by
    rw [hDshape]
    change a ≤ b ∧ b ≤ b + 1
    exact ⟨hab, by omega⟩
  have hDb1 : b + 1 ∈ D.shape.active := by
    rw [hDshape]
    change a ≤ b + 1 ∧ b + 1 ≤ b + 1
    exact ⟨by omega, le_rfl⟩
  have hyR : R.center ∈ closure ((C.neck b).region 0 (C.neck b).epsilon⁻¹) := by
    simpa only [hRc, hlast] using hy
  have hyRout : R.center ∉ (C.neck b).carrier := by
    rw [hRc]
    intro hx
    exact hyout (mem_iUnion₂.mpr ⟨b, hb, hx⟩)
  have hopenQuarter := (D.overlap_contains_quarters b hDb hDb1).2
  rw [hDnew, hDold hb] at hopenQuarter
  have hclosedPositive := hpositive (C.neck b) R (by rw [hlast]; exact heP)
    hRe hyR hyRout
  have hclosedNegative := hnegative (C.neck b) R (by rw [hlast]; exact heN)
    hRe (hsep b hb) hyR hyRout (by simpa only [hlast] using hopenQuarter)
  refine ⟨R, D, hchoice, hselected, hDshape, hDsource, hDneck, ?_⟩
  intro i hi hi1
  rw [hDshape] at hi hi1
  change i ∈ Icc a (b + 1) at hi
  change i + 1 ∈ Icc a (b + 1) at hi1
  by_cases hib : i = b
  · subst i
    rw [hDold hb, hDnew]
    simpa only [hlast] using And.intro hclosedPositive hclosedNegative
  · rcases hi with ⟨hia, hibound⟩
    rcases hi1 with ⟨hi1a, hi1b⟩
    have hio : i ∈ C.shape.active := (hactive i).mpr ⟨hia, by omega⟩
    have hi1o : i + 1 ∈ C.shape.active := (hactive _).mpr ⟨hi1a, by omega⟩
    rw [hDold hio, hDold hi1o]
    exact hquarters i hio hi1o

end PoincareConjecture.BalancedNeckChain
