import PoincareConjecture.Proofs.M34.Thm12_5_Existence.BoundedContinuation
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapChapter11Geometry
import PoincareConjecture.Proofs.M34.Standard.NonnegativeCurvatureNorm












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R

include P



theorem standardFlow_chapter11_compact_center_sequence (E0 : StandardCapEstimate g0)
    {T0 B : ℝ} (hT0 : T0 ∈ Ioo 0 F.base.lifetime) {X : Set StandardCapSpace}
    (hcurv : ∀ t ∈ Ico T0 F.base.lifetime, ∀ x ∉ X,
      (F.connection t).curvatureTensorNorm x ≤ 2 * B) (Rstar : ℝ) :
    ∃ p : ℕ → (G).point,
      (∀ k : ℕ, T0 < (p k).1 ∧ ordinaryChapter11Projection R (p k) ∈ X ∧
        Rstar < (G).scalar (p k) ∧ (k : ℝ) + 1 < (G).scalar (p k)) ∧
      Tendsto (fun k => (G).scalar (p k)) atTop atTop := by
  classical
  have hchoose (k : ℕ) : ∃ p : (G).point,
      T0 < p.1 ∧ ordinaryChapter11Projection R p ∈ X ∧
        Rstar < (G).scalar p ∧ (k : ℝ) + 1 < (G).scalar p := by
    obtain ⟨t, ht, x, hhigh⟩ := maximalFlow_curvature_unbounded_near_lifetime P E0 F
      ⟨hT0.1.le, hT0.2⟩ (max (2 * B) (max Rstar ((k : ℝ) + 1)))
    have htime : t ∈ Ico 0 F.base.lifetime := ⟨hT0.1.le.trans ht.1.le, ht.2⟩
    have hx : x ∈ X := by
      by_contra hx
      exact (not_lt_of_ge ((hcurv t ⟨ht.1.le, ht.2⟩ x hx).trans
        (le_max_left _ _))) hhigh
    have hnorm := (F.base.flow.connection t).curvatureTensorNorm_le_scalar_of_nonnegative_sectional
      x (partialFlow_nonnegativeSectionalCurvature P.curvature E0 F.base t htime x)
    let p : (G).point := ⟨t, R.product.sliceIdentification ⟨t, htime⟩ x⟩
    have hproj : ordinaryChapter11Projection R p = x :=
      ordinaryChapter11Projection_identification (I := partialFlowSpacetimeInterval F.base)
        (F := F.base.flow) R ⟨t, htime⟩ x
    have hscalar : (G).scalar p = (F.connection t).scalarCurvature x := by
      have he := ordinaryChapter11_scalar_eq (I := partialFlowSpacetimeInterval F.base)
        (F := F.base.flow) R (partialFlow_chapter11_calculus F.base P R) p
      simpa only [hproj, p, MaximalStandardCapFlow.connection] using he
    refine ⟨p, ht.1, hproj ▸ hx, ?_, ?_⟩
    · rw [hscalar]
      exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hhigh.trans_le hnorm)
    · rw [hscalar]
      exact ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hhigh.trans_le hnorm)
  choose p hp using hchoose
  refine ⟨p, hp, ?_⟩
  apply tendsto_atTop_mono (g := fun k : ℕ => (G).scalar (p k))
    (f := fun k : ℕ => (k : ℝ)) _ tendsto_natCast_atTop_atTop
  intro k
  linarith [(hp k).2.2.2]

end PoincareConjecture.M34
