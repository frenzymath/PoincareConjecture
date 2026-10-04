import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Ancient.LimitAncientDomain
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Ancient.LimitAncientFlat

/-!
# Actual ancient identification of the infinite-horizon limit

Forward flatness on a finite buffered slab and the normalized terminal
scalar give nonflatness at every ancient time. The identification retains
the exact metric and connection. Literal all-scale noncollapse remains an
internal upstream input, whose geometric transfer is not proved here.
Source: Morgan--Tian Proposition 17.1, pp. 407-408; reviewed derivation
`proof-work/tasks/M47/derivations/limit-ancient-identification.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.M47

/-- A flat earlier slice would remain flat through the normalized time-zero
basepoint. The curvature ceiling is chosen on that finite buffered slab. -/
theorem limitAncientFlow_nonflat
    (h04 : RicciFlowCurvatureTheory.{u})
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) :
    ∀ t : ℝ, t ≤ 0 → ∃ x : L.sliceCarrier.carrier,
      ((limitAncientFlow L).connection t).curvatureTensorNorm x ≠ 0 := by
  classical
  let : ConnectedSpace L.sliceCarrier.carrier := L.connectedSpace
  intro a ha
  by_contra hnot
  have hflat (x : L.sliceCarrier.carrier) :
      ((limitAncientFlow L).connection a).curvatureTensorNorm x = 0 :=
    Classical.not_not.mp (not_exists.mp hnot x)
  have hterminal : ((limitAncientFlow L).connection 0).curvatureTensorNorm L.base = 0 := by
    rcases lt_or_eq_of_le ha with ha | rfl
    · obtain ⟨K, hK, hbound⟩ := limitAncientFlow_compact_time_bound L (Icc (a - 1) 0)
        isCompact_Icc (fun _ ht => ht.2)
      exact limitAncient_forward_flat_on_buffered_slab h04 (limitAncientFlow L) L.base
        (limitAncientFlow_complete L) (limitAncientFlow_nonnegative_curvature_operator L)
        a K ha hK (fun t ht x => (le_abs_self _).trans (hbound t ht x)) hflat
        0 ⟨ha.le, le_rfl⟩ L.base
    · exact hflat L.base
  have hscalar := ((limitAncientFlow L).connection 0).abs_scalarCurvature_le_curvatureTensorNorm
    L.base
  rw [limitAncientFlow_scalar_normalized, hterminal, mul_zero] at hscalar
  norm_num at hscalar

/-- The ancient solution on the actual limit carrier, using the given
all-scale noncollapse producer and derived every-time nonflatness. -/
noncomputable def limitAncientSolution
    (h04 : RicciFlowCurvatureTheory.{u})
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (κ : ℝ) (hκ : 0 < κ)
    (hnc : BlowupLimitNoncollapsed L κ) :
    letI : ConnectedSpace L.sliceCarrier.carrier := L.connectedSpace
    AncientKappaSolution 3 L.sliceCarrier.carrier := by
  letI : ConnectedSpace L.sliceCarrier.carrier := L.connectedSpace
  exact
    { flow := limitAncientFlow L
      kappa := κ
      kappa_pos := hκ
      complete := limitAncientFlow_complete L
      nonnegative_curvature_operator := limitAncientFlow_nonnegative_curvature_operator L
      bounded_curvature := limitAncientFlow_bounded_curvature L
      nonflat := limitAncientFlow_nonflat h04 L
      noncollapsed := limitAncientFlow_noncollapsed L κ hnc }

/-- The infinite-horizon identification retains the literal metric AND
connection. Its only noncollapse input is the named internal limit
predicate; no ancient output from M30 or new entry premise is used. -/
noncomputable def limitAncientIdentification
    (h04 : RicciFlowCurvatureTheory.{u})
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (κ : ℝ) (hκ : 0 < κ)
    (hnc : BlowupLimitNoncollapsed L κ) : M30AncientKappaIdentification L κ where
  certificate :=
    { solution := limitAncientSolution h04 L κ hκ hnc
      kappa_eq := rfl
      metric_eq := fun _ _ => rfl }
  domain_eq := limitAncient_domain_eq
  connection_eq := fun _ _ => HEq.rfl

end PoincareMT.M47
