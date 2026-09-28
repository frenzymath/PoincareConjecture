import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardInterval
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardNonflatness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M30

noncomputable def ancientKappaIdentificationOfNoncollapsed
    (hC : RicciFlowCurvatureTheory.{u})
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed L kappa) :
    M30AncientKappaIdentification L kappa := by
  let C := L.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := L.connectedSpace
  have hsubset : Iic (0 : ℝ) ⊆ blowupBackwardInterval ⊤ := by
    rw [blowupBackwardInterval_top]
  have hne : (Iic (0 : ℝ)).Nontrivial :=
    ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    L.flow hsubset ordConnected_Iic hne
  have hcomplete (t : ℝ) (ht : t ≤ 0) : MetricComplete (F.metric t) :=
    L.complete t (hsubset ht)
  have hoperator (t : ℝ) (ht : t ≤ 0) (x : C.carrier) :
      (F.connection t).NonnegativeCurvatureOperator x :=
    L.nonnegative_curvature_operator t (hsubset ht) x
  have hbounded (a : ℝ) (_ha : a ≤ 0) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a 0, ∀ x : C.carrier,
        (F.connection t).curvatureTensorNorm x ≤ K := by
    obtain ⟨K, hK, hbound⟩ := L.curvature_locally_bounded_in_time
      (Icc a 0) isCompact_Icc (fun _ hs => hsubset hs.2)
    exact ⟨K, hK, fun t ht x => (le_abs_self _).trans (hbound t ht x)⟩
  have hterminal : ∃ p : C.carrier, 0 < (F.connection 0).scalarCurvature p := by
    refine ⟨L.base, ?_⟩
    change 0 < (L.flow.connection 0).scalarCurvature L.base
    rw [L.scalar_normalized]
    norm_num
  have hpositive := scalarCurvature_positive_somewhere_of_locally_bounded_ancient
    hC F hcomplete hoperator hbounded hterminal
  let A : AncientKappaSolution 3 C.carrier := {
    flow := F
    kappa := kappa
    kappa_pos := hkappa
    complete := hcomplete
    nonnegative_curvature_operator := hoperator
    bounded_curvature := by
      intro t ht
      obtain ⟨K, hK, hbound⟩ := L.curvature_locally_bounded_in_time
        {t} isCompact_singleton (singleton_subset_iff.mpr (hsubset ht))
      exact ⟨K, hK, fun x => hbound t (mem_singleton t) x⟩
    nonflat := by
      intro t ht
      obtain ⟨x, hx⟩ := hpositive t ht
      refine ⟨x, ?_⟩
      intro hzero
      have hnorm := (F.connection t).abs_scalarCurvature_le_curvatureTensorNorm x
      rw [hzero, mul_zero] at hnorm
      exact hx.not_ge ((le_abs_self _).trans hnorm)
    noncollapsed := by
      intro _ _ t ht p r hr _ hcurvature
      exact hnc t (hsubset ht) p r hr
        (fun _ hs => hsubset (hs.2.trans ht)) hcurvature }
  exact {
    certificate := {
      solution := A
      kappa_eq := rfl
      metric_eq := fun _ _ => rfl }
    domain_eq := blowupBackwardInterval_top
    connection_eq := fun _ _ => HEq.rfl }

end PoincareConjecture.M30
