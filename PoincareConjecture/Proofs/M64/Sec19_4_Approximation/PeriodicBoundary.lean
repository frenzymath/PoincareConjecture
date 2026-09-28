import PoincareConjecture.Definitions.M64Approximation
import PoincareConjecture.Proofs.M58.Sec18_4_LoopLength

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]

theorem exists_continuous_loopCircle_map_of_periodic
    (f : ℝ → M) (hcont : Continuous f)
    (hperiod : Function.Periodic f curvePeriod) :
    ∃ b : ContinuousMap LoopCircle M, ∀ x : ℝ,
      b (m64LoopCircleParam x) = f x := by
  let I : Set ℝ := Set.Icc 0 curvePeriod
  have hqI0 : Continuous (fun t : I =>
      (⟨m64LoopCircleParam t.1, (m64LoopCircleParam t.1).property⟩ : LoopCircle)) := by
    change Continuous (fun t : I =>
      (⟨Proofs.M58.angularPoint t.1, Proofs.M58.norm_angularPoint t.1⟩ : LoopCircle))
    exact (Proofs.M58.contDiff_angularPoint.continuous.comp
      continuous_subtype_val).subtype_mk _
  let qI : ContinuousMap I LoopCircle :=
    ⟨fun t => ⟨m64LoopCircleParam t.1, (m64LoopCircleParam t.1).property⟩, hqI0⟩
  have hqIsurj : Function.Surjective qI := by
    intro z
    obtain ⟨t, ht, htz⟩ := Proofs.M58.exists_angularPoint z
    refine ⟨⟨t, ht⟩, ?_⟩
    exact Subtype.ext htz
  have hproper : IsProperMap qI := qI.continuous.isProperMap
  have hquot : Topology.IsQuotientMap qI :=
    hproper.isClosedMap.isQuotientMap hproper.continuous hqIsurj
  let fI : ContinuousMap I M :=
    ⟨fun t => f t.1, hcont.comp continuous_subtype_val⟩
  have hfactor : Function.FactorsThrough fI qI := by
    intro s t hst
    have hcoord : m64LoopCircleParam s.1 = m64LoopCircleParam t.1 := by
      exact Subtype.ext (congrArg Subtype.val hst)
    have hang : (s.1 : Real.Angle) = (t.1 : Real.Angle) := by
      apply Real.Angle.cos_sin_inj
      · exact congrArg (fun z : LoopCircle => z.1 0) hcoord
      · exact congrArg (fun z : LoopCircle => z.1 1) hcoord
    exact congrArg hperiod.lift hang
  let b : ContinuousMap LoopCircle M := hquot.lift fI hfactor
  refine ⟨b, ?_⟩
  intro x
  obtain ⟨t, ht, htx⟩ := Proofs.M58.exists_angularPoint (m64LoopCircleParam x)
  have hq : qI ⟨t, ht⟩ = m64LoopCircleParam x := by
    exact Subtype.ext htx
  have hdesc : b (qI ⟨t, ht⟩) = f t := by
    change b (qI ⟨t, ht⟩) = fI ⟨t, ht⟩
    simpa only [ContinuousMap.comp_apply] using
      congrArg (fun c : ContinuousMap I M => c ⟨t, ht⟩)
        (hquot.lift_comp fI hfactor)
  rw [← hq, hdesc]
  have hcoord : m64LoopCircleParam t = m64LoopCircleParam x := by
    exact Subtype.ext htx
  have hang : (t : Real.Angle) = (x : Real.Angle) := by
    apply Real.Angle.cos_sin_inj
    · exact congrArg (fun z : LoopCircle => z.1 0) hcoord
    · exact congrArg (fun z : LoopCircle => z.1 1) hcoord
  exact congrArg hperiod.lift hang

theorem exists_polygon_boundary
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}
    (polygon : M63GeodesicPolygon g D N) :
    Nonempty (M64PolygonBoundary polygon) := by
  obtain ⟨b, hb⟩ := exists_continuous_loopCircle_map_of_periodic
    polygon.map polygon.continuous polygon.periodic
  exact ⟨⟨b, hb⟩⟩

end PoincareConjecture
