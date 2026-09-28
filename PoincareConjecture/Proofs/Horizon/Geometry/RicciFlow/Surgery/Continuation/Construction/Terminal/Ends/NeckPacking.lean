import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CanonicalCover
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InteriorThickness
import Mathlib.Topology.EMetricSpace.Basic









noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem finite_of_disjoint_of_scale_lower_bound {ι : Type*}
    (N : ι → EpsilonNeck g) {K : Set M} (hK : IsCompact K)
    (hcenter : ∀ i, (N i).center ∈ K)
    {s : ℝ} (hs : 0 < s) (hscale : ∀ i, s ≤ (N i).scale)
    (hdisjoint : Pairwise fun i j => Disjoint (N i).carrier (N j).carrier) :
    Finite ι := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hsep {i j : ι} (hij : i ≠ j) :
      ENNReal.ofReal (s / 4) ≤ edist (N i).center (N j).center := by
    have hNi := (N i).mem_central_sphere_iff (N i).center |>.mp
      (N i).center_on_central_sphere
    have hNj := (N j).central_sphere_subset (N j).center_on_central_sphere
    have hinv : 1 ≤ (N i).epsilon⁻¹ := by
      apply (one_le_inv₀ (N i).epsilon_pos).mpr
      linarith [(N i).epsilon_lt_half]
    have hmid : (N i).center ∈
        (N i).region (-(N i).epsilon⁻¹ / 2) ((N i).epsilon⁻¹ / 2) := by
      refine ⟨hNi.1, ?_, ?_⟩ <;> rw [hNi.2] <;> linarith
    have hout : (N j).center ∉ (N i).carrier :=
      fun hi => disjoint_left.mp (hdisjoint hij) hi hNj
    apply (ENNReal.ofReal_le_ofReal ?_).trans
      ((N i).quarter_width_le_edist_of_mem_middle_half hmid hout)
    have hmul := mul_le_mul_of_nonneg_left hinv (N i).scale_pos.le
    linarith [hscale i]
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover
    (fun p : M => Metric.eball p (ENNReal.ofReal (s / 8)))
    (fun _ => Metric.isOpen_eball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, by simp [Metric.mem_eball, hs]⟩)
  have hfinite (p : M) :
      {i : ι | (N i).center ∈ Metric.eball p (ENNReal.ofReal (s / 8))}.Finite := by
    apply Set.Subsingleton.finite
    intro i hi j hj
    by_contra hij
    have hlt : edist (N i).center (N j).center < ENNReal.ofReal (s / 4) := by
      calc
        edist (N i).center (N j).center ≤
            edist (N i).center p + edist p (N j).center := edist_triangle _ _ _
        _ < ENNReal.ofReal (s / 8) + ENNReal.ofReal (s / 8) :=
          ENNReal.add_lt_add hi (by simpa only [mem_ofPred_eq, Metric.mem_eball,
            edist_comm] using hj)
        _ = ENNReal.ofReal (s / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
    exact (not_lt_of_ge (hsep hij)) hlt
  apply Set.finite_univ_iff.mp
  apply (S.finite_toSet.biUnion fun p _ => hfinite p).subset
  intro i hi
  obtain ⟨p, hp, hc⟩ := mem_iUnion₂.mp (hS (hcenter i))
  exact mem_iUnion₂.mpr ⟨p, hp, hc⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}



theorem finite_disjoint_necks_at_scalar_level (Q : SingularLimitConclusion H)
    {ι : Type*} {epsilon q : ℝ} (hε : epsilon < 1 / 2) (hq : 0 < q)
    (N : ι → TerminalStrongNeck Q.extension epsilon)
    (hlevel : ∀ i, Q.terminal_scalar (N i).center = q)
    (hdisjoint : Pairwise fun i j => Disjoint (N i).carrier (N j).carrier) :
    Finite ι := by
  refine EpsilonNeck.finite_of_disjoint_of_scale_lower_bound
    (fun i => (N i).spatialNeck hε) (Q.isCompact_scalar_sublevel q)
    ?_ (Real.rpow_pos_of_pos hq (-1 / 2 : ℝ)) ?_ hdisjoint
  · intro i
    change (Q.extension.extended.connection T).scalarCurvature (N i).center ≤ q
    rw [← Q.terminal_scalar_eq, hlevel i]
  · intro i
    change q ^ (-1 / 2 : ℝ) ≤ (N i).scale
    rw [(N i).scale_scalar, ← Q.terminal_scalar_eq, hlevel i]

end PoincareConjecture.SingularLimitConclusion
