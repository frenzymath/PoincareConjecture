import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem GeneralizedRicciFlowData.continuous_scalar (G : GeneralizedRicciFlowData.{u}) :
    Continuous G.scalar := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  obtain ⟨b, hb, y, rfl⟩ := G.box_covers t x
  let f : (G.box b).interval × (G.box b).carrier.carrier → G.point :=
    fun p => ⟨p.1.val, (G.box b).forward p.1.val p.1.property p.2⟩
  have heq : G.scalar ∘ f = fun p : (G.box b).interval × (G.box b).carrier.carrier =>
      ((G.box b).flow.connection p.1.val).scalarCurvature p.2 := by
    funext p
    exact (G.box_scalar b p.1.val p.1.property p.2).symm
  have hc : Continuous (G.scalar ∘ f) := by
    rw [heq]
    have hj : ContinuousOn (fun p : ℝ × (G.box b).carrier.carrier =>
        ((G.box b).flow.connection p.1).scalarCurvature p.2)
        ((G.box b).interval ×ˢ univ) :=
      (G.box b).flow.contMDiffOn_scalarCurvature.continuousOn
    exact hj.comp_continuous
      (f := fun p : (G.box b).interval × (G.box b).carrier.carrier => (p.1.val, p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.property, mem_univ _⟩)
  exact (G.box_openEmbedding b).isEmbedding.isInducing.continuousAt_iff'
    ((G.box_openEmbedding b).isOpen_range.mem_nhds ⟨(⟨t, hb⟩, y), rfl⟩) |>.mp
      hc.continuousAt

namespace SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  (Q : SingularLimitConclusion H)

theorem continuous_gluing_scalar :
    Continuous (Q.extension.extended.scalar ∘ Q.gluing_map) :=
  Q.extension.extended.continuous_scalar.comp Q.gluing_openEmbedding.continuous

theorem gluing_scalar_old (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) (hlt : t < T)
    (z : (Q.extension.extended.slice T).carrier) :
    Q.extension.extended.scalar (Q.gluing_map (⟨t, ht⟩, z)) =
      H.reference.scalar t (Q.terminal_source z) := by
  rw [Q.gluing_old t ht hlt z,
    Q.extension.spacetime_slices t (H.reference.window_subset ⟨ht.1.le, hlt⟩)]
  exact (Q.extension.scalar_pullback t (H.reference.window_subset ⟨ht.1.le, hlt⟩) _).trans
    (H.reference.scalar_pullback t ⟨ht.1.le, hlt⟩ _)

theorem gluing_scalar_terminal (z : (Q.extension.extended.slice T).carrier) :
    Q.extension.extended.scalar
      (Q.gluing_map (⟨T, H.reference.tMinus_lt, le_rfl⟩, z)) = Q.terminal_scalar z := by
  rw [Q.gluing_terminal, Q.terminal_scalar_eq]
  rfl

theorem exists_strict_scalar_tail (z : (Q.extension.extended.slice T).carrier)
    (a : ℝ) (ha : a < Q.terminal_scalar z) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, a < H.reference.scalar t (Q.terminal_source z) := by
  let f : Ioc H.reference.tMinus T → ℝ := fun t =>
    Q.extension.extended.scalar (Q.gluing_map (t, z))
  have hf : Continuous f := Q.continuous_gluing_scalar.comp
    (continuous_id.prodMk continuous_const)
  have hTa : a < f ⟨T, H.reference.tMinus_lt, le_rfl⟩ := by
    simpa only [f, Q.gluing_scalar_terminal] using ha
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_Ioi.preimage hf)
    ⟨T, H.reference.tMinus_lt, le_rfl⟩ hTa
  obtain ⟨s, hs, hsT⟩ := exists_between
    (max_lt H.reference.tMinus_lt (sub_lt_self T hδ))
  have hsref := (le_max_left H.reference.tMinus (T - δ)).trans_lt hs
  refine ⟨s, hsref, hsT, ?_⟩
  intro t ht
  have htref : H.reference.tMinus < t := hsref.trans_le ht.1
  have hdist : dist (⟨t, htref, ht.2.le⟩ : Ioc H.reference.tMinus T)
      ⟨T, H.reference.tMinus_lt, le_rfl⟩ < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
    have := (le_max_right H.reference.tMinus (T - δ)).trans_lt hs
    linarith [ht.1]
  have h := hball (show (⟨t, htref, ht.2.le⟩ : Ioc H.reference.tMinus T) ∈
    Metric.ball ⟨T, H.reference.tMinus_lt, le_rfl⟩ δ from hdist)
  change a < Q.extension.extended.scalar
    (Q.gluing_map (⟨t, htref, ht.2.le⟩, z)) at h
  rwa [Q.gluing_scalar_old t ⟨htref, ht.2.le⟩ ht.2 z] at h

end SingularLimitConclusion
end PoincareConjecture
