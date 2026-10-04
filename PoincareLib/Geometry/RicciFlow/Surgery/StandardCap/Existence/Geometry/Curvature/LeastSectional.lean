import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.SectionalModelParameters
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.SectionalNormLower
import Mathlib.Topology.Order.Compact

/-!
# A continuous least sectional value in fixed model coordinates

The compact fixed Euclidean plane parameters avoid choosing moving
orthonormal frames. Their quotient infimum is a continuous real function
along the flow, without any asserted differentiability of that infimum.
This is the propagation parameter in Lemma 12.6, pp. 297-298.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

open M04

/-- There is a model orthonormal two-plane in dimension three
(Lemma 12.6, pp. 297-298). -/
theorem modelOrthonormalPairs_three_nonempty : (modelOrthonormalPairs 3).Nonempty := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  refine ⟨(b 0, b 1), b.orthonormal.norm_eq_one 0, b.orthonormal.norm_eq_one 1, ?_⟩
  rw [b.inner_eq_ite]
  norm_num

/-- Least actual sectional quotient over the fixed compact plane
parameters (Lemma 12.6, pp. 297-298). -/
noncomputable def modelLeastSectional
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  sInf (range (fun p : modelOrthonormalPairs 3 =>
    D.curvatureTensor x p.1.1 p.1.2 p.1.1 p.1.2 / metricGram g x p.1.1 p.1.2))

/-- Every common lower bound for the model planes bounds their infimum
(Lemma 12.6, pp. 297-298). -/
theorem le_modelLeastSectional
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin 3)) {c : ℝ}
    (h : ∀ p ∈ modelOrthonormalPairs 3,
      c ≤ D.curvatureTensor x p.1 p.2 p.1 p.2 / metricGram g x p.1 p.2) :
    c ≤ modelLeastSectional D x := by
  obtain ⟨p, hp⟩ := modelOrthonormalPairs_three_nonempty
  unfold modelLeastSectional
  apply le_csInf
  · exact ⟨_, ⟨⟨p, hp⟩, rfl⟩⟩
  · rintro y ⟨q, rfl⟩
    exact h q.1 q.2

/-- The infimum lies below each actual plane quotient; the full tensor
norm supplies the required lower boundedness (Lemma 12.6, pp. 297-298). -/
theorem modelLeastSectional_le
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin 3))
    (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ modelOrthonormalPairs 3) :
    modelLeastSectional D x ≤ D.curvatureTensor x p.1 p.2 p.1 p.2 / metricGram g x p.1 p.2 := by
  unfold modelLeastSectional
  apply csInf_le
  · refine ⟨-D.curvatureTensorNorm x, ?_⟩
    rintro y ⟨q, rfl⟩
    exact neg_curvatureTensorNorm_le_sectionalRayleigh D x q.1.1 q.1.2
      (metricGram_pos_of_linearIndependent g x q.1.1 q.1.2
        (modelOrthonormalPairs_linearIndependent q.2))
  · exact ⟨⟨p, hp⟩, rfl⟩

set_option maxHeartbeats 800000 in
-- Kernel checking identifies the model and canonical tangent instances.
/-- Joint continuity of the least sectional value on the actual time
domain subtype (Lemma 12.6, pp. 297-298). -/
theorem continuous_modelLeastSectional_flow {J : Set ℝ}
    (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) J) :
    Continuous (fun z : J × EuclideanSpace ℝ (Fin 3) =>
      modelLeastSectional (F.connection z.1.1) z.2) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let P := modelOrthonormalPairs 3
  let : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_modelOrthonormalPairs 3)
  let f := fun (z : J × E) (p : P) =>
    (F.connection z.1.1).curvatureTensor z.2 p.1.1 p.1.2 p.1.1 p.1.2 /
      metricGram (F.metric z.1.1) z.2 p.1.1 p.1.2
  have hc : Continuous (Function.uncurry f) := by
    apply continuousOn_univ.mp
    exact (continuousOn_flow_sectionalRayleigh_model F).comp
      (((continuous_subtype_val.comp continuous_fst.fst).prodMk
        (continuous_fst.snd.prodMk
          (continuous_subtype_val.comp continuous_snd))).continuousOn)
      (fun z _ => ⟨z.1.1.2, mem_univ _, z.2.2⟩)
  simpa only [image_univ, modelLeastSectional] using
    (isCompact_univ (X := P)).continuous_sInf hc

set_option maxHeartbeats 800000 in
-- The restriction retains the canonical tangent/model instance conversion.
/-- Every included spatial slice of the least sectional value is
continuous (Lemma 12.6, pp. 297-298). -/
theorem continuous_modelLeastSectional_slice {J : Set ℝ}
    (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) J) {t : ℝ} (ht : t ∈ J) :
    Continuous (modelLeastSectional (F.connection t)) := by
  have h := (continuous_modelLeastSectional_flow F).comp
    (continuous_const.prodMk continuous_id : Continuous
      (fun x : EuclideanSpace ℝ (Fin 3) => ((⟨t, ht⟩ : J), x)))
  convert! h using 1

end PoincareMT.M34
