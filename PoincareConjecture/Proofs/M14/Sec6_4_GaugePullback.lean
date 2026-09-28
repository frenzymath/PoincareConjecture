import PoincareConjecture.Proofs.M14.Sec6_4_GaugeFieldRegularity
import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetConnection
import PoincareConjecture.Proofs.M14.Mathlib.VectorGraphDerivative
import PoincareConjecture.Definitions.M14PathCalculus
import PoincareConjecture.Statements.M12MovingGaugeTheory

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Bundle Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : SmoothSpacetimeInterval K} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
  (e : MovingSpacetimeGauge G.spacetime T U) (g : MovingSpacetimeGaugeGeometry e)
  {b : ℝ → T.Point × U} {J : Set ℝ}
  {Y : ∀ r, G.Horizontal (e.toSpacetime (b r))}

theorem pullbackExtension_gauge_coordinates_contMDiffAt
    (E : M14PullbackExtension G (fun r => e.toSpacetime (b r)) J Y)
    {s : ℝ} (hs : s ∈ J) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (𝓡 n) ∞
      (fun z : ℝ × (T.Point × U) =>
        (show EuclideanSpace ℝ (Fin n) from
          pullbackHorizontalSection g (E.extension z.1) z.2.1 z.2.2)) (s, b s) := by
  obtain ⟨O, hO, hgraph, hE⟩ := E.joint_smooth
  have hfield := (hE _ (hgraph s hs)).contMDiffAt (hO.mem_nhds (hgraph s hs))
  have hmap : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) ∞
      (fun z : ℝ × (T.Point × U) => (z.1, e.toSpacetime z.2)) (s, b s) :=
    contMDiffAt_fst.prodMk ((e.smooth (b s)).comp (s, b s) contMDiffAt_snd)
  have hpull := movingGauge_horizontalField_pullback_contMDiffWithinAt e g
    (b := fun z : ℝ × (T.Point × U) => z.2)
    (Y := fun z => E.extension z.1 (e.toSpacetime z.2))
    (S := univ) contMDiffWithinAt_snd
    (hfield.comp (s, b s) hmap).contMDiffWithinAt
  exact (U.tangentBundle_snd_contMDiff.contMDiffAt.comp_contMDiffWithinAt
    (s, b s) hpull).contMDiffAt univ_mem

theorem horizontalCovariantDerivative_gauge_coordinates
    {c : MetricLeviCivitaFamily g.metric} (H : MovingGaugeCalculus G.leafwise g c)
    (hzero : ∀ t x, movingGaugeDrift g t x = 0)
    (E : M14PullbackExtension G (fun r => e.toSpacetime (b r)) J Y)
    {s : ℝ} (hs : s ∈ J) (hJ : UniqueDiffWithinAt ℝ J s)
    (hb : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) b J s) :
    (show EuclideanSpace ℝ (Fin n) from
      (g.spatialTangentEquiv (b s).1 (b s).2).symm
        (M14HorizontalCovariantDerivative G (fun r => e.toSpacetime (b r)) J Y E s)) =
      derivWithin (fun r => (show EuclideanSpace ℝ (Fin n) from
        (g.spatialTangentEquiv (b r).1 (b r).2).symm (Y r))) J s +
      (show EuclideanSpace ℝ (Fin n) from
        (c (b s).1.val).connection
          (fun _ : U => (show EuclideanSpace ℝ (Fin n) from
            (g.spatialTangentEquiv (b s).1 (b s).2).symm (Y s))) (b s).2
          (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) b J s (1 : ℝ)).2) := by
  let f : ℝ × (T.Point × U) → EuclideanSpace ℝ (Fin n) := fun z =>
    pullbackHorizontalSection g (E.extension z.1) z.2.1 z.2.2
  let v := mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) b J s (1 : ℝ)
  let a := T.inclusionDerivative (b s).1 v.1
  have hvt : v.1 = a • T.positiveTangent (b s).1 := by
    apply (T.inclusionDerivative (b s).1).injective
    simp only [a, map_smul, SmoothSpacetimeInterval.positiveTangent,
      ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hf := pullbackExtension_gauge_coordinates_contMDiffAt e g E hs
  have hgraph := vector_graph_hasDerivWithinAt f (hf.mdifferentiableAt (by simp)) hb hJ
  have hagrees := hgraph.congr_of_mem
    (f₁ := fun r => (show EuclideanSpace ℝ (Fin n) from
      (g.spatialTangentEquiv (b r).1 (b r).2).symm (Y r)))
    (fun r hr => by
      dsimp only [f, pullbackHorizontalSection]
      rw [E.agrees r hr]) hs
  have hderiv := hagrees.derivWithin hJ
  have hsp : MDifferentiableAt (spacetimeModel n) (𝓡 n)
      (fun q : T.Point × U => f (s, q)) (b s) :=
    (hf.comp (b s) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hpart : mvfderiv (spacetimeModel n) (fun q => f (s, q)) (b s) v =
      a • (show EuclideanSpace ℝ (Fin n) from
        movingGaugeSectionTimeDerivative g (E.extension s) (b s).1 (b s).2) +
      mvfderiv (𝓡 n) (fun x : U => f (s, ((b s).1, x))) (b s).2 v.2 := by
    rw [movingGaugeSectionTimeDerivative_eq_model e g (E.extension s) E.domain
      E.domain_open (E.spatial_smooth s) (b s).1 (b s).2 (E.graph_mem s hs)]
    change mfderiv (spacetimeModel n) (𝓡 n) (fun q => f (s, q)) (b s) (v.1, v.2) = _
    rw [mfderiv_prod_eq_add_apply hsp, hvt, map_smul]
    rfl
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal (e.toSpacetime (b s))) :=
    (metric.toCore (e.toSpacetime (b s))).toNormedAddCommGroupOfTopology
      (metric.continuousAt (e.toSpacetime (b s)))
      (metric.isVonNBounded (e.toSpacetime (b s)))
  let : InnerProductSpace ℝ (G.Horizontal (e.toSpacetime (b s))) :=
    .ofCoreOfTopology (metric.toCore (e.toSpacetime (b s)))
      (metric.continuousAt (e.toSpacetime (b s)))
      (metric.isVonNBounded (e.toSpacetime (b s)))
  obtain ⟨d, hd⟩ := E.parameter_derivative s hs
  let L : G.Horizontal (e.toSpacetime (b s)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (g.spatialTangentEquiv (b s).1 (b s).2).symm.toContinuousLinearMap
  have hparam := L.hasFDerivAt.comp_hasDerivAt s hd.differentiableAt.hasDerivAt
  have hparamEq : deriv (fun r => f (r, b s)) s =
      (g.spatialTangentEquiv (b s).1 (b s).2).symm
        (deriv (fun r => E.extension r (e.toSpacetime (b s))) s) := hparam.deriv
  have hvel := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp_mfderivWithin s ((e.smooth (b s)).mdifferentiableAt (by simp))
      hb hJ.uniqueMDiffWithinAt)
  dsimp only [Function.comp_def, ContinuousLinearMap.comp_apply] at hvel
  have hconn := H.horizontal_derivative_eq (E.extension s) E.domain E.domain_open
    (E.spatial_smooth s) (b s).1 (b s).2 (E.graph_mem s hs) a v.2
  have hW : movingGaugeDrift g (b s).1 = 0 := funext (hzero (b s).1)
  rw [hW, CovariantDerivative.zero, Pi.zero_apply, zero_apply, smul_zero, sub_zero] at hconn
  have hfield := movingGauge_pullbackHorizontalSection_smoothAt e g
    (E.extension s) E.domain E.domain_open (E.spatial_smooth s) (b s) (E.graph_mem s hs)
  have hspaceField := (hfield.comp (b s).2
    (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hspace := U.covariantDerivative_eq_derivative_add_constant
    (c (b s).1.val).connection.isCovariantDerivativeOn hspaceField v.2
  dsimp only [Function.comp_def, Prod.fst, Prod.snd, id_eq] at hspace
  have hfieldValue : pullbackHorizontalSection g (E.extension s) (b s).1 (b s).2 =
      (g.spatialTangentEquiv (b s).1 (b s).2).symm (Y s) := by
    unfold pullbackHorizontalSection
    exact congrArg _ (E.agrees s hs)
  rw [hfieldValue] at hspace
  dsimp only [Prod.fst, Prod.snd] at hderiv
  rw [hparamEq, hpart] at hderiv
  dsimp only [M14HorizontalCovariantDerivative]
  rw [map_add]
  change _ + (g.spatialTangentEquiv (b s).1 (b s).2).symm
    (rawHorizontalCovariantDerivative G.leafwise (E.extension s) (e.toSpacetime (b s))
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
        (fun r => e.toSpacetime (b r)) J s (1 : ℝ))) = _
  erw [hvel]
  change _ + (g.spatialTangentEquiv (b s).1 (b s).2).symm
    (rawHorizontalCovariantDerivative G.leafwise (E.extension s) (e.toSpacetime (b s))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (b s) (v.1, v.2))) = _
  rw [hvt, hconn, ContinuousLinearEquiv.symm_apply_apply, hspace, hderiv]
  abel

end PoincareConjecture.M14
