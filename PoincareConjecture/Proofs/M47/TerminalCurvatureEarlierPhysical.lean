import PoincareConjecture.Proofs.M47.SeedOrdinaryBirthVolume
import PoincareConjecture.Proofs.M47.TerminalSourceRealizationCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Metric.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_exists_physical_slice_chart
    {S : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {b Q : ℝ} {I : Set ℝ} (V : TopologicalSpace.Opens C.carrier)
    (e : SurgeryFlowCylinder S C b Q I V) (s : ℝ) (hs : s ∈ I) (q : V)
    (g : RiemannianMetric 3 V)
    (hmetric : ∀ (y : V) (v w : TangentSpace (𝓡 3) y),
      g.inner y v w = e.pullbackInner s hs y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → C.carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → C.carrier) y w)) :
    ∃ chi : PartialDiffeomorph (𝓡 3) (𝓡 3) V (S.slice (b + s / Q)).carrier ∞,
      chi.source = univ ∧ (∀ y : V, chi y = e.forward s hs y.val) ∧
        ∀ (y : V) (v w : TangentSpace (𝓡 3) y),
          g.inner y v w = (rescaledMetric (S.metric (b + s / Q)) Q e.scale_pos).inner
            (chi y) (mfderiv (𝓡 3) (𝓡 3) chi y v) (mfderiv (𝓡 3) (𝓡 3) chi y w) := by
  obtain ⟨chi, hsource, hchi⟩ :=
    Proofs.M47.exists_seed_ordinary_slice_chart V e s hs q
  refine ⟨chi, hsource, hchi, ?_⟩
  intro y v w
  have hmap : (chi : V → (S.slice (b + s / Q)).carrier) =
      fun z : V => e.forward s hs z.val := funext hchi
  have hf := (e.forward_smooth s hs y.val y.property).contMDiffAt
    (V.isOpen.mem_nhds y.property)
  have hd := mfderiv_comp y (hf.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞) y).mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (fun z : V => e.forward s hs z.val) y = _ at hd
  change g.inner y v w = Q * (S.metric (b + s / Q)).inner (chi y)
    (mfderiv (𝓡 3) (𝓡 3) chi y v) (mfderiv (𝓡 3) (𝓡 3) chi y w)
  rw [hmap, hd]
  exact hmetric y v w

theorem terminalCurvature_physical_composite_source
    {M : Type u} {N : Type v} {X : Type w}
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace E N]
    [TopologicalSpace X] [ChartedSpace E X]
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X M ∞)
    (chi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hchi : chi.source = univ) :
    (phi.trans chi).source = phi.source := by
  ext x
  change (x ∈ phi.source ∧ phi x ∈ chi.source) ↔ x ∈ phi.source
  rw [hchi]
  simp only [mem_univ, and_true]

theorem terminalCurvature_physical_composite_jets
    {M : Type u} {N : Type v} {X : Type w}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X M ∞)
    (chi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hchi : chi.source = univ)
    (hmetric : ∀ (y : M) (v w : TangentSpace (𝓡 3) y),
      g.inner y v w = h.inner (chi y)
        (mfderiv (𝓡 3) (𝓡 3) chi y v) (mfderiv (𝓡 3) (𝓡 3) chi y w))
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (m : ℕ) {x : E} (hx : x ∈ (phi.symm.trans c).target) :
    iteratedFDeriv ℝ m (h.pullbackCoefficients ((phi.trans chi) ∘ c.symm)) x =
      iteratedFDeriv ℝ m (g.pullbackCoefficients (phi ∘ c.symm)) x := by
  have heq : h.pullbackCoefficients ((phi.trans chi) ∘ c.symm)
      =ᶠ[𝓝 x] g.pullbackCoefficients (phi ∘ c.symm) := by
    filter_upwards [(phi.symm.trans c).open_target.mem_nhds hx] with y hy
    have hA := (phi.symm.trans c).contMDiffOn_invFun.contMDiffAt
      ((phi.symm.trans c).open_target.mem_nhds hy)
    have hf := chi.contMDiffOn_toFun.contMDiffAt
      (chi.open_source.mem_nhds (show phi (c.symm y) ∈ chi.source by rw [hchi]; trivial))
    exact M44.pullbackCoefficients_eq_of_metric_germ g h
      (hf.mdifferentiableAt (by simp)) (hA.mdifferentiableAt (by simp))
      (Filter.EventuallyEq.refl _ _) (fun v w => (hmetric _ v w).symm)
  exact (heq.iteratedFDeriv ℝ m).self_of_nhds

end PoincareConjecture.M47
