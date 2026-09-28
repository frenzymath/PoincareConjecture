import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PhysicalBuffer
import PoincareConjecture.Proofs.M36.MetricComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.RiemannianMetric

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

theorem edist_comp_le_of_pullback_bound
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    {f : X → Y} (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hmetric : ∀ x (v : TangentSpace (𝓡 3) x),
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ g.inner x v v) (x y : X) :
    h.edist (f x) (f y) ≤ g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hb
  have hd := M36.edist_comp_le_pathELength_of_pullback_bound g h
    (U := univ) (fun z _ => hf z) (fun z _ => hmetric z) zero_le_one hγ
    (subset_univ _)
  rw [hγ0, hγ1] at hd
  exact hd.trans hlength.le

theorem closure_ball_subset_ball_of_margin [RegularSpace X]
    (g : RiemannianMetric 3 X) {p x : X} {a r R : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hR : a + r < R) (hx : x ∈ g.ball p a) :
    closure (g.ball x r) ⊆ g.ball p R := by
  have hc : IsClosed {y : X | g.edist x y ≤ ENNReal.ofReal r} :=
    isClosed_Iic.preimage ((M36.metric_edist_continuous g).comp
      (continuous_const.prodMk continuous_id))
  have hcl : closure (g.ball x r) ⊆ {y : X | g.edist x y ≤ ENNReal.ofReal r} :=
    closure_minimal (fun y (hy : y ∈ g.ball x r) =>
      show g.edist x y ≤ ENNReal.ofReal r from hy.le) hc
  intro y hy
  calc
    g.edist p y ≤ g.edist p x + g.edist x y := M36.metric_edist_triangle g p x y
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal r := add_le_add hx.le (hcl hy)
    _ = ENNReal.ofReal (a + r) := (ENNReal.ofReal_add ha hr).symm
    _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.M44

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem physicalBufferFlow_isCompact_closure_ball
    {J : Set ℝ} (F : RicciFlow 3 M J)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞)
    (t : ℝ) (p : (⟨e.target, e.open_target⟩ : Opens M)) (r : ℝ)
    (hcompact : IsCompact (closure ((F.metric t).ball p.1 r)))
    (hinside : closure ((F.metric t).ball p.1 r) ⊆ e.target) :
    IsCompact (closure (((physicalBufferFlow F e).metric t).ball p r)) := by
  let U : Opens M := ⟨e.target, e.open_target⟩
  have hc : IsCompact ((Subtype.val : U → M) ⁻¹' closure ((F.metric t).ball p.1 r)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact (by
      rw [Subtype.range_coe]
      exact hinside)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.preimage continuous_subtype_val)
  intro x hx
  apply subset_closure
  exact (((physicalBufferFlow F e).metric t).edist_comp_le_of_pullback_bound
    (F.metric t) (f := Subtype.val) contMDiff_subtype_val
    (fun _ _ => le_rfl) p x).trans_lt hx

theorem physicalBufferFlow_isCompact_closure_ball_of_margin [RegularSpace M]
    {J : Set ℝ} (F : RicciFlow 3 M J)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞)
    (t : ℝ) (tip : M) {a r R : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hR : a + r < R)
    (hcompact : IsCompact (closure ((F.metric t).ball tip R)))
    (hinside : (F.metric t).ball tip R ⊆ e.target)
    (p : (⟨e.target, e.open_target⟩ : Opens M)) (hp : p.1 ∈ (F.metric t).ball tip a) :
    IsCompact (closure (((physicalBufferFlow F e).metric t).ball p r)) := by
  have hs := (F.metric t).closure_ball_subset_ball_of_margin ha hr hR hp
  apply physicalBufferFlow_isCompact_closure_ball F e t p r
  · exact hcompact.of_isClosed_subset isClosed_closure (hs.trans subset_closure)
  · exact hs.trans hinside

end PoincareConjecture.M44
