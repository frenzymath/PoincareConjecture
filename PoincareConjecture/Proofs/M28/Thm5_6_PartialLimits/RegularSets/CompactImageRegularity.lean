import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.InverseOpenDistance
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.OpenCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.M28

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

theorem mem_intrinsicImage_regularPoints_of_compact_inverse_buffer
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (V : TopologicalSpace.Opens M) (hVs : (V : Set M) ⊆ e.source)
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ (V : Set M))
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ (V : Set M), ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ C ^ 2 * h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v))
    {x : M} (hx : x ∈ (V : Set M)) {delta : ℝ} (hdelta : 0 < delta)
    (hball : g.ball x (C * delta) ⊆ K) :
    let U : TopologicalSpace.Opens N :=
      ⟨e '' (V : Set M), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        V.isOpen hVs⟩
    (⟨e x, x, hx, rfl⟩ : U) ∈ regularPoints (intrinsicOpenMetric h U) delta := by
  let U : TopologicalSpace.Opens N :=
    ⟨e '' (V : Set M), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      V.isOpen hVs⟩
  have hU : (U : Set N) ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.toPartialEquiv.map_source (hVs hz)
  let p : U := ⟨e x, x, hx, rfl⟩
  have hleft : e.symm (p : N) = x :=
    e.toPartialEquiv.left_inv (hVs hx)
  have hdist (q : U) : g.edist x (e.symm (q : N)) ≤
      ENNReal.ofReal C * (intrinsicOpenMetric h U).edist p q := by
    rw [← hleft]
    apply inverse_edist_le_intrinsicOpenMetric g h e U hU hC
    intro y hy v
    have hyV : e.symm y ∈ (V : Set M) := by
      obtain ⟨z, hz, rfl⟩ := hy
      rw [show e.symm (e z) = z from e.toPartialEquiv.left_inv (hVs hz)]
      exact hz
    exact hbound _ hyV v
  have heK : IsCompact (e '' K) := hK.image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono (hKV.trans hVs))
  have heKU : e '' K ⊆ range (Subtype.val : U → N) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨e z, z, hKV hz, rfl⟩, rfl⟩
  have hQ : IsCompact ((Subtype.val : U → N) ⁻¹' (e '' K)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' heK heKU
  change p ∈ regularPoints (intrinsicOpenMetric h U) delta
  intro r hr
  have hsub : (intrinsicOpenMetric h U).ball p r ⊆
      (Subtype.val : U → N) ⁻¹' (e '' K) := by
    intro q hq
    have hd : g.edist x (e.symm (q : N)) < ENNReal.ofReal (C * delta) := by
      calc
        g.edist x (e.symm (q : N)) ≤
            ENNReal.ofReal C * (intrinsicOpenMetric h U).edist p q := hdist q
        _ < ENNReal.ofReal C * ENNReal.ofReal delta :=
          (ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
            ENNReal.ofReal_ne_top)
            (hq.trans ((ENNReal.ofReal_lt_ofReal_iff hdelta).mpr hr))
        _ = ENNReal.ofReal (C * delta) := (ENNReal.ofReal_mul hC.le).symm
    exact ⟨e.symm (q : N), hball hd, e.toPartialEquiv.right_inv (hU q.property)⟩
  exact hQ.of_isClosed_subset isClosed_closure
    ((closure_mono hsub).trans hQ.isClosed.closure_subset)

theorem mem_regularPoints_of_compact_inverse_buffer
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (V : TopologicalSpace.Opens M) (hVc : IsCompact (closure (V : Set M)))
    (hVs : closure (V : Set M) ⊆ e.source)
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ (V : Set M))
    (hbound : ∀ x ∈ (V : Set M), ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ 4 * h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v))
    {x : M} (hx : x ∈ (V : Set M)) {delta : ℝ} (hdelta : 0 < delta)
    (hball : g.ball x (2 * delta) ⊆ K) :
    e x ∈ regularPoints h delta := by
  let U : TopologicalSpace.Opens N :=
    ⟨e '' (V : Set M), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      V.isOpen (subset_closure.trans hVs)⟩
  let p : U := ⟨e x, x, hx, rfl⟩
  have hp : p ∈ regularPoints (intrinsicOpenMetric h U) delta :=
    mem_intrinsicImage_regularPoints_of_compact_inverse_buffer g h e V
      (subset_closure.trans hVs) hK hKV (by norm_num : (0 : ℝ) < 2)
      (by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hbound) hx hdelta hball
  have hamb := ambient_ball_subset_open_of_intrinsic_regular h U p hp
  have heV : IsCompact (e '' closure (V : Set M)) :=
    hVc.image_of_continuousOn (e.contMDiffOn.continuousOn.mono hVs)
  intro r hr
  have hsub : h.ball (e x) r ⊆ e '' closure (V : Set M) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hamb (hy.trans_le (ENNReal.ofReal_le_ofReal hr.le))
    exact ⟨z, subset_closure hz, rfl⟩
  exact heV.of_isClosed_subset isClosed_closure
    ((closure_mono hsub).trans heV.isClosed.closure_subset)

end PoincareConjecture.M28
