import PoincareConjecture.Proofs.Horizon.Topology.Connected.SublevelEndpoint
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.CountableComplement
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.RegularChart
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function Metric
open scoped Topology ContDiff Manifold

namespace Poincare.Geometry.Manifold

private theorem hasConnectedLowerSide_of_scalar_chart
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → ℝ} {O : Set X} (hO : IsOpen O) {x : X} (hx : x ∈ O)
    (e : OpenPartialHomeomorph X (ℝ × F)) (hxe : x ∈ e.source)
    (hef : ∀ y ∈ e.source, (e y).1 = f y) :
    Poincare.Topology.HasConnectedLowerSide f O (f x) x := by
  have htarget : e.target ∩ e.symm ⁻¹' O ∈ 𝓝 (e x) :=
    (e.symm.isOpen_inter_preimage hO).mem_nhds
      ⟨e.map_source hxe, by simpa only [mem_preimage, e.left_inv hxe] using hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp htarget
  have hBT : ball (e x) r ⊆ e.target := hball.trans inter_subset_left
  let V := e.symm '' ball (e x) r
  have hV : IsOpen V := e.isOpen_image_symm_of_subset_target isOpen_ball hBT
  have hxV : x ∈ V := ⟨e x, mem_ball_self hr, e.left_inv hxe⟩
  have hVO : V ⊆ O := by rintro y ⟨z, hz, rfl⟩; exact (hball hz).2
  have hVe : V ⊆ e.source := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_target (hBT hz)
  let A : Set (ℝ × F) := ball (e x) r ∩ {z | z.1 < f x}
  have hA : IsPreconnected A :=
    ((convex_ball (e x) r).inter
      (convex_halfSpace_lt (show IsLinearMap ℝ (Prod.fst : ℝ × F → ℝ) from
        ⟨fun _ _ => rfl, fun _ _ => rfl⟩) (f x))).isPreconnected
  have himage : e.symm '' A = V ∩ f ⁻¹' Iio (f x) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
      have hval := hef (e.symm z) (e.map_target (hBT hz.1))
      rw [e.right_inv (hBT hz.1)] at hval
      change f (e.symm z) < f x
      rw [← hval]
      exact hz.2
    · rintro ⟨⟨z, hz, rfl⟩, hzy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      have hval := hef (e.symm z) (e.map_target (hBT hz))
      rw [e.right_inv (hBT hz)] at hval
      change z.1 < f x
      rw [hval]
      exact hzy
  have hisimage : e.IsImage (V ∩ f ⁻¹' Iio (f x)) A := by
    intro y hy
    constructor
    · intro hye
      rw [← himage]
      exact ⟨e y, hye, e.left_inv hy⟩
    · intro hyv
      rw [← himage] at hyv
      rcases hyv with ⟨z, hz, rfl⟩
      rwa [e.right_inv (hBT hz.1)]
  refine ⟨V, hV, hxV, hVO, ?_, ?_⟩
  · rw [← himage]
    exact hA.image e.symm (e.symm.continuousOn.mono (inter_subset_left.trans hBT))
  · intro y hy
    have hye := hVe hy.1
    apply (hisimage.closure.apply_mem_iff hye).mp
    have hyball : e y ∈ ball (e x) r := by
      rcases hy.1 with ⟨z, hz, rfl⟩
      simpa only [e.right_inv (hBT hz)] using hz
    have hyhalf : e y ∈ closure ({z : ℝ × F | z.1 < f x}) := by
      have heq : {z : ℝ × F | z.1 < f x} = Iio (f x) ×ˢ (univ : Set F) := by ext z; simp
      rw [heq, closure_prod_eq, closure_Iio, closure_univ]
      exact ⟨by change (e y).1 ≤ f x; rw [hef y hye]; exact hy.2, mem_univ _⟩
    exact isOpen_ball.inter_closure ⟨hyball, hyhalf⟩

theorem hasConnectedLowerSide_of_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {O : Set M} (hO : IsOpen O) {x : M} (hx : x ∈ O)
    (hreg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x ≠ 0) :
    Poincare.Topology.HasConnectedLowerSide f O (f x) x := by
  let L : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x
  have hsurj : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) :=
    (LinearMap.surjective_iff_ne_zero (f := L.toLinearMap)).mpr (by
      intro heq
      apply hreg
      ext v
      exact congrArg (fun A : E →ₗ[ℝ] ℝ => A v) heq)
  obtain ⟨e, hxe, _, _, _, hef, _⟩ :=
    Poincare.Manifold.exists_manifold_superlevel_chart hf x hsurj
  exact hasConnectedLowerSide_of_scalar_chart hO hx e hxe hef

theorem hasConnectedLowerSide_of_regular_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {O : Set M} (hO : IsOpen O)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f O)
    {x : M} (hx : x ∈ O) (hreg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x ≠ 0) :
    Poincare.Topology.HasConnectedLowerSide f O (f x) x := by
  let U : TopologicalSpace.Opens M := ⟨O, hO⟩
  let xU : U := ⟨x, hx⟩
  have hfU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun y : U => f y) :=
    fun y => (hf.contMDiffAt (hO.mem_nhds y.2)).comp y (contMDiff_subtype_val y)
  have hregU : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y : U => f y) xU ≠ 0 := by
    rw [RegularLevel.mfderiv_opens_restrict U f
      ((hf.contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hreg
  obtain ⟨V, hV, hxV, _, hconn, hdense⟩ :=
    hasConnectedLowerSide_of_regular hfU isOpen_univ (mem_univ xU) hregU
  let W : Set M := Subtype.val '' V
  have himage (s : Set ℝ) :
      Subtype.val '' (V ∩ (fun y : U => f y) ⁻¹' s) = W ∩ f ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨z, ⟨hz, hzf⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, hzf⟩
    · rintro ⟨⟨z, hz, rfl⟩, hzf⟩
      exact ⟨z, ⟨hz, hzf⟩, rfl⟩
  refine ⟨W, hO.isOpenEmbedding_subtypeVal.isOpenMap V hV, ⟨xU, hxV, rfl⟩,
    ?_, ?_, ?_⟩
  · rintro y ⟨z, _, rfl⟩
    exact z.2
  · rw [← himage]
    exact hconn.image Subtype.val continuous_subtype_val.continuousOn
  · intro y hy
    rw [← himage (Iic (f x))] at hy
    rcases hy with ⟨z, hz, rfl⟩
    rw [← himage (Iio (f x))]
    exact image_closure_subset_closure_image continuous_subtype_val ⟨z, hdense hz, rfl⟩

theorem hasConnectedLowerSide_of_strict_maximum
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 2))) M]
    {f : M → ℝ} {O : Set M} (hO : IsOpen O) {x : M} (hx : x ∈ O)
    (hmax : ∀ᶠ y in 𝓝 x, y ≠ x → f y < f x) :
    Poincare.Topology.HasConnectedLowerSide f O (f x) x := by
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds hx) hmax)
  let e := chartAt (EuclideanSpace ℝ (Fin (n + 2))) x
  have hxe : x ∈ e.source := mem_chart_source _ x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((e.symm.isOpen_inter_preimage hW).mem_nhds
      ⟨e.map_source hxe, by simpa only [mem_preimage, e.left_inv hxe] using hxW⟩)
  have hBT : ball (e x) r ⊆ e.target := hball.trans inter_subset_left
  let V := e.symm '' ball (e x) r
  have hV : IsOpen V := e.isOpen_image_symm_of_subset_target isOpen_ball hBT
  have hVW : V ⊆ W := by rintro y ⟨z, hz, rfl⟩; exact (hball hz).2
  have heq : V ∩ f ⁻¹' Iio (f x) = V \ {x} := by
    ext y
    constructor
    · rintro ⟨hyV, hyf⟩
      exact ⟨hyV, fun hyx => (lt_irrefl (f x)) (mem_singleton_iff.mp hyx ▸ hyf)⟩
    · rintro ⟨hyV, hyx⟩
      exact ⟨hyV, (hWsub (hVW hyV)).2 (by simpa only [mem_singleton_iff] using hyx)⟩
  refine ⟨V, hV, ⟨e x, mem_ball_self hr, e.left_inv hxe⟩,
    fun y hy => (hWsub (hVW hy)).1, ?_, ?_⟩
  · rw [heq]
    exact (Poincare.Topology.Manifold.isPathConnected_chart_ball_sdiff_countable
      x hr hBT (countable_singleton x)).isConnected.isPreconnected
  · intro y hy
    rw [heq]
    exact (Poincare.Topology.Manifold.dense_compl_countable (n := n)
      (countable_singleton x)).open_subset_closure_inter hV hy.1

end Poincare.Geometry.Manifold
