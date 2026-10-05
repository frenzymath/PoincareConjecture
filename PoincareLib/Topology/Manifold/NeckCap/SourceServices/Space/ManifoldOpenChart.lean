import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Compatibility.ReducedLength
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.LocalSmoothInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Smooth open charts with a manifold source

An invertible manifold derivative gives a local inverse by transporting
M09's Euclidean inverse theorem through a source chart. Injectivity on
an open domain then gives a single chart with a smooth inverse. This
supplies the collar coordinates used in Hatcher, Notes on Basic
3-Manifold Topology, Theorem 1.1 and Lemmas 1.2-1.3, pp. 1-3.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M25.Topology3D

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A smooth map from an ordinary manifold with bijective derivative
has a smooth local inverse; collar-coordinate step in Hatcher, pp. 1-3. -/
theorem exists_manifold_source_local_inverse (f : M → F) {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (x : M) (hx : x ∈ U)
    (hb : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    ∃ e : OpenPartialHomeomorph M F, x ∈ e.source ∧ e.source ⊆ U ∧
      EqOn e f e.source ∧ ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ e.symm e.target := by
  let c := chartAt E x
  let W : Set E := c.target ∩ c.symm ⁻¹' U
  let g : E → F := fun v => f (c.symm v)
  have hxc : x ∈ c.source := mem_chart_source E x
  have hW : IsOpen W := c.continuousOn_symm.isOpen_inter_preimage c.open_target hU
  have hcx : c x ∈ W := by
    refine ⟨c.map_source hxc, ?_⟩
    change c.symm (c x) ∈ U
    rwa [c.left_inv hxc]
  have hcs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hg : ContDiffOn ℝ ∞ g W :=
    (hf.comp (hcs.mono inter_subset_left) (fun v hv => hv.2)).contDiffOn
  have hcsd := (mdifferentiable_chart (I := 𝓘(ℝ, E)) x).symm
  have hfd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f (c.symm (c x)) := by
    rw [c.left_inv hxc]
    exact (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  let d : E →L[ℝ] F :=
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c.symm (c x))).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))
  have hgd : HasFDerivAt g d (c x) :=
    (hfd.hasMFDerivAt.comp (c x)
      (hcsd.mdifferentiableAt hcx.1).hasMFDerivAt).hasFDerivAt
  have hderiv : fderiv ℝ g (c x) = d := HasFDerivAt.fderiv hgd
  have hgb : Function.Bijective (fderiv ℝ g (c x)) := by
    rw [hderiv]
    exact (show Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c.symm (c x))) by
      rw [c.left_inv hxc]
      exact hb).comp (hcsd.mfderiv_bijective hcx.1)
  obtain ⟨e0, hx0, h0W, he0, hi0, _⟩ :=
    PoincareMT.Proofs.M09.exists_smooth_local_inverse g W hW hg (c x) hcx hgb
  let e := c.trans e0
  refine ⟨e, ⟨hxc, hx0⟩, ?_, ?_, ?_⟩
  · intro y hy
    have hu := (h0W hy.2).2
    change c.symm (c y) ∈ U at hu
    simpa only [c.left_inv hy.1] using hu
  · intro y hy
    change e0 (c y) = f y
    rw [he0]
    exact congrArg f (c.left_inv hy.1)
  · exact hcs.comp (hi0.contMDiffOn.mono (fun y hy => hy.1)) (fun y hy => hy.2)

variable (f : M → F) {U : Set M} (hU : IsOpen U)
variable (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
variable (hb : ∀ x ∈ U, Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))

include hU hf hb

/-- A map with bijective manifold derivatives sends open subsets of its
smooth domain to open sets; Hatcher's collar neighborhoods, pp. 1-3. -/
theorem manifold_isOpen_image {T : Set M} (hT : IsOpen T) (hTU : T ⊆ U) :
    IsOpen (f '' T) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, _, he, _⟩ :=
    exists_manifold_source_local_inverse f hU hf x (hTU hx) (hb x (hTU hx))
  have hopen : IsOpen (e '' (e.source ∩ T)) :=
    e.isOpen_image_of_subset_source (e.open_source.inter hT) inter_subset_left
  have hximage : f x ∈ e '' (e.source ∩ T) := ⟨x, ⟨hxe, hx⟩, he hxe⟩
  apply mem_of_superset (hopen.mem_nhds hximage)
  rintro z ⟨v, hv, rfl⟩
  exact ⟨v, hv.2, (he hv.1).symm⟩

/-- The domain restriction of a nonsingular smooth map is open. -/
theorem manifold_isOpenMap_restrict : IsOpenMap (U.domRestrict f) := by
  intro T hT
  have hopen : IsOpen (Subtype.val '' T : Set M) :=
    hU.isOpenEmbedding_subtypeVal.isOpenMap T hT
  have hsub : (Subtype.val '' T : Set M) ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  rw [domRestrict_eq, image_comp]
  exact manifold_isOpen_image f hU hf hb hopen hsub

variable [Nonempty M] (hi : InjOn f U)

/-- An injective nonsingular smooth manifold map is one open chart on
its full domain; the target is its actual image. -/
noncomputable def manifoldOpenChart : OpenPartialHomeomorph M F :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U)
    hf.continuousOn (manifold_isOpenMap_restrict f hU hf hb) hU

/-- The assembled chart keeps the given total forward map. -/
@[simp] theorem manifoldOpenChart_apply (x : M) :
    manifoldOpenChart f hU hf hb hi x = f x := rfl

/-- The assembled chart has exactly the prescribed source. -/
@[simp] theorem manifoldOpenChart_source : (manifoldOpenChart f hU hf hb hi).source = U := rfl

/-- The assembled chart has exactly the prescribed image as target. -/
@[simp] theorem manifoldOpenChart_target :
    (manifoldOpenChart f hU hf hb hi).target = f '' U := rfl

/-- The inverse on the full image agrees locally with each smooth
inverse-function chart, hence is smooth; Hatcher's collar coordinates. -/
theorem manifoldOpenChart_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (manifoldOpenChart f hU hf hb hi).symm (f '' U) := by
  let e := manifoldOpenChart f hU hf hb hi
  intro y hy
  have hx : e.symm y ∈ U := e.map_target hy
  obtain ⟨l, hxl, hlU, hlf, hls⟩ :=
    exists_manifold_source_local_inverse f hU hf (e.symm y) hx (hb _ hx)
  have hly : y ∈ l.target := by
    have hlimage : l (e.symm y) = y := (hlf hxl).trans (e.right_inv hy)
    exact hlimage ▸ l.map_source hxl
  have hagree : e.symm =ᶠ[𝓝 y] l.symm := by
    filter_upwards [(e.open_target.inter l.open_target).mem_nhds ⟨hy, hly⟩] with z hz
    apply hi (e.map_target hz.1) (hlU (l.map_target hz.2))
    exact (e.right_inv hz.1).trans ((hlf (l.map_target hz.2)).symm.trans (l.right_inv hz.2)).symm
  exact ((hls.contMDiffAt (l.open_target.mem_nhds hly)).congr_of_eventuallyEq
    hagree).contMDiffWithinAt

end PoincareMT.M25.Topology3D
