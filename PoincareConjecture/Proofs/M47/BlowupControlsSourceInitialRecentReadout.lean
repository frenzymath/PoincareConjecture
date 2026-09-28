import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentPatch
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier] {i : Fin (F.event T hT).cap_count} {A : ℝ}
  {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
  {J : Set ℝ} {V : Set (F.slice T).carrier}
  (e : SurgeryFlowCylinder F (F.slice T) T ((F.parameters.h T)⁻¹ ^ 2) J V)
  (initial : SurgeryCapInitialComparison F T hT i A)
  (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
  (hh : 0 < F.parameters.h T) {g : RiemannianMetric 3 StandardCapSpace}
  (N : EpsilonNeck g) {epsilon s H c : ℝ}
  (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
  (hdomain : ∀ r ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
    r + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
  (hclock : MapsTo (fun u : ℝ => s + u / H) (Icc (-H * s) 0) J)
  (U : TopologicalSpace.Opens (F.slice T).carrier) {x : U}
  (patch : M45CylinderPatch (neckOpenSourceCarrier U) epsilon⁻¹ x)
  (hcoordinate : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
    (patch.coordinate z).val = initial.chart (N.coordinate_map (neckAxialSpaceMap 1 c z)))
  {I : Set ℝ} (G : RicciFlow 3 U I)
  (hmetric : ∀ u (hu : u ∈ Icc (-H * s) 0) (y : U) (v w : TangentSpace (𝓡 3) y),
    (G.metric u).inner y v w = H * e.pullbackInner (s + u / H) (hclock hu) y.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) y v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) y w))

include hsource hdomain hcoordinate hmetric

theorem source_initial_recent_native_readout
    (u : ℝ) (hu : u ∈ Icc (-H * s) 0) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (v w : RoundCylinderTangent z) :
    roundCylinderPullback (G.metric u) patch.coordinate z v w =
      sourceRecentCapTensor e initial comparison hh N s H c hclock u z v w := by
  let phi := actualCapSliceChart e initial comparison (s + u / H) (hclock hu)
  let q := (F.parameters.h T)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (T + (s + u / H) / q)) q
    (sq_pos_of_pos (inv_pos.mpr hh))
  let Amap := neckAxialSpaceMap 1 c
  let f := initial.chart ∘ N.coordinate_map ∘ Amap
  have hAz : (Amap z).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [Amap, neckAxialSpaceMap, one_mul] using hdomain z.2 hz
  have hpoint := hsource (N.coordinate_map_mem_of_axial_mem hAz)
  have hN := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hAz⟩)).mdifferentiableAt (by simp)
  have hA : MDifferentiableAt Ic Ic Amap z :=
    (neckAxialSpaceMap_contMDiff 1 c).mdifferentiableAt (by simp)
  have hbirthSmooth := initial.chart_smooth.contMDiffAt
    ((Proofs.M46.capInitialPartialDiffeomorph initial).open_source.mem_nhds hpoint)
  have hbirth := hbirthSmooth.mdifferentiableAt (by simp)
  have hf : MDifferentiableAt Ic (𝓡 3) f z := (hbirth.comp (Amap z) hN).comp z hA
  have hpatch : MDifferentiableAt Ic (𝓡 3) (patch.coordinate : RoundCylinderSpace → U) z :=
    (patch.coordinate_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : U → (F.slice T).carrier) (patch.coordinate z) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have heq : (Subtype.val : U → (F.slice T).carrier) ∘ patch.coordinate =ᶠ[𝓝 z] f := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show z ∈ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨mem_univ _, hz⟩)] with p hp
    exact hcoordinate p hp.2
  have hd := (mfderiv_comp z hsub hpatch).symm.trans heq.mfderiv_eq
  have hv := congrArg (fun L => L v) hd
  have hw := congrArg (fun L => L w) hd
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) (patch.coordinate z)
    (mfderiv Ic (𝓡 3) patch.coordinate z v) = mfderiv Ic (𝓡 3) f z v at hv
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) (patch.coordinate z)
    (mfderiv Ic (𝓡 3) patch.coordinate z w) = mfderiv Ic (𝓡 3) f z w at hw
  have hread := hmetric u hu (patch.coordinate z)
    (mfderiv Ic (𝓡 3) patch.coordinate z v) (mfderiv Ic (𝓡 3) patch.coordinate z w)
  rw [hv, hw, hcoordinate z hz] at hread
  have hV : IsOpen V := comparison.choose_spec.2.2.2.1 ▸
    (Proofs.M46.capInitialPartialDiffeomorph initial).open_target
  have hfV : f z ∈ V := comparison.choose_spec.2.2.2.1 ▸
    mem_image_of_mem initial.chart hpoint
  have he := (e.forward_smooth (s + u / H) (hclock hu) |>.contMDiffAt
    (hV.mem_nhds hfV)).mdifferentiableAt (by simp)
  have hphysical := mfderiv_comp z he hf
  have hphiPoint : N.coordinate_map (Amap z) ∈ phi.source := by
    rw [actualCapSliceChart_source]
    exact hpoint
  have hphi := (phi.contMDiffOn.contMDiffAt
    (phi.open_source.mem_nhds hphiPoint)).mdifferentiableAt (by simp)
  have hmodel := mfderiv_comp z (hphi.comp (Amap z) hN) hA
  have haffine : roundCylinderPullback g' ((phi ∘ N.coordinate_map) ∘ Amap) z v w =
      neckAxialTensorPullback 1 c (roundCylinderPullback g' (phi ∘ N.coordinate_map)) z v w := by
    unfold roundCylinderPullback neckAxialTensorPullback
    rw [hmodel]
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, Amap,
      neckAxialSpaceMap_mfderiv]
  calc
    roundCylinderPullback (G.metric u) patch.coordinate z v w =
        H * e.pullbackInner (s + u / H) (hclock hu) (f z)
          (mfderiv Ic (𝓡 3) f z v) (mfderiv Ic (𝓡 3) f z w) := hread
    _ = H * roundCylinderPullback g' (e.forward (s + u / H) (hclock hu) ∘ f) z v w := by
      unfold roundCylinderPullback
      rw [hphysical]
      rfl
    _ = sourceRecentCapTensor e initial comparison hh N s H c hclock u z v w := by
      simp only [sourceRecentCapTensor, dif_pos hu]
      rw [← haffine]
      rfl

theorem source_initial_recent_family_on_patch
    (hfamily : RoundCylinderFamilyClose epsilon (Icc (-H * s) 0)
      (sourceRecentCapTensor e initial comparison hh N s H c hclock)) :
    RoundCylinderFamilyClose epsilon (Icc (-H * s) 0)
      (fun u => roundCylinderPullback (G.metric u) patch.coordinate) := by
  apply hfamily.congr_cylinder
  intro u hu z hz v w
  exact (source_initial_recent_native_readout e initial comparison hh N hsource hdomain hclock
    U patch hcoordinate G hmetric u hu z hz v w).symm

end PoincareConjecture.M47
