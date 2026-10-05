import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.WorldlineUniqueness
import PoincareLib.Geometry.Spacetime.Rescaling.Time

/-!
# Raw cylinders supplied by a flow box

Morgan--Tian Definitions 3.38 and 3.40, p. 61, and Corollary 11.3, p. 269.
A positive affine clock into one box gives a raw cylinder with exactly its
forward and inverse maps. Uniqueness then identifies any meeting cylinder
trajectory with the box line throughout their time overlap. This is the
local comparison needed before spatial gluing.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M30.Cylinder

/-- One ordinary box gives a raw cylinder at any positive affine clock
whose time image lies in the box (Definitions 3.38 and 3.40, p. 61). -/
noncomputable def ofBox (F : GeneralizedRicciFlowData.{u}) (b : F.box_index)
    (origin scale : ℝ) (hscale : 0 < scale) {I : Set ℝ}
    (hI : I ⊆ (fun s : ℝ => origin + s / scale) ⁻¹' (F.box b).interval) :
    GeneralizedFlowCylinder F (F.box b).carrier origin scale I univ where
  scale_pos := hscale
  forward s hs := (F.box b).forward (origin + s / scale) (hI hs)
  inverse s hs := (F.box b).inverse (origin + s / scale) (hI hs)
  forward_smooth s hs := ((F.box b).forward_smooth _ (hI hs)).contMDiffOn
  inverse_smooth s hs := by
    simpa only [image_univ] using (F.box b).inverse_smooth _ (hI hs)
  left_inverse s hs x _ := (F.box b).left_inverse _ (hI hs) x
  right_inverse s hs := by
    simpa only [image_univ] using (F.box b).right_inverse _ (hI hs)
  embedding := by
    have hclock : Topology.IsEmbedding (fun s : I => origin + s.val / scale) :=
      (parabolicTimeOrderIso scale hscale origin).symm.toHomeomorph.isEmbedding.comp
        Topology.IsEmbedding.subtypeVal
    exact (F.box_openEmbedding b).isEmbedding.comp
      ((hclock.codRestrict (F.box b).interval (fun s => hI s.property)).prodMap
        Topology.IsEmbedding.subtypeVal)
  vertical_compatibility s _ x _ := by
    refine ⟨b, x, 1, zero_lt_one, ?_⟩
    intro s' hs' _
    exact ⟨hI hs', rfl⟩

/-- The raw box cylinder retains the original spacetime map
(Definition 3.38, p. 61). -/
@[simp] theorem ofBox_pointMap (F : GeneralizedRicciFlowData.{u}) (b : F.box_index)
    (origin scale : ℝ) (hscale : 0 < scale) {I : Set ℝ}
    (hI : I ⊆ (fun s : ℝ => origin + s / scale) ⁻¹' (F.box b).interval)
    (s : ℝ) (hs : s ∈ I) (x : (F.box b).carrier.carrier) :
    (ofBox F b origin scale hscale hI).pointMap s hs x =
      (⟨origin + s / scale, (F.box b).forward _ (hI hs) x⟩ : F.point) := rfl

/-- The raw box pullback is exactly the scaled ordinary metric
(Definition 3.40, p. 61). -/
@[simp] theorem ofBox_pullbackInner (F : GeneralizedRicciFlowData.{u}) (b : F.box_index)
    (origin scale : ℝ) (hscale : 0 < scale) {I : Set ℝ}
    (hI : I ⊆ (fun s : ℝ => origin + s / scale) ⁻¹' (F.box b).interval)
    (s : ℝ) (hs : s ∈ I) (x : (F.box b).carrier.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (ofBox F b origin scale hscale hI).pullbackInner s hs x v w =
      scale * ((F.box b).flow.metric (origin + s / scale)).inner x v w := by
  exact congrArg (scale * ·) ((F.box b).metric_pullback _ (hI hs) x v w)

/-- A cylinder line meeting a box line stays equal to it whenever both
times are defined (Definition 3.38, p. 61; Corollary 11.3, p. 269). -/
theorem forward_eq_box_on_overlap
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hI : I.OrdConnected)
    {x : C.carrier} (hx : x ∈ U) (b : F.box_index) (y : (F.box b).carrier.carrier)
    {s : ℝ} (hs : s ∈ I) (hb : origin + s / scale ∈ (F.box b).interval)
    (hmeet : e.forward s hs x = (F.box b).forward _ hb y) :
    ∀ t (ht : t ∈ I) (htb : origin + t / scale ∈ (F.box b).interval),
      e.forward t ht x = (F.box b).forward _ htb y := by
  let K := I ∩ (fun t : ℝ => origin + t / scale) ⁻¹' (F.box b).interval
  have hK : K.OrdConnected := hI.inter ((F.box b).flow.interval.preimage_mono
    (parabolicTimeInv_strictMono scale e.scale_pos origin).monotone)
  let eK := restrict e (show K ⊆ I from inter_subset_left) Subset.rfl
  let eB := ofBox F b origin scale e.scale_pos
    (show K ⊆ (fun t : ℝ => origin + t / scale) ⁻¹' (F.box b).interval from
      inter_subset_right)
  have heq : eK.pointMap s ⟨hs, hb⟩ x = eB.pointMap s ⟨hs, hb⟩ y :=
    congrArg (fun z => (⟨origin + s / scale, z⟩ : F.point)) hmeet
  have hall := pointMap_eq_on_interval eK eB hK hx (mem_univ y) ⟨hs, hb⟩ heq
  intro t ht htb
  exact eq_of_heq (Sigma.mk.inj_iff.mp (hall t ⟨ht, htb⟩)).2

end PoincareMT.M30.Cylinder
