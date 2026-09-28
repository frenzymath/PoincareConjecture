import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalAxisEndpoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondCoordinateRadii
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedRadiusPrismMaps

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in


theorem ComponentBranchModel.exists_local_half_face_maps
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (v : D.sample → ℝ × V3) (hv : v ∈ D.axis.vertices)
    {x y : V2} (C : RawCrossingChart e f R x y)
    (hC : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar v).space C.chart.source)
    (hface : (D.complex.closedStar v).AffineOnFaces (fun z ↦ C.chart (D.inverse z)))
    (haxis : ∀ z ∈ (D.complex.closedStar v).space,
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0)
    (s : Bool → Finset (D.sample → ℝ × V3)) (hs : ∀ j, s j ∈ D.axis.faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, v ∈ s j)
    (hdisj : Disjoint (D.complex.barycentricDualBlock (s false)).space
      (D.complex.barycentricDualBlock (s true)).space)
    (G : ∀ b, signedTubeDiamond ≃ₜ (D.complex.barycentricDualBlock (s b)).space)
    (hG : ∀ b, (G b).IsFinitePL)
    (hQ : ∀ b eps delta (z : signedTubeDiamond),
      (z : P2) ∈ signedTubeQuarter eps delta ↔
        (G b z : D.sample → ℝ × V3) ∈ signedCoordinateSector
          (D.complex.barycentricDualBlock (s b)).space
          (fun j w => C.chart (D.inverse w) j.castSucc) (fun _ => true) eps delta)
    (hcenter : ∀ b, (G b ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : D.sample → ℝ × V3) =
        (s b).centroid ℝ id) :
    let V := D.complex.barycentricDualBlock {v}
    let Z := V.space ∩ D.axis.space
    let face := fun (j : Fin 2) (sign : Bool) =>
      {z | z ∈ V.space ∧ C.chart (D.inverse z) j.castSucc = 0 ∧
        SignedJointCross.side sign (C.chart (D.inverse z) j.rev.castSucc)}
    let outer := fun j sign => face j sign ∩ (V.link v).space
    ∃ axis : Icc (0 : ℝ) 1 ≃ₜ Z, axis.IsFinitePL ∧
      (axis ⟨0, le_rfl, zero_le_one⟩ : D.sample → ℝ × V3) = (s false).centroid ℝ id ∧
      (axis ⟨1, zero_le_one, le_rfl⟩ : D.sample → ℝ × V3) = (s true).centroid ℝ id ∧
      ∀ j sign, ∃ map : ↥(signedTubeRadius j sign ×ˢ Icc (0 : ℝ) 1) ≃ₜ face j sign,
        map.IsFinitePL ∧
        (∀ t : Icc (0 : ℝ) 1,
          (map ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : D.sample → ℝ × V3) = axis t) ∧
        (∀ b (z : signedTubeRadius j sign),
          (map ⟨(z, if b then 1 else 0), z.property, by cases b <;> simp⟩ : D.sample → ℝ × V3) =
            G b ⟨z, signedTubeRadius_subset_diamond j sign z.property⟩) ∧
        (∀ z : ↥(signedTubeRadius j sign ×ˢ Icc (0 : ℝ) 1),
          (z : P2 × ℝ) ∈ signedTubePrismAxis 0 1 ↔ (map z : D.sample → ℝ × V3) ∈ Z) ∧
        (∀ z : ↥(signedTubeRadius j sign ×ˢ Icc (0 : ℝ) 1),
          (z : P2 × ℝ) ∈ signedTubePrismOuter j sign 0 1 ↔
            (map z : D.sample → ℝ × V3) ∈ outer j sign) ∧
        ∀ b (z : ↥(signedTubeRadius j sign ×ˢ Icc (0 : ℝ) 1)),
          (z : P2 × ℝ) ∈ signedTubeRadius j sign ×ˢ {if b then 1 else 0} ↔
            (map z : D.sample → ℝ × V3) ∈ signedCoordinateFace
              (D.complex.barycentricDualBlock (s b)).space
              (fun j w => C.chart (D.inverse w) j.castSucc) (fun _ => true) j sign := by
  classical
  let V := D.complex.barycentricDualBlock {v}
  let Z := V.space ∩ D.axis.space
  let J := fun b => (D.complex.barycentricDualBlock (s b)).space
  let center := fun b => (s b).centroid ℝ id
  let c := fun (j : Fin 2) z => C.chart (D.inverse z) j.castSucc
  let face := fun (j : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ c j z = 0 ∧ SignedJointCross.side sign (c j.rev z)}
  let outer := fun j sign => face j sign ∩ (V.link v).space
  let rad := fun b j sign => signedCoordinateFace (J b) c (fun _ => true) j sign
  let corner := fun b j sign => (G b ⟨signedTubeCorner j sign,
    signedTubeRadius_subset_diamond j sign (right_mem_segment ℝ _ _)⟩ : D.sample → ℝ × V3)
  obtain ⟨_, hfaces⟩ := D.local_vertex_faces hcore v hv C hC hface haxis
  obtain ⟨hboundary, hne, hZ, axis, hAxis, hAxis0, hAxis1⟩ :=
    D.exists_local_axis_parameter hcore v hv s hs hcard hvs hdisj
  have hJV (b : Bool) : J b ⊆ V.space :=
    space_subset_of_le (D.complex.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr (hvs b)))
  have hJlink (b : Bool) : J b ⊆ (V.link v).space :=
    D.joint_subset_vertex_link (s b) (hs b) (hcard b) v (hvs b)
  have hRad (b : Bool) (j : Fin 2) (sign : Bool) (z : signedTubeDiamond) :
      (z : P2) ∈ signedTubeRadius j sign ↔ (G b z : D.sample → ℝ × V3) ∈ rad b j sign :=
    signedDiamond_coordinate_radius_iff (J b) c (G b) (hQ b) j sign z
  have hRadTarget (b : Bool) (j : Fin 2) (sign : Bool) : rad b j sign ⊆ J b :=
    fun _ hz => hz.1
  have hrad (b : Bool) (j : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (rad b j sign) {center b, corner b j sign} := by
    have h := isFinitePLBallPair_signed_diamond_radius_image (G b) (hG b) j sign
      (hRadTarget b j sign) (hRad b j sign)
    simpa only [hcenter] using h
  have hRadOuter (b : Bool) (j : Fin 2) (sign : Bool) : rad b j sign ⊆ outer j sign := by
    intro z hz
    exact ⟨⟨hJV b hz.1, hz.2.1, hz.2.2⟩, hJlink b hz.1⟩
  have hcorner (b : Bool) (j : Fin 2) (sign : Bool) : center b ≠ corner b j sign := by
    intro he
    have hx := (G b).injective (Subtype.ext ((hcenter b).trans he))
    exact signedTube_corner_ne_center j sign (congrArg Subtype.val hx).symm
  have houter (j : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (outer j sign) {center false, center true} := by
    have h := (hfaces j sign).2
    rw [hboundary] at h
    exact h
  have hcontact (j : Fin 2) (sign : Bool) : Z ∩ outer j sign = {center false, center true} := by
    rw [← hboundary]
    ext z
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, (hfaces j sign).1.1 (Or.inl h.1), h.2⟩⟩
  refine ⟨axis, hAxis, hAxis0, hAxis1, ?_⟩
  intro j sign
  have hrestr (b : Bool) := exists_signed_diamond_radius_restriction (G b) (hG b)
    j sign (hRadTarget b j sign) (hRad b j sign)
  choose radius hRadius hKeep using hrestr
  have hRa (b : Bool) : (radius b ⟨(0, 0), left_mem_segment ℝ _ _⟩ : D.sample → ℝ × V3) =
      center b := (hKeep b _).trans (hcenter b)
  have hRc (b : Bool) :
      (radius b ⟨signedTubeCorner j sign, right_mem_segment ℝ _ _⟩ : D.sample → ℝ × V3) =
        corner b j sign := hKeep b _
  obtain ⟨H, hH, hHA, hHE, hHZ, hHO, hHD⟩ := exists_signed_radius_prism_map
    j sign 0 1 zero_lt_one (fun b => rad b j sign) center (fun b => corner b j sign)
    (hfaces j sign).1 hZ (houter j sign) (hcontact j sign) (fun b => hrad b j sign)
    (fun b => hRadOuter b j sign) hne (fun b => hcorner b j sign)
    (hdisj.mono (hRadTarget false j sign) (hRadTarget true j sign))
    axis hAxis hAxis0 hAxis1 radius hRadius hRa hRc
  exact ⟨H, hH, hHA, fun b z => (hHE b z).trans (hKeep b z), hHZ, hHO, hHD⟩

end PoincareConjecture.M76.Dehn
