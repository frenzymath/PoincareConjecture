import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ExtendedProtectedProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.MarkedProductInteriorChart



set_option autoImplicit false
noncomputable section
open Set Metric Geometry

namespace PoincareConjecture.M76.ProtectedProductExtension
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set P2)
local notation "Cube" => (Square ×ˢ I : Set P3)
local notation "Extended" => (Set.prod Square (Icc (-2 : ℝ) 2) : Set P3)
local notation "OpenCube" => (Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1))
local notation "OpenExtended" => (Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-2 : ℝ) 2))

def stretch : P3 ≃ᴬ[ℝ] P3 :=
  ((ContinuousLinearEquiv.refl ℝ P2).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ (2 : ℝ) (by norm_num)).toContinuousLinearEquiv).toContinuousAffineEquiv

theorem stretch_apply (z : P3) : stretch z = (z.1, 2 * z.2) := rfl

theorem stretch_image_cube : stretch '' Cube = Extended := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw.1, by change -2 ≤ 2 * w.2 ∧ 2 * w.2 ≤ 2; constructor <;> linarith [hw.2.1, hw.2.2]⟩
  · intro hz
    refine ⟨(z.1, z.2 / 2), ⟨hz.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hz.2.1, hz.2.2]
    · rw [stretch_apply]
      apply Prod.ext
      · rfl
      · change 2 * (z.2 / 2) = z.2
        ring

def extendedCoordinates : V3 ≃ᴬ[ℝ] P3 := markedProductCoordinates.trans stretch

theorem extendedCoordinates_apply (z : V3) :
    extendedCoordinates z = ((z 0, z 1), 2 * z 2) := rfl

theorem extendedCoordinates_preimage_open :
    extendedCoordinates ⁻¹' OpenExtended = markedProductCoordinates ⁻¹' OpenCube := by
  ext z
  change (((-1 < z 0 ∧ z 0 < 1) ∧ (-1 < z 1 ∧ z 1 < 1)) ∧
    (-2 < 2 * z 2 ∧ 2 * z 2 < 2)) ↔
    (((-1 < z 0 ∧ z 0 < 1) ∧ (-1 < z 1 ∧ z 1 < 1)) ∧ (-1 < z 2 ∧ z 2 < 1))
  constructor <;> intro h <;> refine ⟨h.1, ?_, ?_⟩ <;> linarith [h.2.1, h.2.2]

theorem exists_compatible_chart {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (q : P3 → X) (hq : PolyhedralPLInCharts e q Extended) (hqi : InjOn q Extended) :
    ∃ Q : OpenPartialHomeomorph X V3,
      Q.source = interior (q '' Extended) ∧
      Q.target = extendedCoordinates ⁻¹' OpenExtended ∧
      (∀ y, Q.symm y = q (extendedCoordinates y)) ∧
      ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
  let p := q ∘ stretch
  have hs : MapsTo stretch Cube Extended := fun z hz => stretch_image_cube.subset ⟨z, hz, rfl⟩
  have hp : PolyhedralPLInCharts e p Cube := by
    obtain ⟨K, _, hK, hKs, _, _⟩ :=
      (((isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).prod
        (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).prod
          (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).exists_finite_carrier_and_rim_complexes
    rw [← hKs]
    exact hq.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine stretch.toContinuousAffineMap).finitePiecewiseAffineOn hK)
      (fun z hz => hs (hKs.subset hz))
  have hpi : InjOn p Cube := hqi.comp stretch.injective.injOn hs
  have himage : p '' Cube = q '' Extended := by
    rw [image_comp, stretch_image_cube]
  have hcompact : IsCompact Cube := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  let : CompactSpace Cube := isCompact_iff_compactSpace.mp hcompact
  have hemb : Topology.IsEmbedding (fun z : Cube => p z) :=
    (hp.continuousOn.domRestrict.isClosedEmbedding (fun x y h =>
      Subtype.ext (hpi x.property y.property h))).isEmbedding
  have hdim : Module.finrank ℝ P3 = Module.finrank ℝ V3 := by simp
  have hclosed : IsClosed (p '' Cube) := (hcompact.image_of_continuousOn hp.continuousOn).isClosed
  have hboundary (z : P3) (hz : z ∈ Cube) :
      p z ∈ frontier (p '' Cube) ↔ z ∈ frontier Cube := by
    rw [frontier, hclosed.closure_eq, frontier, hcompact.isClosed.closure_eq]
    simp only [mem_sdiff, mem_image_of_mem p hz, hz, true_and]
    exact not_congr (hp.mem_interior_image_iff hdim hemb ⟨z, hz⟩)
  obtain ⟨Q, hsource, htarget, hval, htrans⟩ :=
    exists_marked_product_interior_chart he p hp hpi rfl hboundary
  change Q.source = interior (p '' Cube) at hsource
  rw [himage] at hsource
  refine ⟨Q, hsource, htarget.trans extendedCoordinates_preimage_open.symm, ?_, htrans⟩
  intro y
  exact hval y

end PoincareConjecture.M76.ProtectedProductExtension
