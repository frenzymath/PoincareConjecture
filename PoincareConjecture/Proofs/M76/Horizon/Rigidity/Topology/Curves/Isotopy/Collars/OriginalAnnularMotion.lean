import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalRegionMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Original.SurfaceMotion

set_option autoImplicit false
open Set Geometry PLAnnularStrip unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

open PoincareConjecture.M76.Dehn
local notation "Ann" => squareAnnulus 8 1
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_annular_collar_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U B : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U)
    (A : Ann ≃ₜ B) (hBS : B ⊆ frontier R) (hB : IsClosed B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ z : Ann, j z = (A z : X))
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A))
    (H : I → Ann ≃ₜ Ann)
    (hc : Continuous (fun z : I × Ann => H z.1 z.2))
    (hci : Continuous (fun z : I × Ann => (H z.1).symm z.2))
    (hzero : ∀ x : Ann, H 0 x = x)
    (hfix : ∀ t (x : Ann), depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → H t x = x)
    (track : (ℝ × (ℝ × ℝ)) → (ℝ × ℝ))
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ Ann))
    (hvalue : ∀ t : I, ∀ x : Ann, track ((t : ℝ), x) = (H t x : ℝ × ℝ)) :
    ∃ G : I → R ≃ₜ R,
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ChartwisePLHomeomorph e e (G t)) ∧
      (∀ t : I, ∀ z : Ann,
        (G t ⟨A z, he.closed.frontier_subset (hBS (A z).property)⟩ : X) = A (H t z)) ∧
      (∀ t : I, ∀ x : R, (x : X) ∉ U → G t x = x) ∧
      (∀ t : I, ∀ x : R, (x : X) ∈ frontier R →
        (x : X) ∉ originalAnnulusOpenMark A → G t x = x) := by
  classical
  obtain ⟨s, K, HB, c, delta, hK, hd, _, hcPL, _, _, _, hbase, hmotion⟩ :=
    exists_prepared_original_boundary_collar_motion he hR hne hU hBU
  let f (x : s → ℝ × V3) : X := c (x, 0)
  let sectionMap : (s → ℝ × V3) →ᴬ[ℝ] ((s → ℝ × V3) × ℝ) :=
    (ContinuousAffineMap.id ℝ (s → ℝ × V3)).prod (ContinuousAffineMap.const ℝ _ 0)
  have hf : PolyhedralPLInCharts e f K.space :=
    hcPL.comp_finitePiecewiseAffineOn K hK
      (K.affineOnFaces_affine sectionMap |>.finitePiecewiseAffineOn hK)
      (fun x hx => ⟨hx, le_rfl, hd.le⟩)
  have hfv (x : K.space) : f x = (HB x : X) := hbase x
  obtain ⟨C, hCK, q, _, hC, hq, _, _, hqval, _⟩ :=
    exists_finitePL_original_annular_coordinates e he.compatible HB f hf hfv A hBS j hj hjval
  let hopenq := isOpen_original_annular_coordinate_mark HB A q hCK hqval hopen
  let J (t : I) := originalAnnularExtension q hCK hC hopenq (H t) (hfix t)
  have hJc : Continuous (fun z : I × K.space => J z.1 z.2) :=
    continuous_originalAnnularExtension q hCK hC hopenq H hc hfix
  have hJci : Continuous (fun z : I × K.space => (J z.1).symm z.2) :=
    continuous_originalAnnularExtension_symm q hCK hC hopenq H hci hfix
  have hJzero : ∀ x : K.space, J 0 x = x := by
    intro x
    change originalAnnularExtension q hCK hC hopenq (H 0) (hfix 0) x = x
    rw [originalAnnularExtension_eq_refl q hCK hC hopenq (H 0) (hfix 0) hzero]
    rfl
  obtain ⟨g, hg, hgv⟩ := exists_originalAnnularExtension_joint_finitePL
    K hK q hq hCK hC hopenq H hc hfix track htrack hvalue
  obtain ⟨G, hGc, hGci, hGzero, hGPL, houter, hout, _, _⟩ :=
    hmotion J hJc hJci hJzero g hg hgv
  have hboundary (t : I) (x : frontier R) :
      (G t ⟨x, he.closed.frontier_subset x.property⟩ : X) =
        (originalAnnularExtension A hBS hB hopen (H t) (hfix t) x : X) := by
    have h := houter t (HB.symm x)
    have hx : (⟨HB (HB.symm x), he.closed.frontier_subset (HB (HB.symm x)).property⟩ : R) =
        ⟨x, he.closed.frontier_subset x.property⟩ :=
      Subtype.ext (congrArg (fun y : frontier R => (y : X)) (HB.apply_symm_apply x))
    rw [hx] at h
    rw [h]
    exact congrArg Subtype.val (by
      simpa only [HB.apply_symm_apply] using
        originalAnnularExtension_conjugacy HB A q hCK hBS hC hB hqval hopen
          (H t) (hfix t) (HB.symm x))
  refine ⟨G, hGc, hGci, hGzero, hGPL, ?_, hout, ?_⟩
  · intro t z
    rw [hboundary t ⟨A z, hBS (A z).property⟩,
      originalAnnularExtension_apply]
  · intro t x hx hmark
    apply Subtype.ext
    rw [hboundary t ⟨x, hx⟩,
      originalAnnularExtension_fixed_off_mark A hBS hB hopen (H t) (hfix t) ⟨x, hx⟩ hmark]

end PoincareConjecture.M76.CollarIsotopy
