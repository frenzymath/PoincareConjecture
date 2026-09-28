import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalProductCapCup
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Source" => SProd.sprod Disk (Icc (-1 : ℝ) 1)

theorem exists_original_finite_coordinates
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hP : MapsTo P.map Source (g '' K.space)) :
    ∃ f : V2 × ℝ → E, FinitePiecewiseAffineOn f Source ∧ InjOn f Source ∧
      MapsTo f Source K.space ∧ (∀ z ∈ Source, g (f z) = P.map z) ∧
      ∀ A : Set (V2 × ℝ), A ⊆ Source → f '' A = K.space ∩ g ⁻¹' (P.map '' A) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let H := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let pr : K.space ≃ₜ (g '' K.space) :=
    H.trans (Homeomorph.setCongr (image_eq_range g K.space).symm)
  let f : V2 × ℝ → E := fun z => if hz : z ∈ Source then pr.symm ⟨P.map z,hP hz⟩ else 0
  have hfval (z : Source) : f z = (pr.symm ⟨P.map z,hP z.property⟩ : E) := by
    simp only [f,dif_pos z.property]
  have hfK : MapsTo f Source K.space := by
    intro z hz
    rw [hfval ⟨z,hz⟩]
    exact (pr.symm ⟨P.map z,hP hz⟩).property
  have hvalue (z : V2 × ℝ) (hz : z ∈ Source) : g (f z) = P.map z := by
    rw [hfval ⟨z,hz⟩]
    exact congrArg Subtype.val (pr.apply_symm_apply ⟨P.map z,hP hz⟩)
  have hfc : ContinuousOn f Source := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := continuous_subtype_val.comp (pr.symm.continuous.comp
      (P.polyhedral.continuousOn.domRestrict.subtype_mk (fun z => hP z.property)))
    convert hc using 1
    funext z
    exact hfval z
  have hsource := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  obtain ⟨A,_,hA,hAs,_,_⟩ := hsource.exists_finite_carrier_and_rim_complexes
  have hf : FinitePiecewiseAffineOn f Source := by
    rw [←hAs]
    exact hg.finitePiecewiseAffineOn_lift he hgi A hA
      (hfc.mono hAs.subset) (fun _ hz => hfK (hAs.subset hz))
      ((P.polyhedral.restrict_finite A hA hAs.subset).congr
        (fun z hz => (hvalue z (hAs.subset hz)).symm))
  refine ⟨f,hf,?_,hfK,hvalue,?_⟩
  · intro x hx y hy hxy
    exact P.injective hx hy ((hvalue x hx).symm.trans ((congrArg g hxy).trans (hvalue y hy)))
  · intro A hAS
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨hfK (hAS hz),⟨z,hz,(hvalue z (hAS hz)).symm⟩⟩
    · rintro x ⟨hx,z,hz,hzx⟩
      exact ⟨z,hz,hgi (hfK (hAS hz)) hx ((hvalue z (hAS hz)).trans hzx)⟩

end PoincareConjecture.M76.OriginalDiskProduct
