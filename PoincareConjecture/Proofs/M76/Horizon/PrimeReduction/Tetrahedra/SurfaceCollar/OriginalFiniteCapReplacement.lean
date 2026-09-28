import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalProductFiniteCoordinates

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Source" => SProd.sprod Disk (Icc (-1 : ℝ) 1)

theorem exists_original_finite_cap_replacement
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
      (∀ A : Set (V2 × ℝ), A ⊆ Source → f '' A = K.space ∩ g ⁻¹' (P.map '' A)) ∧
      ∀ b : Bool,
        let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
        let t := if b then (1/2 : ℝ) else -(1/2)
        let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
        IsFinitePLBallPair V2 (f '' C) (f '' (Rim ×ˢ {t})) ∧
          IsFinitePLBallPair V2 (f '' (Disk ×ˢ {t})) (f '' (Rim ×ˢ {t})) ∧
          ∃ H : (f '' C) ≃ₜ (f '' (Disk ×ˢ {t})), H.IsFinitePL ∧
            ∀ x : (f '' C), (x : E) ∈ f '' (Rim ×ˢ {t}) → (H x : E) = x := by
  obtain ⟨f,hf,hfi,hfK,hfg,hcarrier⟩ := P.exists_original_finite_coordinates he K hK hg hgi hP
  refine ⟨f,hf,hfi,hfK,hfg,hcarrier,?_⟩
  intro b
  let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
  let t := if b then (1/2 : ℝ) else -(1/2)
  let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
  obtain ⟨hC,_,_,_,H,hH,hHfix,_⟩ := P.exists_original_product_cap_replacement b
  have hCsub : C ⊆ Source := by
    rintro ⟨x,u⟩ (⟨hx,hu⟩ | ⟨hx,hu⟩)
    · exact ⟨hx,by rw [show u = 0 from hu]; norm_num⟩
    · refine ⟨sphere_subset_closedBall hx,?_⟩
      cases b <;> dsimp [I] at hu <;> constructor <;> linarith [hu.1,hu.2]
  have hEnd : IsFinitePLBallPair V2 (Disk ×ˢ {t}) (Rim ×ˢ {t}) :=
    isFinitePLBallPair_unit_cube.prod_singleton t
  have hEndsub : Disk ×ˢ {t} ⊆ Source := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    refine ⟨hx,?_⟩
    rw [show u = t from hu]
    cases b <;> norm_num [t]
  have hfC : FinitePiecewiseAffineOn f C := by
    obtain ⟨A,_,hA,hAs,_,_⟩ := hC.exists_finite_carrier_and_rim_complexes
    change A.space = C at hAs
    rw [←hAs]
    exact hf.restrict A hA (hAs.subset.trans hCsub)
  have hfEnd : FinitePiecewiseAffineOn f (Disk ×ˢ {t}) := by
    obtain ⟨A,_,hA,hAs,_,_⟩ := hEnd.exists_finite_carrier_and_rim_complexes
    rw [←hAs]
    exact hf.restrict A hA (hAs.subset.trans hEndsub)
  obtain ⟨A,hA,hAval⟩ := hfC.exists_homeomorph_image (hfi.mono hCsub)
  obtain ⟨B,hB,hBval⟩ := hfEnd.exists_homeomorph_image (hfi.mono hEndsub)
  let G := A.symm.trans (H.trans B)
  have hG : G.IsFinitePL := hA.symm.trans (hH.trans hB)
  refine ⟨hC.image hfC (hfi.mono hCsub),hEnd.image hfEnd (hfi.mono hEndsub),G,hG,?_⟩
  intro x hx
  obtain ⟨z,hz,hzx⟩ := hx
  have hzC : z ∈ C := hC.1 hz
  have hAz : A ⟨z,hzC⟩ = x := Subtype.ext ((hAval _).trans hzx)
  have hAinv : A.symm x = ⟨z,hzC⟩ := by rw [←hAz,A.symm_apply_apply]
  change (B (H (A.symm x)) : E) = x
  rw [hBval,hAinv,hHfix ⟨z,hzC⟩ hz]
  exact hzx

end PoincareConjecture.M76.OriginalDiskProduct
