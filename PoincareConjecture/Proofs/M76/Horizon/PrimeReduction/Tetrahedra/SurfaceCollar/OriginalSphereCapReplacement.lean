import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalRetainedCapReplacement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBallPairRecognition

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "Source" => SProd.sprod Disk (Icc (-1 : ℝ) 1)

theorem exists_original_sphere_cap_replacement
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hP : MapsTo P.map Source (g '' K.space)) (hS : S ⊆ g '' K.space)
    (k q : Bool → Set V3)
    (hk : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (k b) (q b) ∧ k b ⊆ Sphere ∧
      s.map '' q b = P.capRimSet b ∧ (s.map '' k b) ∩ P.closedStrip = s.map '' q b) :
    ∃ f : V2 × ℝ → E, FinitePiecewiseAffineOn f Source ∧ InjOn f Source ∧
      MapsTo f Source K.space ∧ (∀ z ∈ Source, g (f z) = P.map z) ∧
      (∀ A : Set (V2 × ℝ), A ⊆ Source → f '' A = K.space ∩ g ⁻¹' (P.map '' A)) ∧
      ∀ b : Bool,
        let D := K.space ∩ g ⁻¹' (s.map '' k b)
        let r := K.space ∩ g ⁻¹' (s.map '' q b)
        let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
        let t := if b then (1/2 : ℝ) else -(1/2)
        let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
        IsFinitePLBallPair V2 D r ∧ g '' D = s.map '' k b ∧ g '' r = P.capRimSet b ∧
          ∃ H : (D ∪ f '' C : Set E) ≃ₜ (D ∪ f '' (Disk ×ˢ {t}) : Set E),
            H.IsFinitePL ∧ (∀ x : D, (H ⟨x,Or.inl x.property⟩ : E) = x) ∧
              (∀ x : (D ∪ f '' C : Set E), (H x : E) ∈ D ↔ (x : E) ∈ D) := by
  obtain ⟨f,hf,hfi,hfK,hfg,hcarrier,hreplace⟩ :=
    P.exists_original_retained_cap_replacement he K hK hg hgi hP
  refine ⟨f,hf,hfi,hfK,hfg,hcarrier,?_⟩
  intro b
  let D := K.space ∩ g ⁻¹' (s.map '' k b)
  let r := K.space ∩ g ⁻¹' (s.map '' q b)
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have himage (a : Set V3) (ha : a ⊆ Sphere) :
      g '' (K.space ∩ g ⁻¹' (s.map '' a)) = s.map '' a := by
    rw [image_inter_preimage]
    apply inter_eq_right.mpr
    rintro _ ⟨x,hx,rfl⟩
    apply hS
    rw [s.map_eq ⟨x,ha hx⟩]
    exact (s.parametrization ⟨x,ha hx⟩).property
  have hDimage : g '' D = s.map '' k b := himage _ (hk b).2.1
  have hrimage : g '' r = s.map '' q b := himage _ ((hk b).1.1.trans (hk b).2.1)
  have hkPL : PolyhedralPLInCharts e s.map (k b) := by
    obtain ⟨A,_,hA,hAs,_,_⟩ := (hk b).1.exists_finite_carrier_and_rim_complexes
    rw [←hAs]
    exact s.piecewiseAffine.restrict_finite A hA (hAs.subset.trans (hk b).2.1)
  have hD : IsFinitePLBallPair V2 D r :=
    isFinitePLBallPair_of_original_parametrization he K hK hg hgi inter_subset_left
      inter_subset_left ((hk b).1.model_equiv (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm)
      hkPL (hsi.mono (hk b).2.1) hDimage.symm hrimage.symm
  refine ⟨hD,hDimage,hrimage.trans (hk b).2.2.1,?_⟩
  apply hreplace b D r hD inter_subset_left
  rw [hDimage,(hk b).2.2.2,(hk b).2.2.1]

end PoincareConjecture.M76.OriginalDiskProduct
