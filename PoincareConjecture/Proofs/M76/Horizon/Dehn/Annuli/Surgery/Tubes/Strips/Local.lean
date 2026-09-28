import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.LocalBranchInverses
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalSourceStrips
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTubeSigns









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
  {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}



theorem RawSourceCrossing.eq_of_coordinate_ne
    {x y : E} (C : RawSourceCrossing e f S R x y)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S)
    (hpoint : f a ∈ C.chart.source) (hab : f a = f b)
    (hne : C.chart (f a) 0 ≠ 0 ∨ C.chart (f a) 1 ≠ 0) : a = b := by
  have hA := C.whole_preimage.subset ⟨ha, hpoint⟩
  have hB := C.whole_preimage.subset ⟨hb, show f b ∈ C.chart.source from hab ▸ hpoint⟩
  have hinjL : InjOn f C.left := by
    intro u hu v hv huv
    exact congrArg Subtype.val (C.left_embedding.injective
      (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) huv)
  have hinjR : InjOn f C.right := by
    intro u hu v hv huv
    exact congrArg Subtype.val (C.right_embedding.injective
      (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) huv)
  rcases hne with hn | hn
  · have hAL : a ∉ C.left := fun h => hn ((C.left_image _ hpoint).mp ⟨a, h, rfl⟩).1
    have hBL : b ∉ C.left := fun h => hn ((C.left_image _ hpoint).mp ⟨b, h, hab.symm⟩).1
    exact hinjR (hA.resolve_left hAL) (hB.resolve_left hBL) hab
  · have hAR : a ∉ C.right := fun h => hn ((C.right_image _ hpoint).mp ⟨a, h, rfl⟩).1
    have hBR : b ∉ C.right := fun h => hn ((C.right_image _ hpoint).mp ⟨b, h, hab.symm⟩).1
    exact hinjL (hA.resolve_right hAR) (hB.resolve_right hBR) hab



theorem ComponentBranchModel.exists_local_source_strip
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hcore : D.core ⊆ interior R)
    (L : SimplicialComplex ℝ (D.sample → ℝ × V3)) (hL : L.faces.Finite)
    (hLK : L.space ⊆ D.complex.space)
    {x y : E} (C : RawSourceCrossing e f S R x y)
    (hLC : MapsTo (fun z ↦ (D.inverse z : X)) L.space C.chart.source)
    {a b : ℝ} (hab : a < b)
    (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (hsigma : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc a b))
    (himage : MapsTo sigma (signedTubeDiamond ×ˢ Icc a b) L.space)
    (j k : Fin 2)
    (hsheet : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      C.chart (D.inverse (sigma (signedSheetStripMap j z))) k.castSucc = 0) :
    ∃ phi : P2 → E,
      FinitePiecewiseAffineOn phi (Icc (-1 : ℝ) 1 ×ˢ Icc a b) ∧
      ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
        phi z ∈ S ∧ phi z ∈ (if k = 0 then C.left else C.right) ∧
        f (phi z) = (D.inverse (sigma (signedSheetStripMap j z)) : X) ∧
        D.graph (f (phi z)) = sigma (signedSheetStripMap j z) ∧
        ∀ w ∈ (if k = 0 then C.left else C.right),
          f w = (D.inverse (sigma (signedSheetStripMap j z)) : X) → w = phi z := by
  classical
  obtain ⟨P, u, _hP, hPs, huPL, hu, _huinv, _hcover⟩ :=
    D.exists_local_branch_inverses L hL hLK C hLC
  let q : Bool := decide (k = 1)
  have hq : (if q then (1 : Fin 3) else 0) = k.castSucc := by
    fin_cases k <;> rfl
  have hbranch : (if q then C.right else C.left) =
      (if k = 0 then C.left else C.right) := by
    fin_cases k <;> rfl
  obtain ⟨v, hv, hvvalue⟩ := (huPL q).1
  let phi := v ∘ sigma ∘ signedSheetStripMap j
  have hsheet' (z : P2) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
      sigma (signedSheetStripMap j z) ∈ L.space ∩
        {w | (D.inverse w : X) ∈ R ∧ C.chart (D.inverse w) (if q then 1 else 0) = 0} := by
    refine ⟨himage (signedSheetStripMap_mem j hz), interior_subset (hcore (D.inverse _).property), ?_⟩
    rw [hq]
    exact hsheet z hz
  have hphi (z : P2) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
      phi z = (u q ⟨sigma (signedSheetStripMap j z), hsheet' z hz⟩ : E) :=
    (hvvalue ⟨sigma (signedSheetStripMap j z), hsheet' z hz⟩).symm
  refine ⟨phi, hv.comp (hsigma.comp (signedSheetStripMap_finitePL hab j)
    (fun _ hz => signedSheetStripMap_mem j hz)) hsheet', ?_⟩
  intro z hz
  have hmem := (hPs q).subset (u q ⟨_, hsheet' z hz⟩).property
  dsimp only at hmem
  rw [← hphi z hz, hbranch] at hmem
  have hvalue := hu q ⟨_, hsheet' z hz⟩
  rw [← hphi z hz] at hvalue
  refine ⟨hmem.1.1, hmem.2, hvalue.1, hvalue.2, ?_⟩
  intro w hw hwf
  have heq : f w = f (phi z) := hwf.trans hvalue.1.symm
  fin_cases k
  · exact congrArg Subtype.val (C.left_embedding.injective
      (a₁ := ⟨w, hw⟩) (a₂ := ⟨phi z, hmem.2⟩) heq)
  · exact congrArg Subtype.val (C.right_embedding.injective
      (a₁ := ⟨w, hw⟩) (a₂ := ⟨phi z, hmem.2⟩) heq)

end PoincareConjecture.M76.Dehn.Annuli

