import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalFiniteCapReplacement
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Source" => SProd.sprod Disk (Icc (-1 : ℝ) 1)

theorem exists_original_retained_cap_replacement
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
      ∀ (b : Bool) (D r : Set E), IsFinitePLBallPair V2 D r → D ⊆ K.space →
        (g '' D) ∩ P.closedStrip = P.capRimSet b →
        let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
        let t := if b then (1/2 : ℝ) else -(1/2)
        let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
        ∃ H : (D ∪ f '' C : Set E) ≃ₜ (D ∪ f '' (Disk ×ˢ {t}) : Set E), H.IsFinitePL ∧
          (∀ x : D, (H ⟨x,Or.inl x.property⟩ : E) = x) ∧
          (∀ x : (D ∪ f '' C : Set E), (H x : E) ∈ D ↔ (x : E) ∈ D) := by
  obtain ⟨f,hf,hfi,hfK,hfg,hcarrier,hreplace⟩ :=
    P.exists_original_finite_cap_replacement he K hK hg hgi hP
  refine ⟨f,hf,hfi,hfK,hfg,hcarrier,?_⟩
  intro b D r hD hDK hcontact
  let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
  let t := if b then (1/2 : ℝ) else -(1/2)
  let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
  let T := Disk ×ˢ {t}
  let Q := Rim ×ˢ {t}
  have ht : t ∈ Icc (-(1/2 : ℝ)) (1/2) := by cases b <;> norm_num [t]
  have hQsub : Q ⊆ Source := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    refine ⟨sphere_subset_closedBall hx,?_⟩
    rw [show u = t from hu]
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hQC : Q ⊆ C := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    refine Or.inr ⟨hx,?_⟩
    rw [show u = t from hu]
    cases b <;> norm_num [t,I]
  have hQT : Q ⊆ T := prod_mono sphere_subset_closedBall (Subset.refl _)
  have hCstrip : C ⊆ Disk ×ˢ Icc (-(1/2 : ℝ)) (1/2) := by
    rintro ⟨x,u⟩ (⟨hx,hu⟩ | ⟨hx,hu⟩)
    · exact ⟨hx,by rw [show u = 0 from hu]; norm_num⟩
    · refine ⟨sphere_subset_closedBall hx,?_⟩
      cases b <;> dsimp [I] at hu <;> constructor <;> linarith [hu.1,hu.2]
  have hTstrip : T ⊆ Disk ×ˢ Icc (-(1/2 : ℝ)) (1/2) := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    exact ⟨hx,by simpa only [show u = t from hu] using ht⟩
  have hstripSub : Disk ×ˢ Icc (-(1/2 : ℝ)) (1/2) ⊆ Source := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    exact ⟨hx,by constructor <;> linarith [hu.1,hu.2]⟩
  have hDQ : f '' Q ⊆ D := by
    intro x hx
    have hx' := (hcarrier Q hQsub).subset hx
    have hxcap : g x ∈ P.capRimSet b := hx'.2
    obtain ⟨y,hy,hyx⟩ := (hcontact.symm.subset hxcap).1
    exact (hgi (hDK hy) hx'.1 hyx) ▸ hy
  have hDA (A : Set (V2 × ℝ))
      (hA : A ⊆ Disk ×ˢ Icc (-(1/2 : ℝ)) (1/2)) (hQA : Q ⊆ A) :
      D ∩ f '' A = f '' Q := by
    apply Subset.antisymm
    · rintro x ⟨hxD,hxA⟩
      have hx' := (hcarrier A (hA.trans hstripSub)).subset hxA
      have hxcap : g x ∈ P.capRimSet b :=
        hcontact.subset ⟨mem_image_of_mem g hxD,image_mono hA hx'.2⟩
      exact (hcarrier Q hQsub).symm.subset ⟨hDK hxD,hxcap⟩
    · exact fun x hx => ⟨hDQ hx,image_mono hQA hx⟩
  have hDC := hDA C hCstrip hQC
  have hDT := hDA T hTstrip hQT
  obtain ⟨_,_,H,hH,hHfix⟩ := hreplace b
  have hid : (Homeomorph.refl D).IsFinitePL := by
    obtain ⟨A,_,hA,hAs,_,_⟩ := hD.exists_finite_carrier_and_rim_complexes
    exact ⟨id,⟨A,hA,hAs,A.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,
      fun _ => rfl⟩
  obtain ⟨G,hG,hGid,hGH⟩ := (Homeomorph.refl D).exists_union_finitePL H hid hH
    (by
      intro x
      change (x : E) ∈ f '' C ↔ (x : E) ∈ f '' T
      constructor
      · intro hx
        exact (hDT.symm.subset (hDC.subset ⟨x.property,hx⟩)).2
      · intro hx
        exact (hDC.symm.subset (hDT.subset ⟨x.property,hx⟩)).2)
    (by
      intro x hxD hxC
      exact (hHfix ⟨x,hxC⟩ (hDC.subset ⟨hxD,hxC⟩)).symm)
  refine ⟨G,hG,hGid,?_⟩
  intro x
  constructor
  · intro hx
    have heq : G ⟨(G x : E),Or.inl hx⟩ = G x := Subtype.ext (hGid ⟨G x,hx⟩)
    have := congrArg Subtype.val (G.injective heq)
    exact this ▸ hx
  · intro hx
    have heq : (G x : E) = x := hGid ⟨x,hx⟩
    exact heq.symm ▸ hx

end PoincareConjecture.M76.OriginalDiskProduct
