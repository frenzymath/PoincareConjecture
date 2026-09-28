import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.DiskContactSourceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.RetainedCharts



set_option autoImplicit false
open Set Metric Geometry Topology
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem essential_disk_minimum_in_planar_coordinates
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R T : Set X}
    (f : V2 → X)
    (hminimum : ∀ k : V2 → X,
      PolyhedralPLInCharts e k D2 → IsEmbedding (fun x : D2 => k x) →
      MapsTo k D2 R → (∀ x : D2,k x ∈ frontier R ↔ (x : V2) ∈ Q2) →
      (¬∃ F : C(D2,frontier R),∀ x : Q2,
        (F ⟨x,sphere_subset_closedBall x.property⟩ : X) = k x) →
      (∀ y ∈ T ∩ frontier R,y ∈ k '' D2 →
        ∃ C : OriginalSurfacePairChart e T (k '' D2) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔ 0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔ (C.coordinates v).1.2 = 0) →
      (∀ y ∈ T ∩ interior R,y ∈ k '' D2 →
        Nonempty (OriginalSurfacePairChart e T (k '' D2) y false)) →
      Nat.card (ConnectedComponents (D2 ∩ f ⁻¹' T : Set V2)) ≤
        Nat.card (ConnectedComponents (D2 ∩ k ⁻¹' T : Set V2)))
    (J : SimplicialComplex ℝ P2)
    (hJs : J.space = (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) '' D2)
    (k : P2 → X) (hk : PolyhedralPLInCharts e k J.space)
    (hki : IsEmbedding (fun x : J.space => k x)) (hkR : MapsTo k J.space R)
    (hkproper : ∀ x ∈ J.space,k x ∈ frontier R ↔ x ∈ frontier J.space)
    (hkno : ¬∃ F : C(J.space,frontier R),∀ x : J.space,
      (x : P2) ∈ frontier J.space → (F x : X) = k x)
    (hboundary : ∀ x ∈ J.space,k x ∈ T → k x ∈ frontier R →
      ∃ C : OriginalSurfacePairChart e (k '' J.space) T (k x) true,
        (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔ 0 ≤ (C.coordinates v).1.2) ∧
        ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔ (C.coordinates v).1.2 = 0)
    (hinterior : ∀ x ∈ J.space,k x ∈ T → k x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (k '' J.space) T (k x) false)) :
    Nat.card (ConnectedComponents
      (J.space ∩ (f ∘ (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm) ⁻¹' T : Set P2)) ≤
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' T : Set P2)) := by
  let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  change J.space = a '' D2 at hJs
  have hforward (x : V2) (hx : x ∈ D2) : a x ∈ J.space := hJs.symm.subset ⟨x,hx,rfl⟩
  have hback (x : P2) (hx : x ∈ J.space) : a.symm x ∈ D2 := by
    obtain ⟨y,hy,rfl⟩ := hJs.subset hx
    simpa using hy
  have hJfront : frontier J.space = a '' Q2 := by
    rw [hJs]
    change frontier (a.toHomeomorph '' D2) = a.toHomeomorph '' Q2
    rw [←a.toHomeomorph.image_frontier,frontier_closedBall _ (by norm_num : (1:ℝ) ≠ 0)]
  have hbackfront (x : P2) : x ∈ frontier J.space ↔ a.symm x ∈ Q2 := by
    rw [hJfront]
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨a.symm x,hx,a.apply_symm_apply x⟩
  let k0 : V2 → X := k ∘ a
  have hkimage : k0 '' D2 = k '' J.space := by rw [image_comp,←hJs]
  obtain ⟨J0,_,hJ0,hJ0s,_,_⟩ := (isFinitePLBallPair_unit_cube (ι := Fin 2)).exists_finite_carrier_and_rim_complexes
  have hk0 : PolyhedralPLInCharts e k0 D2 := by
    rw [←hJ0s]
    exact hk.comp_finitePiecewiseAffineOn J0 hJ0
      ((J0.affineOnFaces_affine a.toContinuousLinearMap.toContinuousAffineMap).finitePiecewiseAffineOn hJ0)
      (fun x hx => hforward x (hJ0s.subset hx))
  let H : D2 ≃ₜ J.space := (a.toHomeomorph.image D2).trans (Homeomorph.setCongr hJs.symm)
  have hk0i : IsEmbedding (fun x : D2 => k0 x) := hki.comp H.isEmbedding
  have hk0R : MapsTo k0 D2 R := fun x hx => hkR (hforward x hx)
  have hk0proper : ∀ x : D2,k0 x ∈ frontier R ↔ (x : V2) ∈ Q2 := by
    intro x
    exact (hkproper (a x) (hforward x x.property)).trans
      ((hbackfront (a x)).trans (by simp))
  have hk0no : ¬∃ F : C(D2,frontier R),∀ x : Q2,
      (F ⟨x,sphere_subset_closedBall x.property⟩ : X) = k0 x := by
    rintro ⟨F,hF⟩
    let G : C(J.space,frontier R) := F.comp ⟨H.symm,H.symm.continuous⟩
    refine hkno ⟨G,?_⟩
    intro x hx
    have hxQ := (hbackfront x).mp hx
    have hh := hF ⟨a.symm x,hxQ⟩
    change (F ⟨a.symm x,hback x x.property⟩ : X) = k x
    simpa only [k0,Function.comp_apply,a.apply_symm_apply] using hh
  have hk0bc : ∀ y ∈ T ∩ frontier R,y ∈ k0 '' D2 →
      ∃ C : OriginalSurfacePairChart e T (k0 '' D2) y true,
        (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔ 0 ≤ (C.coordinates v).1.2) ∧
        ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔ (C.coordinates v).1.2 = 0 := by
    intro y hy hyk
    obtain ⟨x,hx,rfl⟩ := hkimage.subset hyk
    obtain ⟨C,hCR,hCF⟩ := hboundary x hx hy.1 hy.2
    rw [hkimage]
    exact C.swap_boundary_region hCR hCF
  have hk0ic : ∀ y ∈ T ∩ interior R,y ∈ k0 '' D2 →
      Nonempty (OriginalSurfacePairChart e T (k0 '' D2) y false) := by
    intro y hy hyk
    obtain ⟨x,hx,rfl⟩ := hkimage.subset hyk
    obtain ⟨C⟩ := hinterior x hx hy.1 hy.2
    simpa only [hkimage] using (show Nonempty
      (OriginalSurfacePairChart e T (k '' J.space) (k x) false) from ⟨C.swap⟩)
  have hmin := hminimum k0 hk0 hk0i hk0R hk0proper hk0no hk0bc hk0ic
  have hcountf := contact_component_card_source_homeomorph a.toHomeomorph D2 f T
  have hcountk := contact_component_card_source_homeomorph a.toHomeomorph D2 k0 T
  change Nat.card (ConnectedComponents ((a '' D2) ∩ (k0 ∘ a.symm) ⁻¹' T : Set P2)) = _ at hcountk
  change Nat.card (ConnectedComponents ((a '' D2) ∩ (f ∘ a.symm) ⁻¹' T : Set P2)) = _ at hcountf
  have hkcomp : k0 ∘ a.symm = k := by
    funext x
    simp [k0]
  rw [hkcomp,←hJs] at hcountk
  rw [←hJs] at hcountf
  change Nat.card (ConnectedComponents (J.space ∩ (f ∘ a.symm) ⁻¹' T : Set P2)) ≤ _
  rw [hcountf,hcountk]
  exact hmin

end PoincareConjecture.M76
