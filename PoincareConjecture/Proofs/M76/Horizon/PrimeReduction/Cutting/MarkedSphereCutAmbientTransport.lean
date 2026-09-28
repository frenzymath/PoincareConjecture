import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.RelativeCutAmbientTransport



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

noncomputable def MarkedSphereCut.image
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (c : MarkedSphereCut e R κ) (F : X ≃ₜ X) (hFR : F '' R = R)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) : MarkedSphereCut e R κ := by
  classical
  have hFi : F '' interior R = interior R := by rw [F.image_interior,hFR]
  have hFfront : F '' frontier R = frontier R := by rw [F.image_frontier,hFR]
  have hcarrier : F '' c.carrier = R \ ⋃ i, F '' c.collar i := by
    rw [MarkedSphereCut.carrier,image_sdiff F.injective,image_iUnion,hFR]
  let W (i) : ((F '' c.spheres i) × unitInterval) ≃ₜ closure (F '' c.collar i) :=
    ((F.image (c.spheres i)).symm.prodCongr (Homeomorph.refl unitInterval)).trans
      ((c.product i).trans ((F.image (closure (c.collar i))).trans
        (Homeomorph.setCongr (F.image_closure _))))
  let B (b : κ × Bool) : (F '' c.spheres b.1) ≃ₜ (F '' c.ports b) :=
    (F.image (c.spheres b.1)).symm.trans ((c.portMap b).trans (F.image (c.ports b)))
  refine {
    spheres := fun i => F '' c.spheres i
    spherePL := fun i => Classical.choice ((c.spherePL i).nonempty_image F c.plCut.cover hF)
    sphereInterior := ?_
    sphereDisjoint := ?_
    collar := fun i => F '' c.collar i
    product := W
    collarOpen := fun i => F.isOpenMap _ (c.collarOpen i)
    collarInterior := ?_
    collarDisjoint := ?_
    openCoordinates := ?_
    centerCoordinates := ?_
    sphereClosure := ?_
    ports := fun b => F '' c.ports b
    portMap := B
    portPL := fun b => Classical.choice ((c.portPL b).nonempty_image F c.plCut.cover hF)
    portDisjoint := ?_
    portClosure := ?_
    collarContact := ?_
    endpoints := ?_
    center := ?_
    compactCut := hcarrier ▸ c.compactCut.image F.continuous
    plCut := hcarrier ▸ c.plCut.image_of_original_atlas_move F hF
    frontierCut := ?_ }
  · intro i
    rw [←hFi]
    exact image_mono (c.sphereInterior i)
  · intro i j hij
    exact (c.sphereDisjoint hij).image F.injective.injOn (subset_univ _) (subset_univ _)
  · intro i
    rw [←F.image_closure,←hFi]
    exact image_mono (c.collarInterior i)
  · intro i j hij
    rw [←F.image_closure,←F.image_closure]
    exact (c.collarDisjoint hij).image F.injective.injOn (subset_univ _) (subset_univ _)
  · intro i z
    change F (c.product i ((F.image (c.spheres i)).symm z.1,z.2)) ∈ F '' c.collar i ↔ _
    rw [F.injective.mem_set_image]
    exact c.openCoordinates i _
  · intro i z
    change F (c.product i ((F.image (c.spheres i)).symm z.1,z.2)) ∈ F '' c.spheres i ↔ _
    rw [F.injective.mem_set_image]
    exact c.centerCoordinates i _
  · intro i
    rw [←F.image_closure]
    exact image_mono (c.sphereClosure i)
  · intro i j hij
    exact (c.portDisjoint hij).image F.injective.injOn (subset_univ _) (subset_univ _)
  · intro b
    rw [←F.image_closure]
    exact image_mono (c.portClosure b)
  · intro i
    rw [←hcarrier,←F.image_closure,←image_inter F.injective,MarkedSphereCut.carrier,
      c.collarContact,image_union]
  · intro i x
    exact ⟨congrArg F (c.endpoints i ((F.image (c.spheres i)).symm x)).1,
      congrArg F (c.endpoints i ((F.image (c.spheres i)).symm x)).2⟩
  · intro i x
    change F (c.product i ((F.image (c.spheres i)).symm x,⟨1/2,by norm_num⟩)) = x
    rw [c.center]
    exact congrArg Subtype.val ((F.image (c.spheres i)).apply_symm_apply x)
  · rw [←hcarrier,←F.image_frontier,MarkedSphereCut.carrier,c.frontierCut,
      image_union,image_iUnion,hFfront]

theorem MarkedSphereCut.image_carrier
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (c : MarkedSphereCut e R κ) (F : X ≃ₜ X) (hFR : F '' R = R)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) : (c.image F hFR hF).carrier = F '' c.carrier := by
  change R \ ⋃ i, F '' c.collar i = F '' (R \ ⋃ i,c.collar i)
  rw [image_sdiff F.injective,image_iUnion,hFR]

theorem MarkedSphereCut.image_no_punctured_sphere_components
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X}
    (c : MarkedSphereCut e R κ)
    (hno : HasNoPuncturedSphereComponents e f c.carrier)
    (F : X ≃ₜ X) (hFR : F '' R = R)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    HasNoPuncturedSphereComponents e f (c.image F hFR hF).carrier := by
  rw [c.image_carrier]
  apply hno.image_of_original_atlas_move F c.plCut.cover hf hF L g hg hgi
  intro x hx
  apply hreal
  rcases hx with hx | hx
  · exact hx.1
  · exact hFR.subset (image_mono (show c.carrier ⊆ R from inter_subset_left) hx)

end PoincareConjecture.M76
