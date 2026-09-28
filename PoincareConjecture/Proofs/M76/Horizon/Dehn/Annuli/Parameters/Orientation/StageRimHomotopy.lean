import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.HomotopySigns
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.WholeCircleAdjustments










set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1


noncomputable def annulusRimCylinder : C(I × Circle, Ann) where
  toFun z := ⟨annulusMap 8 (by norm_num) (z.2, 2 * (z.1 : ℝ) - 1),
    _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) z.2
      ⟨2 * (z.1 : ℝ) - 1, by constructor <;> linarith [z.1.property.1, z.1.property.2]⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)).comp
      (continuous_snd.prodMk (Continuous.subtype_mk (by fun_prop)
        (fun z ↦ by constructor <;> linarith [z.1.property.1, z.1.property.2])))

@[simp] theorem annulusRimCylinder_zero (z : Circle) :
    annulusRimCylinder (0, z) = annulusRimPoint false z := by
  apply Subtype.ext
  change annulusMap 8 (by norm_num) (z, 2 * (0 : ℝ) - 1) =
    annulusMap 8 (by norm_num) (z, -1)
  norm_num

@[simp] theorem annulusRimCylinder_one (z : Circle) :
    annulusRimCylinder (1, z) = annulusRimPoint true z := by
  apply Subtype.ext
  change annulusMap 8 (by norm_num) (z, 2 * (1 : ℝ) - 1) =
    annulusMap 8 (by norm_num) (z, 1)
  norm_num


noncomputable def annulus_radial_rim_homotopy
    {X : Type*} [TopologicalSpace X] (c : C(Ann, X)) (radial : C(X, Circle))
    (q : Bool → C(Circle, Circle))
    (hrims : ∀ b z, radial (c (annulusRimPoint b z)) = q b z) :
    (q false).Homotopy (q true) where
  toFun z := radial (c (annulusRimCylinder z))
  continuous_toFun := radial.continuous.comp (c.continuous.comp annulusRimCylinder.continuous)
  map_zero_left z := by rw [annulusRimCylinder_zero, hrims]
  map_one_left z := by rw [annulusRimCylinder_one, hrims]


noncomputable def inverse_rim_homotopy
    (q : Bool → Circle ≃ₜ Circle)
    (H : (⟨(q false).symm, (q false).symm.continuous⟩ : C(Circle, Circle)).Homotopy
      ⟨(q true).symm, (q true).symm.continuous⟩) :
    (⟨q false, (q false).continuous⟩ : C(Circle, Circle)).Homotopy
      ⟨q true, (q true).continuous⟩ where
  toFun z := q true (H.symm (z.1, q false z.2))
  continuous_toFun := (q true).continuous.comp
    (H.symm.continuous.comp (continuous_fst.prodMk ((q false).continuous.comp continuous_snd)))
  map_zero_left z := by simp only [H.symm.apply_zero, ContinuousMap.coe_mk,
    Homeomorph.apply_symm_apply]
  map_one_left z := by simp only [H.symm.apply_one, ContinuousMap.coe_mk,
    Homeomorph.symm_apply_apply]

end PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
  {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (st : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)



noncomputable def stage_annulus_rim_reparametrization_homotopy
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    {T : Set st.Carrier} (c : source ≃ₜ T) (q : Bool → Q2 ≃ₜ Q2)
    (hrims : ∀ (b : Bool) (u : Q2),
      (c ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩ :
        st.Carrier) = st.annulusRim hS b (q b u)) :
    (⟨q false, (q false).continuous⟩ : C(Q2, Q2)).Homotopy
      ⟨q true, (q true).continuous⟩ where
  toFun z := chartShellRadial L retained (st.projection (c (cylinder z)))
  continuous_toFun := (chartShellRadial L retained).continuous.comp
    (st.projection.continuous.comp (continuous_subtype_val.comp
      (c.continuous.comp cylinder.continuous)))
  map_zero_left u := by
    rw [cylinder_zero, hrims false]
    exact stage_radial_rim L retained st hS hvalues false (q false u)
  map_one_left u := by
    rw [cylinder_one, hrims true]
    exact stage_radial_rim L retained st hS hvalues true (q true u)



noncomputable def stage_annulus_period_reparametrization_homotopy
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    {T : Set st.Carrier} (c : source ≃ₜ T) (q : Bool → Q2 ≃ₜ Q2)
    (hrims : ∀ (b : Bool) (u : Q2),
      (c ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩ :
        st.Carrier) = st.annulusRim hS b (q b u))
    {p : ℝ} (j : AddCircle p ≃ₜ Q2) :
    (⟨j.symm ∘ q false ∘ j, j.symm.continuous.comp ((q false).continuous.comp j.continuous)⟩ :
      C(AddCircle p, AddCircle p)).Homotopy
      ⟨j.symm ∘ q true ∘ j, j.symm.continuous.comp ((q true).continuous.comp j.continuous)⟩ where
  toFun z := j.symm
    (stage_annulus_rim_reparametrization_homotopy L retained st hS hvalues c q hrims
      (z.1, j z.2))
  continuous_toFun := j.symm.continuous.comp
    ((stage_annulus_rim_reparametrization_homotopy L retained st hS hvalues c q hrims).continuous.comp
      (continuous_fst.prodMk (j.continuous.comp continuous_snd)))
  map_zero_left u := congrArg j.symm
    ((stage_annulus_rim_reparametrization_homotopy L retained st hS hvalues c q hrims).apply_zero
      (j u))
  map_one_left u := congrArg j.symm
    ((stage_annulus_rim_reparametrization_homotopy L retained st hS hvalues c q hrims).apply_one
      (j u))

local notation "Circle" => AddCircle (4 * (8 : ℝ))



noncomputable def stage_square_annulus_rim_homotopy
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    {T : Set st.Carrier} (c : squareAnnulus 8 1 ≃ₜ T)
    (j : Circle ≃ₜ Q2) (q : Bool → Circle ≃ₜ Circle)
    (hrims : ∀ b z, (c (annulusRimPoint b z) : st.Carrier) =
      st.annulusRim hS b (j (q b z))) :
    (⟨q false, (q false).continuous⟩ : C(Circle, Circle)).Homotopy
      ⟨q true, (q true).continuous⟩ := by
  refine annulus_radial_rim_homotopy
    ⟨fun x ↦ (c x : st.Carrier), continuous_subtype_val.comp c.continuous⟩
    ⟨fun x ↦ j.symm (chartShellRadial L retained (st.projection x)),
      j.symm.continuous.comp ((chartShellRadial L retained).continuous.comp
        st.projection.continuous)⟩ (fun b ↦ ⟨q b, (q b).continuous⟩) ?_
  intro b z
  change j.symm (chartShellRadial L retained (st.projection
    (c (annulusRimPoint b z)))) = q b z
  rw [hrims, stage_radial_rim L retained st hS hvalues]
  exact j.symm_apply_apply _



noncomputable def stage_square_annulus_correction_homotopy
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    {T : Set st.Carrier} (c : squareAnnulus 8 1 ≃ₜ T)
    (j : Circle ≃ₜ Q2) (q : Bool → Circle ≃ₜ Circle)
    (hrims : ∀ b z, (c (annulusRimPoint b (q b z)) : st.Carrier) =
      st.annulusRim hS b (j z)) :
    (⟨q false, (q false).continuous⟩ : C(Circle, Circle)).Homotopy
      ⟨q true, (q true).continuous⟩ := by
  apply inverse_rim_homotopy q
  apply stage_square_annulus_rim_homotopy L retained st hS hvalues c j
    (fun b ↦ (q b).symm)
  intro b z
  simpa only [Homeomorph.apply_symm_apply] using hrims b ((q b).symm z)

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
