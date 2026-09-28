import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.RawCutComponentHomotopy
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomologyTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismTrimComponentTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomeomorphTransport








set_option autoImplicit false
open Set CategoryTheory Limits
namespace PoincareConjecture.M76
universe u v

theorem original_cut_component_homology_retract_of_raw_coordinates
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    {κ : Type v} [Finite κ] {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    {K : Set E} {R Q : Set X} (g : E → X) (hg : ContinuousOn g K)
    (hgR : MapsTo g K R) (F : X → E) (hF : Continuous F) (hFK : MapsTo F R K)
    (hFg : ∀ y ∈ K, F (g y) = y) (hgF : ∀ y ∈ R, g (F y) = y)
    (O S : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i,O i) (hcQ : IsClosed Q)
    (hCR : ∀ i,closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀ i z,(W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀ i z,(W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC : ∀ i,S i ⊆ closure (O i))
    (p : E) (x : X) (hx : x ∈ Q)
    (hxp : F x ∈ connectedComponentIn (K \ g ⁻¹' ⋃ i,S i) p)
    (M : ModuleCat.{u} (ZMod 2)) [Nontrivial M]
    (i₀ : M ⟶ (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn (K \ g ⁻¹' ⋃ i,S i) p))).homology M 1)
    (r₀ : (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn (K \ g ⁻¹' ⋃ i,S i) p))).homology M 1 ⟶ M)
    (hi₀ : i₀ ≫ r₀ = 𝟙 M) :
    ∃ (i : M ⟶ (TopCat.toSSet.obj (TopCat.of (connectedComponentIn Q x))).homology M 1)
      (r : (TopCat.toSSet.obj (TopCat.of (connectedComponentIn Q x))).homology M 1 ⟶ M),
      i ≫ r = 𝟙 M ∧ ¬ IsZero ((TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn Q x))).homology M 1) := by
  have hmaps : MapsTo g (K \ g ⁻¹' ⋃ i,S i) (R \ ⋃ i,S i) :=
    fun y hy => ⟨hgR hy.1,hy.2⟩
  have hFmaps : MapsTo F (R \ ⋃ i,S i) (K \ g ⁻¹' ⋃ i,S i) := by
    intro y hy
    exact ⟨hFK hy.1,by simpa only [mem_preimage,hgF y hy.1] using hy.2⟩
  let T : (K \ g ⁻¹' ⋃ i,S i : Set E) ≃ₜ (R \ ⋃ i,S i : Set X) :=
    { toFun := fun y => ⟨g y,hmaps y.property⟩
      invFun := fun y => ⟨F y,hFmaps y.property⟩
      left_inv := fun y => Subtype.ext (hFg y y.property.1)
      right_inv := fun y => Subtype.ext (hgF y y.property.1)
      continuous_toFun := (hg.mono sdiff_subset).domRestrict.subtype_mk _
      continuous_invFun := (hF.comp continuous_subtype_val).subtype_mk _ }
  have hp := connectedComponentIn_nonempty_iff.mp ⟨F x,hxp⟩
  let p' : (K \ g ⁻¹' ⋃ i,S i : Set E) := ⟨p,hp⟩
  obtain ⟨i₁,r₁,hi₁⟩ := module_homology_retract_of_component_homeomorph T p' i₀ r₀ hi₀
  obtain ⟨q,_,hcomp,e,_⟩ := exists_raw_cut_component_homotopyEquiv R Q O S W hQ hcQ
    hCR hdis hO hS hSC (T p')
  obtain ⟨i₂,r₂,hi₂⟩ := CutGraph.module_homology_retract_of_homotopyEquiv M e 1 i₁ r₁ hi₁
  have hxraw : x ∈ connectedComponentIn (R \ ⋃ i,S i) (T p' : X) := by
    have hm := (hg.mono sdiff_subset).mapsTo_connectedComponentIn hp hxp
    have hc := connectedComponentIn_mono (g p) (mapsTo_iff_image_subset.mp hmaps) hm
    change x ∈ connectedComponentIn (R \ ⋃ i,S i) (g p)
    simpa only [hgF x (hQ.subset hx).1] using hc
  have heq : connectedComponentIn Q q = connectedComponentIn Q x :=
    connectedComponentIn_eq (hcomp.symm.subset ⟨hxraw,hx⟩)
  have hresult : ∃ (i : M ⟶ (TopCat.toSSet.obj (TopCat.of (connectedComponentIn Q x))).homology M 1)
      (r : (TopCat.toSSet.obj (TopCat.of (connectedComponentIn Q x))).homology M 1 ⟶ M),
      i ≫ r = 𝟙 M := by
    rw [← heq]
    exact ⟨i₂,r₂,hi₂⟩
  obtain ⟨i,r,hir⟩ := hresult
  refine ⟨i,r,hir,?_⟩
  intro hzero
  have hi : i = 0 := hzero.eq_of_tgt i 0
  have hid : 𝟙 M = 0 := hir.symm.trans (by rw [hi,zero_comp])
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp ((IsZero.iff_id_eq_zero M).mpr hid)
  exact false_of_nontrivial_of_subsingleton M

end PoincareConjecture.M76
